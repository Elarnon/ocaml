open Lambda

(** TRMC (tail-recursion-modulo-cons) is a code transformation that
    rewrites transformed functions in destination-passing-style, in
    such a way that certain calls that were not in tail position in the
    original program become tail-calls in the transformed program.

    As a classic example, the following program
    {|
     let rec map f = function
     | [] -> []
     | x :: xs ->
       let y = f x in
       y :: map f xs
    |}
    becomes (expressed in almost-source-form; the translation is in
    fact at the Lambda-level)
    {|
     let rec map f = function
     | [] -> []
     | x :: xs _>
       let y = f x in
       let dst = y :: Placeholder in
       map_trmc dst 1 f xs; dst
     and map_trmc dst offset f = function
     | [] ->
       dst.1 <- []
     | x :: xs ->
       let y = f x in
       let dst' = y :: Placeholder in
       dst.offset <- dst';
       map_trmc dst offset f fx
    |}

    In this example, the expression (y :: map f xs) had a call in
    non-tail-position, and it gets rewritten into tail-calls.  TRMC
    handles all such cases where the continuation of the call
    (what needs to be done after the return) is a "construction", the
    creation of a (possibly nested) data block.

    The code transformation generates two versions of the
    input function, the "direct" version with the same type and
    behavior as the original one (here just [map]), and
    the "destination-passing-style" version (here just [map_trmc]).

    Any call to the original function from outside the let..rec
    declaration gets transformed into a call into the direct version,
    which will itself call the destination-passing-style versions on
    recursive calls that may benefit from it (they are in tail-position
    modulo constructors).

    Because of this inherent code duplication, the transformation may
    not always improve performance. In this implementation, TRMC is
    opt-in, we only transform functions that the user has annotated
    with an attribute to request the transformation.

    Note: in this implementation, the scope of the TRMC transformation
    is a single set of mutually-recursive-declarations; TRMC applies
    to declarations of the form
      [let[@trmc] rec f1 = t1 and .. and fn = tn in u]
    and only the callsites of [f1..fn] within [t1..tn] will get
    considered for destination-passing-style transformations; callsites in [u]
    are not analyzed, and will always call the direct version (which may
    in turn call the destination-passing-style versions).
    In particular, there is no propagation of information across modules.
*)

type 'offset destination = { var: Ident.t; offset: 'offset; }
and offset = lambda
(** In the OCaml value model, interior pointers are not allowed.  To
    represent the "placeholder to mutate" in DPS code, we thus use a pair
    of the block containing the placeholder, and the offset of the
    placeholder within the block.

    In the common case, this offset is an arbitrary lambda expression, typically
    a constant integer or a variable. We define ['a destination] as parametrized
    over the offset type to represent formal destination parameters (where
    the offset is an Ident.t), and maybe in the future statically-known
    offsets (where the offset is an integer).
*)

let add_dst_params ({var; offset} : Ident.t destination) params =
  (var, Pgenval) :: (offset, Pintval) :: params

let add_dst_args ({var; offset} : offset destination) args =
  Lvar var :: offset :: args

let assign_to_dst loc {var; offset} lam =
  Lprim(Psetfield_computed(Pointer, Heap_initialization),
        [Lvar var; offset; lam], loc)

(** The type ['a Dps.t] (destination-passing-style) represents a
    version of ['a] that is parametrized over a [lambda destination].
    A [lambda Dps.t] is a code fragment in destination-passing-style,
    a [(lambda * lambda) Dps.t] represents two subterms parametrized
    over the same destination. *)
module Dps = struct
  type 'a dynamic =
    tail:bool -> dst:lambda destination -> 'a
  (** A term parametrized over a destination. The [tail] argument is
      passed by the caller to indicate whether the term will be placed
      in tail-position -- this allows to generate correct @tailcall
      annotations. *)

  type 'a linear_static =
    tail:bool -> dst:lambda destination -> delayed:(lambda -> lambda) -> 'a
  (** Short verion:

      To optimize nested constructors, we keep track in the choice
      structure of which DPS terms are in the "linear static"
      fragment, where the destination is set in a single static
      location of the program (and not by calling another
      TRMC function).

      When we would generate code to update a destination by setting
      it to a "partial value" containing a new destination, we can
      look at whether the consumer of this new destination is in the
      linear static DPS fragment. In this case we optimize away the
      creation of the new location (and update to the
      current destination) by "delaying" the partial value application
      to the unique place inside the DPS term that sets its
      destination.

      The [delayed] argument of a static DPS term represents those
      delayed partial contexts, to be applied when setting the
      location.

      Longer version with examples:

      We want to optimize nested constructors, for example

      {[
        (x () :: y () :: trmc call)
      ]}

      which would naively generate (in a DPS context parametrized
      over a location dst.i):

      {[
        let dstx = x () :: Placeholder in
        dst.i <- dstx;
        let dsty = y () :: Placeholder in
        dstx.1 <- dsty;
        trmc dsty.1 call
      ]}

      when we would rather hope for

      {[
        let vx = x () in
        let dsty = y () :: Placeholder in
        dst.i <- vx :: dsty;
        trmc dsty.1 call
      ]}

      We could detect this special case (nested constructors)
      and generate the expected code. But can we instead see this as
      a specific instance of a more general/powerful optimization?

      The idea is that the unoptimized version is of the form
      of a destination-creation site for dstx.1

      {[
        let dstx = x () :: Placeholder in
        dst.i <- dstx;
      ]}

      followed by a piece of code where the value set to [dstx.1] is
      statically known: there is a single place that writes to it, in the
      current function body. This destination is used in a linear static
      way, in opposition to:

      - non-linear usage: cases where the control-flow splits and
        multiple places write different things to dstx.1

      - dynamic usage: when the destination is passed to a function call
        rather than set explicitly in the body.

      When a choice uses its destination in a linear static way, we
      could optimize away the destination creation by it inside the
      linear-static choice, to get simplified away when it meets the
      single destination-set instruction. This transformation suffices
      to get from the "regular" to the "optimized" version of the
      instance above.

      So this is the idea: this simplification of nested constructors
      can be justified for the whole class of expressions that are doing
      a "linear static" usage of their continuations.

      We do this on the fly in our implementation. We avoid creating
      this new destination [dstx.1], and instead pass to the following
      code the destination [dst.i] with a "delayed" transformation
      [(x () ::)], to be applied at the place where [dstx.1] would
      have been set:

      {[
        dstx.1 <- dsty;
      ]}
      becomes
      {[
        dst.i <- x () :: dsty;
      ]}

      More precisely, we need to bind the possibly-effectful [x ()]
      to a variable [vx], so that it does not get reordered with
      respect to other computations in the term ([y ()] in our example above).

      Finally, we give some counter-examples where usage is non-linear.

      Source program:
      {[
        x :: (if foo then y1 :: trmc call1 else y2 :: trmc call2)
      ]}

      Naive code:
      {[
        let dstx = x :: Placeholder in
        dst.i <- dstx;
        if foo then begin
          let dsty1 = y1 :: Placeholder in
          dstx.1 <- dsty1;
          trmc dsty1.1 call1
        end else
          let dsty2 = y2 :: Placeholder in
          dstx.1 <- dsty2;
          trmc dsty2.1 call1
        end
      ]}

      One could propose to optimize this into:
      {[
        let vx = x in
        if foo then begin
          let dsty1 = y1 :: Placeholder in
          dstx.1 <- vx :: sty1;
          trmc dsty1.1 call1
        end else
          let dsty2 = y2 :: Placeholder in
          dstx.1 <- vx :: dsty2;
          trmc dsty2.1 call1
        end
      ]}
      but note that this duplicates the (vx ::) construction in the two
      branches, while we want to avoid any code duplication in the code
      generated for a single specialization of the TRMC
      function. (In general this duplicated part corresponds to the
      nested constructors so it may be quite large, when constructing
      interesting AST fragments for example.)

      On the other hand, the following examples are outside the "nested
      constructor" fragment and yet remains static and linear, so we can
      optimize them:
      {[
        x :: (foo; y :: trmc call)
        x :: (let v = e in y :: trmc call)
      ]}
  *)

  type 'a t =
    | Dynamic of 'a dynamic
    | Linear_static of 'a linear_static

  let coerce (dps : 'a linear_static) : 'a dynamic =
    fun ~tail ~dst ->
      dps ~tail ~dst ~delayed:(fun t -> t)

  let run : 'a t -> 'a dynamic = function
    | Dynamic dps -> dps
    | Linear_static dps -> coerce dps

  let map f = function
    | Dynamic dps ->
        Dynamic (fun ~tail ~dst -> f (dps ~tail ~dst))
    | Linear_static dps ->
        Linear_static (fun ~tail ~dst ~delayed -> f (dps ~tail ~dst ~delayed))

  (* Pairing two DPS terms gives a result that
     uses its destination at least twice, so it is
     never linear, always Dynamic *)
  let pair (fa : 'a t) (fb : 'b t) : ('a * 'b) t =
    let dyna, dynb = run fa, run fb in
    Dynamic (fun ~tail ~dst -> (dyna ~tail ~dst, dynb ~tail ~dst))
end

(** The TRMC transformation requires information flows in two opposite
    directions: the information of which callsites can be rewritten in
    destination-passing-style flows from the leaves of the code to the
    root, and the information on whether we remain in tail-position
    flows from the root to the leaves -- and also the knowledge of
    which version of the function we currently want to generate, the
    direct version or a destination-passing-style version.

    To clarify this double flow of information, we split the TRMC
    compilation in two steps:

    1. A function [trmc t] that takes a term and processes it from
    leaves to root; it produces a "code choice", a piece of data of
    type [lambda Choice.t], that contains information on how to transform the
    input term [t] *parameterized* over the (still missing) contextual
    information.

    2. Code-production operators that have contextual information
    to transform a "code choice" into the final code.

    The code-production choices for a single term have type [lambda Choice.t];
    using a parametrized type ['a Choice.t] is useful to represent simultaneous
    choices over several subterms; for example [(lambda * lambda) Choice.t]
    makes a choice for a pair of terms, for example the [then] and [else]
    cases of a conditional (their choice is synchronized, they are either
    both in destination-passing-style or none of them is). With this parameter,
    ['a Choice.t] has an applicative structure, which is useful to write
    the actual code transformation in the {!choice} function.
*)
module Choice = struct
  type 'a t =
    | Return of 'a
    (** [Return t] means that there are no TRMC opportunities in the subterm [t]:
        no matter which context we are in,
        we should evaluate [t] and "return" it. *)
    | Set of 'a settable
    (** [Set t] represents a piece of code that does contain
        TRMC opportunities: if the context allows, we can write parts of
        it in destination-passing-style to turn non-tail calls into tail
        calls. See the type [settable] below. *)

  and 'a settable = {
    dps: 'a Dps.t;
    direct: unit -> 'a;
    benefits_from_dps: bool;
  }
  (**
     A [settable] record represents code that may be written in destination-passing style
     if its usage context allows it. More precisely:

     - If the surrounding context is already in destination-passing
       style, it has a destination available, we should produce the
       code in [dps] -- a function parametrized over the destination.
       It passes the ~tail boolean to indicate whether the produced code
       is used in tail position.

     - If the surrounding context is in direct style (no destination
       is available), we should produce the fallback code from
       [direct].

      (Note: [direct] is also a function (on [unit]) to ensure that any
      effects performed during code production will only happen once we
      do know that we want to produce the direct-style code.)

     The [benefits_from_dps] boolean indicates whether
     the use of destination-passing-style is beneficial to this function,
     in the sense that the [dps] version has strictly more recursive calls
     to TRMC versions than the [direct] version. When [benefits_from_dps]
     is false, there is no difference in number of TRMC sub-calls --
     see the {!choice_makeblock} case.
  *)

  (** Finds the first [settable] element in a list [choices];
      - if it exists, it gives a record
        [{rev_returns; settable; tail_choices}] such that
        [choices =
          List.rev_append
            (List.map Return rev_returns)
            (Settable settable :: tail_choices)]
      - if there is no settable element, it gives a list [returns]
        such that [choices = List.map Return returns]
  *)
  type 'a settable_zipper = {
    rev_returns : 'a list;
    settable : 'a settable;
    tail_choices: 'a t list
  }

  let find_settable : 'a t list -> ('a settable_zipper, 'a list) result =
    let rec find rev_returns = function
      | [] -> Error (List.rev rev_returns)
      | Return r :: rest -> find (r :: rev_returns) rest
      | Set settable :: tail_choices -> Ok { rev_returns; settable; tail_choices }
    in find []

  let map_settable f s = {
    benefits_from_dps = s.benefits_from_dps;
    direct = (fun () -> f (s.direct ()));
    dps = Dps.map f s.dps;
  }

  let map f = function
    | Return t -> Return (f t)
    | Set s -> Set (map_settable f s)

  let pair ((c1, c2) : 'a t * 'b t) : ('a * 'b) t =
    match c1, c2 with
    | Return v1, Return v2 -> Return (v1, v2)
    | Set s1, Return v2 ->
        Set (map_settable (fun v1 -> (v1, v2)) s1)
    | Return v1, Set s2 ->
        Set (map_settable (fun v2 -> (v1, v2)) s2)
    | Set s1, Set s2 ->
        Set {
          benefits_from_dps = s1.benefits_from_dps || s2.benefits_from_dps;
          direct = (fun () -> s1.direct (), s2.direct ());
          dps = Dps.pair s1.dps s2.dps;
        }

  let (let+) c f = map f c
  let (and+) c1 c2 = pair (c1, c2)

  let option (c : 'a t option) : 'a option t =
    match c with
    | None -> Return None
    | Some c -> let+ v = c in Some v

  let rec list (c : 'a t list) : 'a list t =
    match c with
    | [] -> Return []
    | c::cs ->
        let+ v = c
        and+ vs = list cs in
        v :: vs

  let direct : lambda t -> lambda = function
    | Return t -> t
    | Set settable -> settable.direct ()

  let dps loc : lambda t -> lambda Dps.dynamic = function
    | Return t ->
        (fun ~tail:_ ~dst -> assign_to_dst loc dst t)
    | Set settable ->
        Dps.run settable.dps
end

let (let+), (and+) = Choice.((let+), (and+))

type context = {
  candidates: candidate Ident.Map.t;
}
and candidate = {
  arity: int;
  dps_id: Ident.t;
}

let trmc_placeholder = Lconst (Const_base (Const_int 0))
(* TODO consider using a more magical constant like 42, for debugging? *)

let find_candidate = function
  | Lfunction lfun when lfun.attr.trmc_candidate -> Some lfun
  | _ -> None

let declare_binding ctx (var, def) =
  match find_candidate def with
  | None -> ctx
  | Some lfun ->
  let arity = List.length lfun.params in
  let dps_id = Ident.create_local (Ident.name var ^ "_trmc") in
  let cand = { arity; dps_id } in
  { candidates = Ident.Map.add var cand ctx.candidates }

let rec choice ctx t =
  let rec choice ctx t =
    begin[@warning "-8"]
      (*FIXME: allows non-exhaustive pattern matching;
        use an overkill functor-based solution instead? *)
      match t with
      | (Lvar _ | Lconst _ | Lfunction _ | Lsend _
        | Lassign _ | Lfor _ | Lwhile _) ->
          let t = traverse ctx t in
          Choice.Return t

      (* [choice_prim] handles most primitives, but the important case of construction
         [Lprim(Pmakeblock(...), ...)] is handled by [choice_makeblock] *)
      | Lprim (prim, primargs, loc) ->
          choice_prim ctx prim primargs loc

      (* [choice_apply] handles applications, in particular tail-calls which
         generate Set choices at the leaves *)
      | Lapply apply ->
          choice_apply ctx apply
      (* other cases use the [lift] helper that takes the sub-terms in tail
         position and the context around them, and generates a choice for
         the whole term from choices for the tail subterms. *)
      | Lsequence (l1, l2) ->
          let l1 = traverse ctx l1 in
          let+ l2 = choice ctx l2 in
          Lsequence (l1, l2)
      | Lifthenelse (l1, l2, l3) ->
          let l1 = traverse ctx l1 in
          let+ (l2, l3) = choice_pair ctx (l2, l3) in
          Lifthenelse (l1, l2, l3)
      | Llet (lk, vk, var, def, body) ->
          (* non-recursive bindings are not specialized *)
          let def = traverse ctx def in
          let+ body = choice ctx body in
          Llet (lk, vk, var, def, body)
      | Lletrec (bindings, body) ->
          let ctx, bindings = traverse_letrec ctx bindings in
          let+ body = choice ctx body in
          Lletrec(bindings, body)
      | Lswitch (l1, sw, loc) ->
          (* decompose *)
          let consts_lhs, consts_rhs = List.split sw.sw_consts in
          let blocks_lhs, blocks_rhs = List.split sw.sw_blocks in
          (* transform *)
          let l1 = traverse ctx l1 in
          let+ consts_rhs = choice_list ctx consts_rhs
          and+ blocks_rhs = choice_list ctx blocks_rhs
          and+ sw_failaction = choice_option ctx sw.sw_failaction in
          (* rebuild *)
          let sw_consts = List.combine consts_lhs consts_rhs in
          let sw_blocks = List.combine blocks_lhs blocks_rhs in
          let sw = { sw with sw_consts; sw_blocks; sw_failaction; } in
          Lswitch (l1, sw, loc)
      | Lstringswitch (l1, cases, fail, loc) ->
          (* decompose *)
          let cases_lhs, cases_rhs = List.split cases in
          (* transform *)
          let l1 = traverse ctx l1 in
          let+ cases_rhs = choice_list ctx cases_rhs
          and+ fail = choice_option ctx fail in
          (* rebuild *)
          let cases = List.combine cases_lhs cases_rhs in
          Lstringswitch (l1, cases, fail, loc)
      | Lstaticraise (id, ls) ->
          let ls = traverse_list ctx ls in
          Choice.Return (Lstaticraise (id, ls))
      | Ltrywith (l1, id, l2) ->
          (* in [try l1 with id -> l2], the term [l1] is
             not in tail-call position (after it returns
             we need to remove the exception handler),
             so it is not transformed here *)
          let l1 = traverse ctx l1 in
          let+ l2 = choice ctx l2 in
          Ltrywith (l1, id, l2)
      | Lstaticcatch (l1, ids, l2) ->
          (* In [static-catch l1 with ids -> l2],
             the term [l1] is in fact in tail-position *)
          let+ l1 = choice ctx l1
          and+ l2 = choice ctx l2 in
          Lstaticcatch (l1, ids, l2)
      | Levent (lam, lev) ->
          let+ lam = choice ctx lam in
          Levent (lam, lev)
      | Lifused (x, lam) ->
          let+ lam = choice ctx lam in
          Lifused (x, lam)
    end

  and choice_apply ctx apply =
    let exception No_trmc in
    try
      match apply.ap_func with
      | Lvar f ->
          (* TODO: if [@tailcall false] then raise No_trmc; *)
          let candidate =
            try Ident.Map.find f ctx.candidates
            with Not_found ->
              (* TODO warn: tail-callness of the call is broken in
                 the destination-passing-style version; either the function [f]
                 should be marked as trmc-specializable at the callsite,
                 or the user should add [@tailcall false] to clarify
                 that they are aware of this limitation. *)
              raise No_trmc
          in
          Choice.Set {
            benefits_from_dps = true;
            dps = Dynamic (fun ~tail ~dst ->
              let f_dps = candidate.dps_id in
              Lapply { apply with
                       ap_func = Lvar f_dps;
                       ap_args = add_dst_args dst apply.ap_args;
                       ap_tailcall =
		         if tail then Should_be_tailcall else Default_tailcall;
                     });
            direct = (fun () -> Lapply apply);
          }
      | _nontail -> raise No_trmc
    with No_trmc -> Choice.Return (Lapply apply)

  and choice_makeblock ctx (tag, flag, shape) blockargs loc =
    let k new_flag new_block_args =
      Lprim (Pmakeblock (tag, new_flag, shape), new_block_args, loc) in
    let choices = List.map (choice ctx) blockargs in
    match Choice.find_settable choices with
    | Error all_returns ->
        let all_returns = traverse_list ctx all_returns in
        Choice.Return (k flag all_returns)
    | Ok { rev_returns; settable; tail_choices } ->
        begin
          (* fail if this settable position is not unique *)
          match Choice.find_settable tail_choices with
          | Error _all_returns -> ()
          | Ok _another_settable ->
              failwith "TODO proper error/warning: ambiguous settable position"
        end;
        let before = traverse_list ctx (List.rev rev_returns) in
        let after = traverse_list ctx (List.map Choice.direct tail_choices) in
        let plug_args before t after =
          List.append before @@ t :: after in
        let k_with_placeholder =
          k Mutable (plug_args before trmc_placeholder after)
        in
        let placeholder_pos = List.length before in
        let placeholder_pos_lam = Lconst (Const_base (Const_int placeholder_pos)) in
        let let_block_in body =
          let block_var = Ident.create_local "block" in
          Llet(Strict, Pgenval, block_var, k_with_placeholder,
               body block_var)
        in
        let block_dst block_var = { var = block_var; offset = placeholder_pos_lam } in
        Choice.Set {
          benefits_from_dps =
            (* Whether or not the caller provides a destination,
               we can always provide a destination to our settable
               subterm, so the number of TRMC sub-calls is identical
               in the [direct] and [dps] versions. *)
            false;
          direct = (fun () ->
            if not settable.benefits_from_dps then
              k flag (plug_args before (settable.direct ()) after)
            else
              let_block_in @@ fun block_var ->
              Lsequence(Dps.run settable.dps ~tail:false ~dst:(block_dst block_var),
                        Lvar block_var)
          );
          dps = Linear_static (fun ~tail ~dst ~delayed ->
            match settable.dps with
            | Dynamic dps ->
                let_block_in @@ fun block_var ->
                Lsequence(assign_to_dst loc dst (delayed (Lvar block_var)),
                          dps ~tail ~dst:(block_dst block_var))
            | Linear_static dps ->
                let bind_list start lambdas k =
                  (* TODO optimization: no binding for variables and constants *)
                  let bindings =
                    lambdas |> List.mapi (fun i lam ->
                      (Ident.create_local ("arg" ^ string_of_int (start+i))),
                      lam)
                  in
                  let body = k (List.map fst bindings) in
                  List.fold_right (fun (v,lam) body ->
                    Llet(Strict, Pgenval, v, lam, body)
                  ) bindings body
                in
                let vars = List.map (fun v -> Lvar v) in
                bind_list 1 before @@ fun vbefore ->
                bind_list (List.length before) after @@ fun vafter ->
                dps ~tail ~dst ~delayed:(fun t ->
                  delayed (k flag (plug_args (vars vbefore) t (vars vafter))))
          );
        }

  and choice_prim ctx prim primargs loc =
    begin [@warning "-8"] (* see choice *)
      match prim with
      (* The important case is the construction case *)
      | Pmakeblock (tag, flag, shape) ->
          choice_makeblock ctx (tag, flag, shape) primargs loc

      (* Some primitives have arguments in tail-position *)
      | (Pidentity | Popaque) as idop ->
          let l1 = match primargs with
            |  [l1] -> l1
            | _ -> invalid_arg "choice_prim" in
          let+ l1 = choice ctx l1 in
          Lprim (idop, [l1], loc)
      | (Psequand | Psequor) as shortcutop ->
          let l1, l2 = match primargs with
            |  [l1; l2] -> l1, l2
            | _ -> invalid_arg "choice_prim" in
          let l1 = traverse ctx l1 in
          let+ l2 = choice ctx l2 in
          Lprim (shortcutop, [l1; l2], loc)

      (* in common cases we just Return *)
      | Pbytes_to_string | Pbytes_of_string
      | Pgetglobal _ | Psetglobal _
      | Pfield _ | Pfield_computed
      | Psetfield _ | Psetfield_computed _
      | Pfloatfield _ | Psetfloatfield _
      | Pccall _
      | Praise _
      | Pnot
      | Pnegint | Paddint | Psubint | Pmulint | Pdivint _ | Pmodint _
      | Pandint | Porint | Pxorint
      | Plslint | Plsrint | Pasrint
      | Pintcomp _
      | Poffsetint _ | Poffsetref _
      | Pintoffloat | Pfloatofint
      | Pnegfloat | Pabsfloat
      | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
      | Pfloatcomp _
      | Pstringlength | Pstringrefu  | Pstringrefs
      | Pbyteslength | Pbytesrefu | Pbytessetu | Pbytesrefs | Pbytessets
      | Parraylength _ | Parrayrefu _ | Parraysetu _ | Parrayrefs _ | Parraysets _
      | Pisint | Pisout

      (* we don't handle array indices as destinations yet *)
      | (Pmakearray _ | Pduparray _)

      (* we don't handle { foo with x = ...; y = recursive-call } *)
      | Pduprecord _

      | (
        (* operations returning boxed values could be considered constructions someday *)
        Pbintofint _ | Pintofbint _
        | Pcvtbint _
        | Pnegbint _
        | Paddbint _ | Psubbint _ | Pmulbint _ | Pdivbint _ | Pmodbint _
        | Pandbint _ | Porbint _ | Pxorbint _ | Plslbint _ | Plsrbint _ | Pasrbint _
        | Pbintcomp _
      )
      | Pbigarrayref _ | Pbigarrayset _
      | Pbigarraydim _
      | Pstring_load_16 _ | Pstring_load_32 _ | Pstring_load_64 _
      | Pbytes_load_16 _ | Pbytes_load_32 _ | Pbytes_load_64 _
      | Pbytes_set_16 _ | Pbytes_set_32 _ | Pbytes_set_64 _
      | Pbigstring_load_16 _ | Pbigstring_load_32 _ | Pbigstring_load_64 _
      | Pbigstring_set_16 _ | Pbigstring_set_32 _ | Pbigstring_set_64 _ | Pctconst _
      | Pbswap16
      | Pbbswap _
      | Pint_as_pointer
        ->
          let primargs = traverse_list ctx primargs in
          Choice.Return (Lprim (prim, primargs, loc))
    end

  and choice_list ctx terms =
    Choice.list (List.map (choice ctx) terms)
  and choice_pair ctx (t1, t2) =
    Choice.pair (choice ctx t1, choice ctx t2)
  and choice_option ctx t =
    Choice.option (Option.map (choice ctx) t)

  in choice ctx t

and traverse ctx = function
  | Lletrec (bindings, body) ->
      let ctx, bindings = traverse_letrec ctx bindings in
      Lletrec (bindings, traverse ctx body)
  | lam ->
      shallow_map (traverse ctx) lam

and traverse_letrec ctx bindings =
  let ctx = List.fold_left declare_binding ctx bindings in
  let bindings = List.concat_map (traverse_binding ctx) bindings in
  ctx, bindings

and traverse_binding ctx (var, def) =
  match find_candidate def with
  | None -> [(var, traverse ctx def)]
  | Some lfun ->
  let cand = Ident.Map.find var ctx.candidates in
  let cand_choice = choice ctx lfun.body in
  let direct =
    Lfunction { lfun with body = Choice.direct cand_choice } in
  let dps =
    let dst = {
      var = Ident.create_local "dst";
      offset = Ident.create_local "offset";
    } in
    let dst_lam = { dst with offset = Lvar dst.offset } in
    Lambda.duplicate @@ Lfunction { lfun with (* TODO check function_kind *)
      params = add_dst_params dst lfun.params;
      body = Choice.dps lfun.loc cand_choice ~tail:true ~dst:dst_lam;
    } in
  let dps_var = cand.dps_id in
  [(var, direct); (dps_var, dps)]

and traverse_list ctx terms =
  List.map (traverse ctx) terms

let rewrite t =
  let ctx = { candidates = Ident.Map.empty } in
  traverse ctx t
