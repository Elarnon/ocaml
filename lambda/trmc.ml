open Lambda

type error =
  |  Ambiguous_constructor_arguments of lambda list

exception Error of Location.t * error

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
      [let[@tailrec_mod_constr] rec f1 = t1 and .. and fn = tn in u]
    and only the callsites of [f1..fn] within [t1..tn] will get
    considered for destination-passing-style transformations; callsites in [u]
    are not analyzed, and will always call the direct version (which may
    in turn call the destination-passing-style versions).
    In particular, there is no propagation of information across modules.
*)

type 'offset destination = { var: Ident.t; offset: 'offset; loc : Debuginfo.Scoped_location.t }
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

let assign_to_dst {var; offset; loc} lam =
  Lprim(Psetfield_computed(Pointer, Heap_initialization),
        [Lvar var; offset; lam], loc)

(** The type [Constr.t] represents a reified constructor with a single hole, which can
    be either directly applied to a [lambda] term, or be used to create
    a fresh [lambda destination] with a placeholder.
 *)
module Constr = struct
  type t = {
    tag : int;
    flag: Asttypes.mutable_flag;
    shape : block_shape;
    before: lambda list;
    after: lambda list;
    loc : Debuginfo.Scoped_location.t;
  }

  let apply ?flag con t =
    let flag = match flag with None -> con.flag | Some flag -> flag in
    let block_args = List.append con.before @@ t :: con.after in
    Lprim (Pmakeblock (con.tag, flag, con.shape), block_args, con.loc)

  let trmc_placeholder = Lconst (Const_base (Const_int 0))
  (* TODO consider using a more magical constant like 42, for debugging? *)

  let with_placeholder con (body : lambda destination -> lambda -> lambda) : lambda =
    let k_with_placeholder = apply ~flag:Mutable con trmc_placeholder in
    let placeholder_pos = List.length con.before in
    let placeholder_pos_lam = Lconst (Const_base (Const_int placeholder_pos)) in
    let block_var = Ident.create_local "block" in
    Llet (Strict, Pgenval, block_var, k_with_placeholder,
          body { var = block_var; offset = placeholder_pos_lam ; loc = con.loc } (Lvar block_var))

  (** We want to delay the application of the constructor to a later time.
      This may move the constructor application below some effectful
      expressions (if we move into a context of the form [foo;
      bar_with_trmc_inside] for example), and we want to preserve the
      evaluation order of the other arguments of the constructor.  So we bind
      them before proceeding, unless they are obviously side-effect free. *)
  let delay_impure : t -> (t -> lambda) -> lambda =
    let bind_list name lambdas k =
      let can_be_delayed =
        (* Note that the delayed subterms will be used
           exactly once in the linear-static subterm. So
           we are happy to delay constants, which we would
           not want to duplicate. *)
        function
        | Lvar _ | Lconst _ -> true
        | _ -> false in
      let bindings, args =
        lambdas
        |> List.mapi (fun i lam ->
            if can_be_delayed lam then (None, lam)
            else begin
              let v = Ident.create_local (Printf.sprintf "arg_%s_%d" name i) in
              (Some (v, lam), Lvar v)
            end)
        |> List.split in
      let body = k args in
      List.fold_right (fun binding body ->
          match binding with
          | None -> body
          | Some (v, lam) -> Llet(Strict, Pgenval, v, lam, body)
        ) bindings body in
    fun con body ->
    bind_list "before" con.before @@ fun vbefore ->
    bind_list "after" con.after @@ fun vafter ->
    body { con with before = vbefore; after = vafter }
end

(** The type ['a Dps.t] (destination-passing-style) represents a
    version of ['a] that is parametrized over a [lambda destination].
    A [lambda Dps.t] is a code fragment in destination-passing-style,
    a [(lambda * lambda) Dps.t] represents two subterms parametrized
    over the same destination. *)
module Dps = struct
  type 'a t =
    tail:bool -> dst:lambda destination -> delayed:Constr.t list -> 'a
  (* A term parametrized over a destination. The [tail] argument is
      passed by the caller to indicate whether the term will be placed
      in tail-position -- this allows to generate correct @tailcall
      annotations. *)
  (* Short verion:

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
  (** A term parameterized over a destination.  The [tail] argument
      is passed by the caller to indicate whether the term will be placed
      in tail-position -- this allows to generate correct @tailcall
      annotations.

      Moreover, we want to optimize nested constructors, for example:

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

      The idea is that the unoptimized version first creates a
      destination site [dstx], which is then used by the following
      code.  If we keep track of the current destination:

      {[
        (* Destination is [dst.i] *)
        let dstx = x () :: Placeholder in
        dst.i (* Destination *) <- dstx;
        (* Destination is [dstx.1] *)
        let dsty = y () :: Placeholder in
        dstx.1 (* Destination *) <- dsty;
        (* Destination is [dsty.1] *)
        trmc dsty.1 call
      ]}

      Instead of binding the whole newly-created destination, we can
      simply let-bind the non-placeholder arguments (in order to 
      preserve execution order), and keep track of a list of blocks to
      be created along with the current destination.  Instead of seeing
      a DPS fragment as writing to a destination, we see it as a term
      with shape [dst.i <- C .] where [C .] is a linear context consisting
      only of constructor applications.

      {[
        (* Destination is [dst.i <- C .] *)
        let vx = x () in
        (* Destination is [dst.i <- C (vx :: .)] *)
        let vy = y () in
        (* Destination is [dst.i <- C (vx :: vy :: .)] *)
        (* Making a call: reify the destination *)
        let dsty = vy :: Placeholder in
        dst.i <- vx :: dsty;
        trmc dsty.1 call
      ]}

      The [delayed] argument represents the context [C] as a list of
      reified constructors, to allow both to build the final holey
      block ([vy :: Placeholder]) at the recursive call site, and
      the delayed constructor applications ([vx :: dsty]).

      In practice, it is not desirable to perform this simplification
      when there are multiple TRMC calls (e.g. in different branches
      of an [if] block), because it would cause duplication of the
      nested constructor applications.  The [Choice] module keeps track
      of this information.
*)

  let write_to_dst dst delayed t =
    assign_to_dst dst @@
    List.fold_left (fun t con -> Constr.apply con t) t delayed

  let return (v : lambda) : lambda t =
    fun ~tail:_ ~dst ~delayed ->
      write_to_dst dst delayed v
  (** Create a new destination-passing-style term which is simply
      setting the destination with the given [v], hence "returning"
      it.
   *)

  let empty (v : 'a) : 'a t = fun ~tail:_ ~dst:_ ~delayed:_ -> v
  (** Create an empty container for destination-passing-style lambdas.
    
      This is meant to be used for container types which do not contain
      any lambda values, such as [None] or [[]].
   *)

  let delay_impure (dps : 'a t) : 'a t =
    fun ~tail ~dst ~delayed ->
      List.fold_left (fun k c delayed ->
          Constr.delay_impure c (fun c -> k (c :: delayed)))
        (fun delayed -> dps ~tail ~dst ~delayed)
        delayed
        []

  let reify_delay (dps : tail:bool -> dst:lambda destination -> lambda) : lambda t =
    fun ~tail ~dst ~delayed ->
    match delayed with
    | [] -> dps ~tail ~dst 
    | x :: xs ->
        Constr.with_placeholder x @@ fun block_dst block ->
            Lsequence (
              write_to_dst dst xs block,
              dps ~tail ~dst:block_dst)

  let map (f : 'a -> 'b) (dps : 'a t) : 'b t =
    fun ~tail ~dst ~delayed ->
      f @@ dps ~tail ~dst ~delayed

  let pair (fa : 'a t) (fb : 'b t) : ('a * 'b) t =
    fun ~tail ~dst ~delayed ->
      (fa ~tail ~dst ~delayed, fb ~tail ~dst ~delayed)
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
  type 'a t = {
    dps : 'a Dps.t;
    direct : unit -> 'a;
    uses_dps : bool;
    (* If false, there are no TRMC opportunities in the subterm.
       No matter which context we are in, we should evaluate [direct ()] and "return" it. 

       Otherwise this is a piece of code which does contain TRMC opportunities.
       If the context allows, we can write parts of it in destination-passing-style
       to turn non-tail calls into tail calls. *)
    is_linear : bool;
    benefits_from_dps : bool;
    explicit_tailcall_request: bool;
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

     The [explicit_tailcall_request] boolean is true when the user
     used a [@tailcall] annotation on the optimizable callsite.
     When one of several calls could be optimized, we expect that
     exactly one of them will be annotated by the user, or fail
     because the situation is ambiguous.
  *)
  (* If the surrounding context is already in destination-passing style, 
      it has a destination available, and we should produce the code in [dps] --
      a function parameterized over the destination.  The [tail] boolean indicates
      whether the produced code is used in tail position.

      If the surrounding context is in direct style (no destination is available),
      we should produce the fallback code from [direct].

      (Note: [direct] is also a function (on [unit]) to ensure that any
      effects performed during code production will only happen once we
      do know that we want to produce the direct-style code.)

      The [uses_dps] boolean indicates whether the function contains at
      least one TRMC sub-call in its [dps] version.  If [false], there is no
      reason to use the [dps] version at all.

      The [benefits_from_dps] boolean indicates whether the use of destination-passing-style
      is beneficial to this function, in the sense that the [dps] version has strictly more
      recursive calls to TRMC versions than the [direct] version.  When [benefits_from_dps]
      is [false], there is no difference in the number of TRMC sub-calls -- see the
      {!choice_makeblock} case.

      The [is_linear] boolean indicates whether the function makes a single use
      of its destination.  If [false], calling the [dps] version with delayed constructors
      will cause code duplication.

      The [explicit_tailcall_request] boolean is true when the user
      used a [@tailcall] annotation on the optimizable callsite.
      When one of several calls could be optimized, we expect that
      exactly one of them will be annotated by the user, or fail
      because the situation is ambiguous.
  *)

  let ensures_linear (c : lambda t) : lambda t =
    if c.is_linear then 
      c 
    else { c with
      dps = Dps.reify_delay (fun ~tail ~dst -> c.dps ~tail ~dst ~delayed:[]); 
      is_linear = true
    }
  (** Ensures that the resulting term makes linear use of the delayed
      constructors by applying them now if needed.
   *)

  let map_pure f s = {
      dps = Dps.map f s.dps;
      direct = (fun () -> f @@ s.direct ());
      is_linear = s.is_linear;
      uses_dps = s.uses_dps;
      benefits_from_dps = s.benefits_from_dps;
      explicit_tailcall_request = s.explicit_tailcall_request;
  }
  (** Apply function [f] to the transformed term.
    
      [f] must be "pure" with respect to the delayed constructors, that is,
      it must not move delayed constructors into effectful contexts.
    *)

  let map_impure (f : 'a -> lambda) (s : 'a t) : lambda t =
    let c = map_pure f s in
    { c with dps = Dps.delay_impure c.dps }
  (** Apply function [f] to the transformed term.
    
     [f] might create an effectful context, and hence all potentially effectful
     arguments to delayed constructors will be let-bound before being passed onto
     the context
    *)

  let return v = {
    dps = Dps.return v;
    direct = (fun () -> v);
    uses_dps = false;
    is_linear = true;
    benefits_from_dps = false;
    explicit_tailcall_request = false;
  }

  let empty v = {
    dps = Dps.empty v;
    direct = (fun () -> v);
    uses_dps = false;
    is_linear = false;
    benefits_from_dps = false;
    explicit_tailcall_request = false;
  }

  let pair (c1, c2) =
    {
      dps = Dps.pair c1.dps c2.dps;
      direct = (fun () -> (c1.direct (), c2.direct ()));
      is_linear = false;
      uses_dps = c1.uses_dps || c2.uses_dps;
      benefits_from_dps = c1.benefits_from_dps || c2.benefits_from_dps;
      explicit_tailcall_request = c1.explicit_tailcall_request || c2.explicit_tailcall_request;
    }

  let option (c : 'a t option) : 'a option t =
    match c with
    | None -> empty None
    | Some c -> map_pure (fun v -> Some v) c

  let rec list (c : 'a t list) : 'a list t =
    match c with
    | [] -> empty []
    | c :: cs ->
        map_pure
          (fun (v, vs) -> v :: vs)
          (pair (c, list cs))

  let direct (c : lambda t) : lambda = c.direct ()

  let dps (c : lambda t) ~tail ~dst =
    c.dps ~tail:tail ~dst:dst ~delayed:[]

  (** The [find_*] machinery is used to locate a single settable subterm
      to optimize among a list of subterms. If there are several possible choices,
      we require that exactly one of them be annotated with [@tailcall], or
      we report an ambiguity. *)
  type 'a find_settable_result =
    | All_returns of 'a list
    | Nonambiguous of 'a zipper
    | Ambiguous of 'a t list
  and 'a zipper =
    { rev_before : 'a list; settable : 'a t; after : 'a list }

  let find_nonambiguous_settable choices =
    let is_explicit s = s.explicit_tailcall_request in
    let nonambiguous ~explicit choices =
      (* here is how we will compute the result once we know that there
         is an unambiguously-determined settable, and whether
         an explicit request was necessary to disambiguate *)
      let rec split rev_before : 'a t list -> _ = function
        | [] -> assert false (* we know there is at least one settable *)
        | c :: rest when (c.uses_dps && (not explicit || is_explicit c)) ->
            { rev_before; settable = c; after = List.map direct rest }
        | c :: rest -> split (direct c :: rev_before) rest
      in split [] choices
    in
    let settable_subterms =
      List.filter (function c -> c.uses_dps) choices
    in
    match settable_subterms with
    | [] ->
        All_returns (List.map direct choices)
    | [ _one ] ->
        Nonambiguous (nonambiguous ~explicit:false choices)
    | several_subterms ->
        let explicit_subterms = List.filter is_explicit several_subterms in
        begin match explicit_subterms with
        | [] -> Ambiguous several_subterms
        | [ _one ] ->
            Nonambiguous (nonambiguous ~explicit:true choices)
        | several_explicit_subterms -> Ambiguous several_explicit_subterms
        end
end

let (let+) c f = Choice.map_impure f c
let (and+) c1 c2 = Choice.pair (c1, c2)

type context = {
  specialized: specialized Ident.Map.t;
}
and specialized = {
  arity: int;
  dps_id: Ident.t;
}

let find_specialized = function
  | Lfunction lfun when lfun.attr.trmc_candidate -> Some lfun
  | _ -> None

let declare_binding ctx (var, def) =
  match find_specialized def with
  | None -> ctx
  | Some lfun ->
  let arity = List.length lfun.params in
  let dps_id = Ident.create_local (Ident.name var ^ "_trmc") in
  let cand = { arity; dps_id } in
  { specialized = Ident.Map.add var cand ctx.specialized }

let rec choice ctx t =
  let rec choice ctx ~tail t =
    Choice.ensures_linear @@
    match t with
    | (Lvar _ | Lconst _ | Lfunction _ | Lsend _
      | Lassign _ | Lfor _ | Lwhile _) ->
        let t = traverse ctx t in
        Choice.return t

    (* [choice_prim] handles most primitives, but the important case of construction
       [Lprim(Pmakeblock(...), ...)] is handled by [choice_makeblock] *)
    | Lprim (prim, primargs, loc) ->
        choice_prim ctx ~tail prim primargs loc

    (* [choice_apply] handles applications, in particular tail-calls which
       generate Set choices at the leaves *)
    | Lapply apply ->
        choice_apply ctx ~tail apply
    (* other cases use the [lift] helper that takes the sub-terms in tail
       position and the context around them, and generates a choice for
       the whole term from choices for the tail subterms. *)
    | Lsequence (l1, l2) ->
        let l1 = traverse ctx l1 in
        let+ l2 = choice ctx ~tail l2 in
        Lsequence (l1, l2)
    | Lifthenelse (l1, l2, l3) ->
        let l1 = traverse ctx l1 in
        let+ (l2, l3) = choice_pair ctx ~tail (l2, l3) in
        Lifthenelse (l1, l2, l3)
    | Llet (lk, vk, var, def, body) ->
        (* non-recursive bindings are not specialized *)
        let def = traverse ctx def in
        let+ body = choice ctx ~tail body in
        Llet (lk, vk, var, def, body)
    | Lletrec (bindings, body) ->
        let ctx, bindings = traverse_letrec ctx bindings in
        let+ body = choice ctx ~tail body in
        Lletrec(bindings, body)
    | Lswitch (l1, sw, loc) ->
        (* decompose *)
        let consts_lhs, consts_rhs = List.split sw.sw_consts in
        let blocks_lhs, blocks_rhs = List.split sw.sw_blocks in
        (* transform *)
        let l1 = traverse ctx l1 in
        let+ consts_rhs = choice_list ctx ~tail consts_rhs
        and+ blocks_rhs = choice_list ctx ~tail blocks_rhs
        and+ sw_failaction = choice_option ctx ~tail sw.sw_failaction in
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
        let+ cases_rhs = choice_list ctx ~tail cases_rhs
        and+ fail = choice_option ctx ~tail fail in
        (* rebuild *)
        let cases = List.combine cases_lhs cases_rhs in
        Lstringswitch (l1, cases, fail, loc)
    | Lstaticraise (id, ls) ->
        let ls = traverse_list ctx ls in
        Choice.return (Lstaticraise (id, ls))
    | Ltrywith (l1, id, l2) ->
        (* in [try l1 with id -> l2], the term [l1] is
           not in tail-call position (after it returns
           we need to remove the exception handler),
           so it is not transformed here *)
        let l1 = traverse ctx l1 in
        let+ l2 = choice ctx ~tail l2 in
        Ltrywith (l1, id, l2)
    | Lstaticcatch (l1, ids, l2) ->
        (* In [static-catch l1 with ids -> l2],
           the term [l1] is in fact in tail-position *)
        let+ l1 = choice ctx ~tail l1
        and+ l2 = choice ctx ~tail l2 in
        Lstaticcatch (l1, ids, l2)
    | Levent (lam, lev) ->
        (* We can move effectful delayed constructors across events *)
        Choice.map_pure
          (fun lam -> Levent (lam, lev))
          (choice ctx ~tail lam)
    | Lifused (x, lam) ->
        let+ lam = choice ctx ~tail lam in
        Lifused (x, lam)

  and choice_apply ctx ~tail apply =
    let exception No_TRMC in
    try
      match apply.ap_func with
      | Lvar f ->
          let explicit_tailcall_request =
            match apply.ap_tailcall with
            | Should_be_tailcall -> true
            | Default_tailcall -> false
            | Should_not_be_tailcall ->
                (* [@tailcall false] disables TRMC optimization
                   on this tailcall *)
                raise No_TRMC
          in
          let specialized =
            try Ident.Map.find f ctx.specialized
            with Not_found ->
              if tail then
                Location.prerr_warning
                  (Debuginfo.Scoped_location.to_location apply.ap_loc)
                  Warnings.TRMC_breaks_tailcall;
              raise No_TRMC
          in
          Choice.{
            is_linear = true;
            uses_dps = true;
            benefits_from_dps = true;
            explicit_tailcall_request;
            dps = Dps.reify_delay @@ (fun ~tail ~dst ->
              Lapply { apply with
                       ap_func = Lvar specialized.dps_id;
                       ap_args = add_dst_args dst apply.ap_args;
                       ap_tailcall=
                         if tail then Should_be_tailcall else Default_tailcall;
            });
            direct = (fun () -> Lapply apply);
          }
      | _nontail -> raise No_TRMC
    with No_TRMC -> Choice.return (Lapply apply)

  and choice_makeblock ctx ~tail:_ (tag, flag, shape) blockargs loc =
    let choices = List.map (choice ~tail:false ctx) blockargs in
    match Choice.find_nonambiguous_settable choices with
    | Choice.Ambiguous subterms ->
        let subterms = List.map Choice.direct subterms in
        raise (Error (Debuginfo.Scoped_location.to_location loc,
                      Ambiguous_constructor_arguments subterms))
    | Choice.All_returns all_returns ->
        Choice.return @@ Lprim (Pmakeblock (tag, flag, shape), all_returns, loc)
    | Choice.Nonambiguous { Choice.rev_before; settable; after } ->
        let con = Constr.{
            tag = tag;
            flag = flag;
            shape = shape;
            before = List.rev rev_before;
            after = after;
            loc = loc
        } in
        assert settable.uses_dps;

        Choice.{
          explicit_tailcall_request =
            settable.explicit_tailcall_request;
          uses_dps = 
            (* The underlying settable must use dps, because that is what the
               [find_nonambiguous_settable] function looks for. *)
            true;
          is_linear =
            settable.is_linear;
          benefits_from_dps =
            (* Whether or not the caller provides a destination,
               we can always provide a destination to our settable
               subterm, so the number of TRMC sub-calls is identical
               in the [direct] and [dps] versions. *)
            false;
          direct = (fun () ->
            if not settable.benefits_from_dps then
              Constr.apply con (direct settable)
            else
              Constr.with_placeholder con @@ fun block_dst block ->
              Lsequence(dps settable ~tail:false ~dst:block_dst,
                        block)
          );
          dps = (fun ~tail ~dst ~delayed ->
            settable.dps ~tail ~dst ~delayed:(con :: delayed));
        }

  and choice_prim ctx ~tail prim primargs loc =
    match prim with
    (* The important case is the construction case *)
    | Pmakeblock (tag, flag, shape) ->
        choice_makeblock ctx ~tail (tag, flag, shape) primargs loc

    (* Some primitives have arguments in tail-position *)
    | (Pidentity | Popaque) as idop ->
        let l1 = match primargs with
          |  [l1] -> l1
          | _ -> invalid_arg "choice_prim" in
        let+ l1 = choice ctx ~tail l1 in
        Lprim (idop, [l1], loc)
    | (Psequand | Psequor) as shortcutop ->
        let l1, l2 = match primargs with
          |  [l1; l2] -> l1, l2
          | _ -> invalid_arg "choice_prim" in
        let l1 = traverse ctx l1 in
        let+ l2 = choice ctx ~tail l2 in
        Lprim (shortcutop, [l1; l2], loc)

    (* in common cases we just return *)
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
    (* TODO(gasche): Missed constructors due disabling exhaustivity checks.  I don't know
       what they do. *)
    | Pignore | Prevapply | Pdirapply | Pcompare_ints | Pcompare_floats | Pcompare_bints _
      ->
        let primargs = traverse_list ctx primargs in
        Choice.return (Lprim (prim, primargs, loc))

  and choice_list ctx ~tail (terms : lambda list) =
    Choice.list (List.map (choice ctx ~tail) terms)
  and choice_pair ctx ~tail ((t1, t2) : (lambda * lambda)) = 
    Choice.pair (choice ctx ~tail t1, choice ctx ~tail t2)
  and choice_option ctx ~tail (t : lambda option) =
    Choice.option (Option.map (choice ctx ~tail) t)

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
  match find_specialized def with
  | None -> [(var, traverse ctx def)]
  | Some lfun ->
  let cand = Ident.Map.find var ctx.specialized in
  let cand_choice = choice ctx ~tail:true lfun.body in
  begin if not cand_choice.Choice.uses_dps then
      Location.prerr_warning
        (Debuginfo.Scoped_location.to_location lfun.loc)
        Warnings.Unused_TRMC_attribute;
  end;
  let direct =
    Lfunction { lfun with body = Choice.direct cand_choice } in
  let dps =
    let dst = {
      var = Ident.create_local "dst";
      offset = Ident.create_local "offset";
      loc = lfun.loc;
    } in
    let dst_lam = { dst with offset = Lvar dst.offset } in
    Lambda.duplicate @@ Lfunction { lfun with (* TODO check function_kind *)
      params = add_dst_params dst lfun.params;
      body = Choice.dps cand_choice ~tail:true ~dst:dst_lam;
    } in
  let dps_var = cand.dps_id in
  [(var, direct); (dps_var, dps)]

and traverse_list ctx terms =
  List.map (traverse ctx) terms

let rewrite t =
  let ctx = { specialized = Ident.Map.empty } in
  traverse ctx t

let report_error ppf = function
  | Ambiguous_constructor_arguments subterms ->
      ignore subterms; (* TODO: find locations for each subterm *)
      Format.pp_print_text ppf
        "[@tailrec_mod_constr]: this constructor application may be \
         TRMC-transformed in several different ways. Please \
         disambiguate by adding an explicit [@tailcall] attribute to \
         the call that should be made tail-recursive, or a [@tailcall \
         false] attribute on calls that should not be transformed."
let () =
  Location.register_error_of_exn
    (function
      | Error (loc, err) ->
          Some (Location.error_of_printer ~loc report_error err)
      | _ ->
        None
    )
