(* TEST
   * expect *)

(* build-up *)
let[@tailrec_mod_constr] rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: append xs ys
[%%expect {|
val append : 'a list -> 'a list -> 'a list = <fun>
|}]

(* incorrect version: this cannot work *)
let[@tailrec_mod_constr] rec flatten = function
  | [] -> []
  | xs :: xss -> append xs (flatten xss)
[%%expect {|
Line 3, characters 17-40:
3 |   | xs :: xss -> append xs (flatten xss)
                     ^^^^^^^^^^^^^^^^^^^^^^^
Warning 70: This call is in tail-position in a TRMC function, but
the function called is not itself specialized for TRMC,
so the call will not be in tail position in the transformed
version.
Please either mark the called function with the
[@tailrec_mod_constr] attribute, or mark this call with the
[@tailcall false] attribute to make its non-tailness explicit.
Lines 1-3, characters 39-40:
1 | .......................................function
2 |   | [] -> []
3 |   | xs :: xss -> append xs (flatten xss)
Warning 69: This function is marked [@tailrec_mod_constr] but is never applied in TRMC position.
val flatten : 'a list list -> 'a list = <fun>
|}]

(* correct version *)
let[@tailrec_mod_constr] rec flatten = function
  | [] -> []
  | xs :: xss ->
      let[@tailrec_mod_constr] rec append_flatten xs xss =
        match xs with
        | [] -> flatten xss
        | x :: xs -> x :: append_flatten xs xss
      in append_flatten xs xss
[%%expect {|
val flatten : 'a list list -> 'a list = <fun>
|}]

(* incorrect version *)
let[@tailrec_mod_constr] rec flatten = function
  | [] -> []
  | xs :: xss ->
      let rec append_flatten xs xss =
        match xs with
        | [] -> flatten xss
        | x :: xs ->
            (* incorrect: this call to append_flatten is not transformed *)
            x :: append_flatten xs xss
      in append_flatten xs xss
[%%expect {|
Line 10, characters 9-30:
10 |       in append_flatten xs xss
              ^^^^^^^^^^^^^^^^^^^^^
Warning 70: This call is in tail-position in a TRMC function, but
the function called is not itself specialized for TRMC,
so the call will not be in tail position in the transformed
version.
Please either mark the called function with the
[@tailrec_mod_constr] attribute, or mark this call with the
[@tailcall false] attribute to make its non-tailness explicit.
Lines 1-10, characters 39-30:
 1 | .......................................function
 2 |   | [] -> []
 3 |   | xs :: xss ->
 4 |       let rec append_flatten xs xss =
 5 |         match xs with
 6 |         | [] -> flatten xss
 7 |         | x :: xs ->
 8 |             (* incorrect: this call to append_flatten is not transformed *)
 9 |             x :: append_flatten xs xss
10 |       in append_flatten xs xss
Warning 69: This function is marked [@tailrec_mod_constr] but is never applied in TRMC position.
val flatten : 'a list list -> 'a list = <fun>
|}]

(* incorrect version: the call to append-flatten is not transformed *)
let rec flatten = function
  | [] -> []
  | xs :: xss ->
      let[@tailrec_mod_constr] rec append_flatten xs xss =
        match xs with
        | [] ->
            (* incorrect: if flatten does not have a TRMC version,
               this call is not tail-recursive in the TRMC version of
               append-flatten, so this version is in fact equivalent
               to the "cannot work" version above: the "append" part
               runs in constant stack space, but the "flatten" part is
               not tail-recursive. *)
            flatten xss
        | x :: xs ->
            x :: append_flatten xs xss
      in append_flatten xs xss
[%%expect {|
Line 13, characters 12-23:
13 |             flatten xss
                 ^^^^^^^^^^^
Warning 70: This call is in tail-position in a TRMC function, but
the function called is not itself specialized for TRMC,
so the call will not be in tail position in the transformed
version.
Please either mark the called function with the
[@tailrec_mod_constr] attribute, or mark this call with the
[@tailcall false] attribute to make its non-tailness explicit.
val flatten : 'a list list -> 'a list = <fun>
|}]
