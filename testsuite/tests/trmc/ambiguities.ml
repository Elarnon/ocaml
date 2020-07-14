(* TEST
   * expect *)
type 'a tree =
| Leaf of 'a
| Node of 'a tree * 'a tree
[%%expect{|
type 'a tree = Leaf of 'a | Node of 'a tree * 'a tree
|}]

module Ambiguous = struct
  let[@tailrec_mod_constr] rec map f = function
  | Leaf v -> Leaf (f v)
  | Node (left, right) ->
    Node (map f left, map f right)
end
[%%expect{|
Line 5, characters 4-34:
5 |     Node (map f left, map f right)
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: [@tailrec_mod_constr]: this constructor application may be trmc-transformed in
       several different ways. Please disambiguate by adding an explicit
       [@tailcall] attribute to the call that should be made tail-recursive,
       or a [@tailcall false] attribute on calls that should not be
       transformed.
|}]

module Positive_disambiguation = struct
  let[@tailrec_mod_constr] rec map f = function
  | Leaf v -> Leaf (f v)
  | Node (left, right) ->
    Node (map f left, (map [@tailcall]) f right)
end
[%%expect{|
module Positive_disambiguation :
  sig val map : ('a -> 'b) -> 'a tree -> 'b tree end
|}]

module Negative_disambiguation = struct
  let[@tailrec_mod_constr] rec map f = function
  | Leaf v -> Leaf (f v)
  | Node (left, right) ->
    Node ((map [@tailcall false]) f left, map f right)
end
[%%expect{|
module Negative_disambiguation :
  sig val map : ('a -> 'b) -> 'a tree -> 'b tree end
|}]
