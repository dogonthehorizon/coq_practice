(* Write the function that corresponsd to the polynomial 2 * x^2 + 3 * x + 3 on
   relative integers, using lambda abstraction and the functions Zplus and
   Zmult provided in the ZArith library of Coq. Compute the value of this
   function on integers 2, 3, 4.*)

Require Import ZArith.

Open Scope Z_scope.

Definition Z_poly (x:Z) : Z :=
  (Zplus (Zplus (Zmult 2 (Zmult x x)) (Zmult 3 x)) 3).

Eval compute in Z_poly.
Eval compute in (Z_poly 2).
Eval compute in (Z_poly 3).
Eval compute in (Z_poly 4).
