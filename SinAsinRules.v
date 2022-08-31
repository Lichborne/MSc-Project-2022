Require Import Reals.

Local Open Scope R_scope.

Axiom asin44: asin (sqrt 4 / sqrt 4) = (PI/2)%R.
Axiom asin34: asin (sqrt 3 / sqrt 4) = (PI/3)%R.
Axiom asin24: asin (sqrt 2 / sqrt 4) = (PI/4)%R.
Axiom asin14: asin (sqrt 1 / sqrt 4) = (PI/6)%R.

Local Close Scope R_scope.
