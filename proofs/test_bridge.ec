require import AllCore Distr.

(* Test A: bestaat er een ingebouwde duniform voor int? *)
op test_A : int distr = duniform 5.

(* Test B: bestaat dunit? *)
op test_B : int distr = dunit 5.
