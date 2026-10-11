require import AllCore Distr.

(* Test 1: bestaat dunit? *)
op t1 : int distr = dunit 5.

(* Test 2: bestaat er een ingebouwde uniforme distributie op finType? *)
op t2 : bool distr = duniform.

(* Test 3: werkt dmap? *)
op t3 : int distr = dmap (dunit 5) (fun (x : int) => x + 1).
