require import AllCore Distr.

(* Test 1: bestaat dunit? *)
op t1 : int distr = dunit 5.

(* Test 2: duniform op een expliciete lijst *)
op t2 : int distr = duniform [0; 1; 2; 3; 4].

(* Test 3: werkt dmap? *)
op t3 : int distr = dmap (dunit 5) (fun (x : int) => x + 1).

(* Test 4: bestaat er een ingebouwde duniform voor int? *)
op t4 : int distr = duniform 5.
