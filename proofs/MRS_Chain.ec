
(* ================================================================= *)
(* MRS_Chain.ec                                                       *)
(* Arbitrary finite-depth chain construction for MRS.                 *)
(* Positive Anchor Convention: A_0 = dr(N) >= 1.                     *)
(* Frobenius boundary: 162.                                           *)
(* No fixed maximum depth.                                            *)
(* No axioms or admits declared in this file.                         *)
(* ================================================================= *)

require import AllCore Int IntDiv List.
require import MRS_Core.
require import MRS_Distr.

(* ----------------------------------------------------------------- *)
(* Chain construction                                                 *)
(*                                                                    *)
(* depth specifies the requested number of steps.                     *)
(* tri contains zero-based indices using sample_triangle.             *)
(* All other layers use sample_basic.                                 *)
(*                                                                    *)
(* For every finite depth >= 0, the loop performs exactly depth steps. *)
(* ----------------------------------------------------------------- *)

module MRSChain = {

  proc build(N : int, depth : int, tri : int list) : int list = {
    var chain, current, a, b, i;

    chain   <- [N];
    current <- N;
    i       <- 0;

    while (i < depth) {
      if (mem i tri) {
        (a, b) <@ MRSRep.sample_triangle(current);
      } else {
        (a, b) <@ MRSRep.sample_basic(current);
      }

      chain   <- chain ++ [a; b];
      current <- a;
      i       <- i + 1;
    }

    return chain;
  }
}.
