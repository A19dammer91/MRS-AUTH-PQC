(* ================================================================= *)
(*  MRS_Chain.ec                                                      *)
(*  Arbitrary finite-depth chain construction for MRS.                *)
(*  Positive Anchor Convention: A_0 = dr(N) >= 1.                    *)
(*  Frobenius boundary: 162.                                          *)
(*  No fixed maximum depth.                                           *)
(*  No axioms or admits declared in this file.                        *)
(* ================================================================= *)

require import AllCore Int IntDiv List.
require import MRS_Core.
require import MRS_Distr.
require import MRS_Equiv.

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
      if (mem tri i) {
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

(* ================================================================= *)
(* Equivalence of two chain executions with identical inputs.        *)
(*                                                                    *)
(* The proof uses a `while`-invariant that keeps the loop variables   *)
(* and the sampled pair equal on both sides. At each iteration, the   *)
(* `if (mem tri i)` condition is the same on both sides (since tri    *)
(* and i are equal), so the same branch is taken. The sampler called  *)
(* is therefore the same on both sides, and its equivalence lemma     *)
(* (`sample_basic_equiv` or `sample_triangle_equiv`) provides the     *)
(* required equality.                                                 *)
(* ================================================================= *)

lemma build_equiv (N depth : int) (tri : int list) :
  162 < N =>
  equiv [MRSChain.build ~ MRSChain.build :
    arg{1} = (N, depth, tri) /\
    arg{2} = (N, depth, tri) ==>
    ={res}].
proof.
  move=> hN.
  proc.
  while (={i, chain, current, N, depth, tri, a, b} /\ 162 < current).
  - (* Loop body: preserve the invariant. *)
    if => />.
    + (* Branch: mem tri i — use sample_triangle *)
      call (sample_triangle_equiv current{1} hN).
      auto => />.
    + (* Branch: ! mem tri i — use sample_basic *)
      call (sample_basic_equiv current{1} hN).
      auto => />.
  - (* Loop entry: invariant holds initially. *)
    auto => />.
qed.

(* ================================================================= *)
(* End of MRS_Chain.ec                                                *)
(* ================================================================= *)
