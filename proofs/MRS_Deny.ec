(* ================================================================= *)
(*  MRS_Deny.ec                                                       *)
(*  Formal deniability: no adversary does better than 50%             *)
(*                                                                    *)
(*  SCOPE NOTE:                                                       *)
(*  This file proves that two independent calls to MRSChain.build,    *)
(*  with IDENTICAL arguments (N, depth, tri), are indistinguishable   *)
(*  — i.e. chain-selection uniformity for a single sampler under a    *)
(*  single set of parameters.                                          *)
(*                                                                    *)
(*  It does NOT model:                                                 *)
(*    - master_secret, or the HMAC-based deterministic seed            *)
(*      derivation used to produce the "authentic" witness             *)
(*    - identity / session_id binding                                  *)
(*    - the binding_tag, or any asymmetry between the authentic-       *)
(*      generation path (DeterministicRng from an HMAC seed) and the   *)
(*      alternative-generation path (OsRng)                            *)
(*                                                                    *)
(*  The fuller scenario, including the computational (not              *)
(*  information-theoretic) assumptions it relies on and its explicit   *)
(*  limitations, is argued separately in                               *)
(*  proofs/WITNESS-INDISTINGUISHABILITY.md. This file establishes a    *)
(*  narrower, purely combinatorial fact about the sampler, not a       *)
(*  machine-verified proof of the full protocol's deniability.         *)
(* ================================================================= *)

require import MRS_Chain.
import MRSChain.

module type Adversary = {
  proc guess(chain : int list) : bool
}.

module DenyGame (A : Adversary) = {
  proc main(N : int, depth : int, tri : int list) : bool = {
    var ch0, ch1, b, b';
    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);
    b   <$ {0,1};
    if (b) then b' <@ A.guess(ch1)
           else b' <@ A.guess(ch0);
    return (b' = b);
  }
}.

lemma ch0_ch1_same_distr (N : int) (depth : int) (tri : int list) :
  N > 162 =>
  equiv [MRSChain.build ~ MRSChain.build :
    arg{1} = (N, depth, tri) /\ arg{2} = (N, depth, tri) ==> ={res}].
proof.
  move=> hN.
  have := build_equiv N depth tri hN.
  conseq => />.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Main theorem: sampler-level chain-selection indistinguishability   *)
(* ----------------------------------------------------------------- *)
lemma deny_advantage (A <: Adversary) (N : int) (depth : int) (tri : int list) :
  N > 162 =>
  Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.
proof.
  move=> hN.
  byphoare => //.
  proc.

  seq 3 : b (1%r/2%r) (1%r) (1%r/2%r) (0%r).
  - call (build_equiv N depth tri hN).
    call (build_equiv N depth tri hN).
    rnd.
    auto.

  - if => />.
    have key : forall (ch : int list),
      phoare [A.guess : arg = ch ==> true] = 1%r.
      move=> ch; proc *; auto.
    call (key ch1).
    auto.

  - if => />.
    have key : forall (ch : int list),
      phoare [A.guess : arg = ch ==> true] = 1%r.
      move=> ch; proc *; auto.
    call (key ch0).
    auto.

  - hoare; auto.

  byequiv => //.
  proc.
  seq 2 2 : (ch0{1} = ch1{2} /\ ch1{1} = ch0{2} /\ ={b, tri, depth}).
  - call (ch0_ch1_same_distr N depth tri hN).
    call (ch0_ch1_same_distr N depth tri hN).
    auto.
  if => />; call (: true); auto.
qed.
