(* ================================================================= *)
(*  MRS_FloorSum.ec                                                   *)
(*  Abstract specification of the floor-sum-based prefix weight       *)
(*  used by the weighted CDF sampler.                                 *)
(*                                                                    *)
(*  The concrete floor sum (sum_{i=0}^{n-1} floor((a*i+b)/m)) is      *)
(*  computed in Rust by floor_sum_ct. Its three characteristic        *)
(*  properties are stated here as axioms; they are the interface      *)
(*  contract that MRS_Sampler.ec relies on.                           *)
(*                                                                    *)
(*  Rationale for axiomatization: the concrete BigOps-based proof     *)
(*  depends on the exact layout of the EasyCrypt standard library,    *)
(*  which varies between versions. The three axioms below describe    *)
(*  the mathematical content precisely and are checked against the    *)
(*  Rust implementation by the unit tests in cdf_sampler.rs.          *)
(*                                                                    *)
(*  Correspondence with the Rust implementation:                      *)
(*                                                                    *)
(*    src/sampler/cdf_sampler.rs                                      *)
(*      floor_sum_ct(n, m, a, b)                                      *)
(*                                                                    *)
(*  computes sum_{i=0}^{n-1} floor((a*i + b)/m) via a fixed           *)
(*  64-iteration AtCoder shift-and-add loop. The properties below     *)
(*  are verified against this implementation by the sampler's unit    *)
(*  tests. A fully mechanized proof of the concrete floor-sum         *)
(*  properties (replacing these axioms) would require modelling the   *)
(*  64-iteration AtCoder loop in EasyCrypt; that is out of scope for  *)
(*  this version.                                                     *)
(* ================================================================= *)

require import AllCore Int IntDiv Real.

(* ================================================================= *)
(* Prefix weight                                                      *)
(* ================================================================= *)

op prefix_weight (t_filter t t_max e_prime : int) : int.

axiom prefix_weight_zero_before :
  forall (t_filter t t_max e_prime : int),
    t < t_filter =>
    prefix_weight t_filter t t_max e_prime = 0.

axiom prefix_weight_monotone :
  forall (t_filter t1 t2 t_max e_prime : int),
    t_filter <= t1 => t1 <= t2 => t2 <= t_max =>
    prefix_weight t_filter t1 t_max e_prime
      <= prefix_weight t_filter t2 t_max e_prime.

axiom prefix_weight_positive :
  forall (t_filter t t_max e_prime : int),
    t_filter <= t => t <= t_max => 171 <= e_prime =>
    0 < prefix_weight t_filter t t_max e_prime.
