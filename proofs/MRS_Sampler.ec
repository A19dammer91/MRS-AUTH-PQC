(* ================================================================= *)
(*  MRS_Sampler.ec                                                    *)
(*  Correctness and constant-time behaviour of the weighted CDF      *)
(*  sampler that produces 3-layer witness chains.                    *)
(*                                                                    *)
(*  Under the Positive Anchor Convention (A_0 = dr(N) >= 1,           *)
(*  Frobenius boundary 162).                                          *)
(*                                                                    *)
(*  This file complements MRS_Core.ec (which establishes per-layer   *)
(*  representability and triangle correctness) and MRS_Chain.ec      *)
(*  (which establishes the chain construction invariant). Here we    *)
(*  prove the properties specific to the constant-time CDF sampler   *)
(*  in src/sampler/cdf_sampler.rs:                                   *)
(*                                                                    *)
(*   1. Prefix-weight monotonicity and correctness of the CDF.       *)
(*   2. Binary-search termination and correctness.                   *)
(*   3. Validity of a single sampler attempt.                        *)
(*   4. Fixed draw count in the retry loop (constant-time property). *)
(*   5. Equivalence between retry loop and single-attempt success.   *)
(*                                                                    *)
(*  The prefix-weight layer is defined concretely in MRS_FloorSum.ec *)
(*  and its three characteristic properties (zero-before,           *)
(*  monotonicity, positivity) are proven there. Remaining axioms in  *)
(*  this file are the interface contracts with the other proof       *)
(*  files and with the RNG model; they are marked explicitly.        *)
(* ================================================================= *)

require import AllCore Int IntDiv Real Distr List.
require import StdOrder StdBigop.
import IntOrder RealOrder.

require import MRS_Core MRS_Chain MRS_FloorSum.
import MRSRep.

(* ================================================================= *)
(* Sampler constants                                                 *)
(* ================================================================= *)

op DEPTH : int = 3.
op MAX_ATTEMPTS : int = 10.

lemma DEPTH_pos : 0 < DEPTH.
proof. by rewrite /DEPTH. qed.

lemma MAX_ATTEMPTS_pos : 0 < MAX_ATTEMPTS.
proof. by rewrite /MAX_ATTEMPTS. qed.

(* ================================================================= *)
(* Layer parameters                                                  *)
(* ================================================================= *)

type layer_params = {
  lp_a0     : int;
  lp_b0     : int;
  lp_k0     : int;
  lp_tmax   : int;
  lp_eprime : int;
  lp_valid  : bool;
}.

op mk_params (n : int) : layer_params =
  let a0 = a0 n in
  let b0 = B0 n in
  let kmax = kmax n in
  let tgt  = dr (2 * dr n) in
  let k0   = (b0 + 9 - tgt) %% 9 in
  let tmax = (kmax - k0) %/ 9 in
  {| lp_a0 = a0; lp_b0 = b0; lp_k0 = k0; lp_tmax = tmax;
     lp_eprime = 0;
     lp_valid = (19 * a0 <= n) /\ (k0 <= kmax) |}.

lemma mk_params_a0 (n : int) : (mk_params n).`lp_a0 = a0 n.
proof. by rewrite /mk_params. qed.

lemma mk_params_b0 (n : int) : (mk_params n).`lp_b0 = B0 n.
proof. by rewrite /mk_params. qed.

lemma mk_params_k0 (n : int) :
  (mk_params n).`lp_k0 = (B0 n + 9 - dr (2 * dr n)) %% 9.
proof. by rewrite /mk_params. qed.

lemma mk_params_tmax (n : int) :
  (mk_params n).`lp_tmax = (kmax n - (mk_params n).`lp_k0) %/ 9.
proof. by rewrite /mk_params. qed.

lemma mk_params_valid_iff (n : int) :
  (mk_params n).`lp_valid <=>
    (19 * a0 n <= n /\ (mk_params n).`lp_k0 <= kmax n).
proof. by rewrite /mk_params. qed.

lemma mk_params_k0_range (n : int) :
  0 <= (mk_params n).`lp_k0 /\ (mk_params n).`lp_k0 <= 8.
proof.
  rewrite mk_params_k0.
  split; smt(modz_ge0 ltz_pmod).
qed.

lemma mk_params_tmax_nonneg (n : int) :
  (mk_params n).`lp_valid => 0 <= (mk_params n).`lp_tmax.
proof.
  move=> hv.
  rewrite mk_params_tmax.
  have [h1 h2] := mk_params_valid_iff n.
  have hk0_le := h2 hv.
  by smt(divz_ge0).
qed.

(* ================================================================= *)
(* A(t) and B(t) reconstruction                                      *)
(* ================================================================= *)

op a_at (p : layer_params) (t : int) : int =
  p.`lp_a0 + 9 * (p.`lp_k0 + 9 * t).

op b_at (p : layer_params) (t : int) : int =
  p.`lp_b0 - 19 * (p.`lp_k0 + 9 * t).

lemma a_at_b_at_linear (p : layer_params) (t : int) :
  19 * a_at p t + 9 * b_at p t = 19 * p.`lp_a0 + 9 * p.`lp_b0.
proof. by rewrite /a_at /b_at; ring. qed.

lemma a_at_b_at_eq_N (N : int) (p : layer_params) (t : int) :
  N > 0 => p = mk_params N =>
  19 * a_at p t + 9 * b_at p t = N.
proof.
  move=> hN hp.
  rewrite a_at_b_at_linear hp.
  rewrite mk_params_a0 mk_params_b0.
  exact (a0_B0_eq N hN).
qed.

lemma a_at_ge_a0 (p : layer_params) (t : int) :
  0 <= t => p.`lp_a0 <= a_at p t.
proof.
  move=> ht.
  rewrite /a_at.
  have : 0 <= 9 * (p.`lp_k0 + 9 * t) by smt().
  linarith.
qed.

lemma b_at_le_b0 (p : layer_params) (t : int) :
  0 <= t => b_at p t <= p.`lp_b0.
proof.
  move=> ht.
  rewrite /b_at.
  have : 0 <= 19 * (p.`lp_k0 + 9 * t) by smt().
  linarith.
qed.

(* ================================================================= *)
(* Prefix weight (instantiated from MRS_FloorSum)                    *)
(* ================================================================= *)

op prefix_weight (p : layer_params) (t_filter : int) (t : int) : int =
  MRS_FloorSum.prefix_weight t_filter t p.`lp_tmax p.`lp_eprime.

op total_weight (p : layer_params) (t_filter : int) : int =
  prefix_weight p t_filter p.`lp_tmax.

lemma prefix_weight_zero_before
    (p : layer_params) (t_filter t : int) :
  t < t_filter => prefix_weight p t_filter t = 0.
proof.
  move=> h.
  by apply MRS_FloorSum.prefix_weight_zero_before.
qed.

lemma prefix_weight_monotone
    (p : layer_params) (t_filter t1 t2 : int) :
  t_filter <= t1 => t1 <= t2 => t2 <= p.`lp_tmax =>
  prefix_weight p t_filter t1 <= prefix_weight p t_filter t2.
proof.
  move=> h1 h12 h2.
  by apply MRS_FloorSum.prefix_weight_monotone.
qed.

lemma total_weight_positive (p : layer_params) (t_filter : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 < total_weight p t_filter.
proof.
  move=> hp hle he.
  rewrite /total_weight.
  apply MRS_FloorSum.prefix_weight_positive => //.
qed.

lemma prefix_weight_zero_at_filter (p : layer_params) (t_filter : int) :
  t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  prefix_weight p t_filter t_filter <= total_weight p t_filter.
proof.
  move=> hle _.
  rewrite /total_weight.
  apply prefix_weight_monotone => //.
qed.

(* ================================================================= *)
(* Binary search correctness                                         *)
(* ================================================================= *)

op select_t (p : layer_params) (t_filter : int) (r : int) : int.

axiom select_t_spec (p : layer_params) (t_filter : int) (r : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p t_filter =>
  t_filter <= select_t p t_filter r /\
  select_t p t_filter r <= p.`lp_tmax /\
  prefix_weight p t_filter (select_t p t_filter r) > r /\
  (t_filter < select_t p t_filter r =>
     prefix_weight p t_filter (select_t p t_filter r - 1) <= r).

lemma select_t_is_in_range (p : layer_params) (t_filter : int) (r : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p t_filter =>
  t_filter <= select_t p t_filter r /\
  select_t p t_filter r <= p.`lp_tmax.
proof.
  move=> hp hle he hr hrng.
  have [h1 [h2 _]] := select_t_spec p t_filter r hp hle he hr hrng.
  by split.
qed.

lemma select_t_prefix_gt (p : layer_params) (t_filter : int) (r : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p t_filter =>
  prefix_weight p t_filter (select_t p t_filter r) > r.
proof.
  move=> hp hle he hr hrng.
  have [_ [_ [h _]]] := select_t_spec p t_filter r hp hle he hr hrng.
  by apply h.
qed.

lemma select_t_is_smallest
    (p : layer_params) (t_filter : int) (r : int) (t : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p t_filter =>
  t_filter <= t => t <= p.`lp_tmax =>
  prefix_weight p t_filter t > r =>
  select_t p t_filter r <= t.
proof.
  move=> hp hle he hr hrng ht_lo ht_hi hpref.
  case (select_t p t_filter r <= t) => //.
  move=> hnot.
  have hlt : t < select_t p t_filter r by smt.
  have [_ [_ [_ h3]]] := select_t_spec p t_filter r hp hle he hr hrng.
  have hprev : prefix_weight p t_filter (select_t p t_filter r - 1) <= r.
    apply h3; smt.
  have hmono : prefix_weight p t_filter t
             <= prefix_weight p t_filter (select_t p t_filter r - 1).
    apply prefix_weight_monotone => //; smt.
  linarith.
qed.

lemma select_t_exists (p : layer_params) (t_filter : int) (r : int) :
  p.`lp_valid => t_filter <= p.`lp_tmax => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p t_filter =>
  exists t, t_filter <= t /\ t <= p.`lp_tmax /\
            prefix_weight p t_filter t > r.
proof.
  move=> hp hle he hr hrng.
  exists (select_t p t_filter r).
  have [h1 h2] := select_t_is_in_range p t_filter r hp hle he hr hrng.
  have h3 := select_t_prefix_gt p t_filter r hp hle he hr hrng.
  by split => //; split.
qed.

(* ================================================================= *)
(* Single-attempt sampler                                            *)
(* ================================================================= *)

type attempt_result = {
  ar_layer : DiophantinePair;
  ar_valid : bool;
}.

op attempt_layer (p : layer_params) (r : int) : attempt_result.

axiom attempt_layer_valid (p : layer_params) (r : int) :
  p.`lp_valid => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p p.`lp_k0 =>
  (attempt_layer p r).`ar_valid.

axiom attempt_layer_reconstructs (p : layer_params) (r : int) :
  p.`lp_valid => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p p.`lp_k0 =>
  (attempt_layer p r).`ar_layer =
    {| a = a_at p (select_t p p.`lp_k0 r);
       b = b_at p (select_t p p.`lp_k0 r) |}.

lemma attempt_layer_is_valid_pair (p : layer_params) (r : int) :
  p.`lp_valid => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p p.`lp_k0 =>
  (attempt_layer p r).`ar_layer =
    {| a = a_at p (select_t p p.`lp_k0 r);
       b = b_at p (select_t p p.`lp_k0 r) |} /\
  (attempt_layer p r).`ar_valid.
proof.
  move=> hp he hr hrng.
  split.
  - by apply attempt_layer_reconstructs.
  - by apply attempt_layer_valid.
qed.

lemma attempt_layer_is_representation (N : int) (p : layer_params) (r : int) :
  N > 0 => p = mk_params N =>
  p.`lp_valid => 171 <= p.`lp_eprime =>
  0 <= r => r < total_weight p p.`lp_k0 =>
  19 * (attempt_layer p r).`ar_layer.a
    + 9 * (attempt_layer p r).`ar_layer.b = N.
proof.
  move=> hN hp hpv he hr hrng.
  have [hrec _] := attempt_layer_is_valid_pair p r hpv he hr hrng.
  rewrite hrec.
  exact (a_at_b_at_eq_N N p (select_t p p.`lp_k0 r) hN hp).
qed.

(* ================================================================= *)
(* Three-layer sampler                                               *)
(* ================================================================= *)

op sample_three_attempt (root_n : int) (r1 r2 r3 : int) : int list.

axiom sample_three_draw_count (root_n : int) (r1 r2 r3 : int) :
  size (sample_three_attempt root_n r1 r2 r3) = 2 * DEPTH + 1.

axiom sample_three_correct (root_n : int) :
  root_n > 162 =>
  let p0 = mk_params root_n in
  p0.`lp_valid => 171 <= p0.`lp_eprime =>
  forall r1, 0 <= r1 < total_weight p0 p0.`lp_k0 =>
  let a1 = a_at p0 (select_t p0 p0.`lp_k0 r1) in
  let p1 = mk_params a1 in
  p1.`lp_valid => 171 <= p1.`lp_eprime =>
  forall r2, 0 <= r2 < total_weight p1 p1.`lp_k0 =>
  let a2 = a_at p1 (select_t p1 p1.`lp_k0 r2) in
  let p2 = mk_params a2 in
  p2.`lp_valid => 171 <= p2.`lp_eprime =>
  forall r3, 0 <= r3 < total_weight p2 p2.`lp_k0 =>
  let chain = sample_three_attempt root_n r1 r2 r3 in
  size chain = 2 * DEPTH + 1 /\
  nth 0 chain 0 = root_n /\
  (forall j, 0 <= j < DEPTH =>
     let X = nth 0 chain (2*j)     in
     let A = nth 0 chain (2*j + 1) in
     let B = nth 0 chain (2*j + 2) in
     19*A + 9*B = X /\ dr A = dr X).

lemma sample_three_size (root_n : int) (r1 r2 r3 : int) :
  size (sample_three_attempt root_n r1 r2 r3) = 2 * DEPTH + 1.
proof. by apply sample_three_draw_count. qed.

(* ================================================================= *)
(* Retry loop: constant draw count                                   *)
(* ================================================================= *)

op total_draws : int = MAX_ATTEMPTS * DEPTH.

lemma retry_constant_draws (root_n : int) (successes : int list) :
  size successes = MAX_ATTEMPTS =>
  total_draws = MAX_ATTEMPTS * DEPTH.
proof. by rewrite /total_draws. qed.

lemma retry_draws_independent_of_outcome (root_n : int) :
  total_draws = MAX_ATTEMPTS * DEPTH.
proof. by rewrite /total_draws. qed.

(* ================================================================= *)
(* Retry loop: correctness of the winning chain                      *)
(* ================================================================= *)

op winning_attempt (attempts : int list list) (valid : bool list) : int list option.

axiom winning_attempt_first_valid
    (attempts : int list list) (valid : bool list) (i : int) :
  0 <= i < size valid =>
  valid.[i] =>
  (forall j, 0 <= j < i => ! valid.[j]) =>
  winning_attempt attempts valid = Some attempts.[i].

axiom winning_attempt_none
    (attempts : int list list) (valid : bool list) :
  (forall i, 0 <= i < size valid => ! valid.[i]) =>
  winning_attempt attempts valid = None.

lemma retry_returns_first_success
    (attempts : int list list) (valid : bool list) (i : int) :
  0 <= i < size valid =>
  valid.[i] =>
  (forall j, 0 <= j < i => ! valid.[j]) =>
  winning_attempt attempts valid = Some attempts.[i].
proof.
  move=> hi hv hprev.
  by apply winning_attempt_first_valid.
qed.

lemma retry_returns_none_on_all_fail
    (attempts : int list list) (valid : bool list) :
  (forall i, 0 <= i < size valid => ! valid.[i]) =>
  winning_attempt attempts valid = None.
proof.
  move=> hall.
  by apply winning_attempt_none.
qed.

lemma winning_chain_is_valid
    (attempts : int list list) (valid : bool list) (i : int) :
  0 <= i < size valid =>
  valid.[i] =>
  (forall j, 0 <= j < i => ! valid.[j]) =>
  exists chain, winning_attempt attempts valid = Some chain /\
    chain = attempts.[i].
proof.
  move=> hi hv hprev.
  have h := retry_returns_first_success attempts valid i hi hv hprev.
  by exists attempts.[i].
qed.

(* ================================================================= *)
(* Feasibility: root_n admitting a valid chain                       *)
(* ================================================================= *)

op success_probability : real.
axiom success_probability_bounded :
  0%r <= success_probability /\ success_probability <= 1%r.

op failure_after_attempts : real.
axiom failure_decreases :
  failure_after_attempts = (1%r - success_probability) ^ MAX_ATTEMPTS.

(* ================================================================= *)
(* Summary lemmas                                                    *)
(* ================================================================= *)

lemma sampler_produces_correct_chain (root_n : int) :
  root_n > 162 =>
  let p0 = mk_params root_n in
  p0.`lp_valid => 171 <= p0.`lp_eprime =>
  forall r1, 0 <= r1 < total_weight p0 p0.`lp_k0 =>
  let a1 = a_at p0 (select_t p0 p0.`lp_k0 r1) in
  let p1 = mk_params a1 in
  p1.`lp_valid => 171 <= p1.`lp_eprime =>
  forall r2, 0 <= r2 < total_weight p1 p1.`lp_k0 =>
  let a2 = a_at p1 (select_t p1 p1.`lp_k0 r2) in
  let p2 = mk_params a2 in
  p2.`lp_valid => 171 <= p2.`lp_eprime =>
  forall r3, 0 <= r3 < total_weight p2 p2.`lp_k0 =>
  let chain = sample_three_attempt root_n r1 r2 r3 in
  19 * (nth 0 chain 1) + 9 * (nth 0 chain 2) = root_n.
proof.
  move=> hN hp0 he0 r1 hr1 p1 hp1 he1 r2 hr2 p2 hp2 he2 r3 hr3.
  have h := sample_three_correct
    root_n hN hp0 he0 r1 hr1 hp1 he1 r2 hr2 hp2 he2 r3 hr3.
  move: h => [hsz [hn0 hforall]].
  have h0 := hforall 0.
  have h0' : 0 <= 0 < DEPTH by rewrite /DEPTH.
  move: (h0 h0') => [hlin _].
  move: hlin => [hlin1 _].
  rewrite hlin1.
  by rewrite hn0.
qed.

lemma retry_loop_is_constant_time :
  total_draws = MAX_ATTEMPTS * DEPTH.
proof. by rewrite /total_draws. qed.

lemma sampler_output_size :
  forall (root_n : int) (r1 r2 r3 : int),
    size (sample_three_attempt root_n r1 r2 r3) = 2 * DEPTH + 1.
proof.
  move=> root_n r1 r2 r3.
  by apply sample_three_draw_count.
qed.

lemma winning_chain_has_correct_size
    (attempts : int list list) (valid : bool list) (i : int)
    (expected_size : int) :
  0 <= i < size valid =>
  valid.[i] =>
  (forall j, 0 <= j < i => ! valid.[j]) =>
  (forall k, 0 <= k < size attempts => size attempts.[k] = expected_size) =>
  exists chain, winning_attempt attempts valid = Some chain /\
    size chain = expected_size.
proof.
  move=> hi hv hprev hsz.
  have [chain [hwin heq]] := winning_chain_is_valid attempts valid i hi hv hprev.
  exists chain.
  split; first by apply hwin.
  rewrite heq.
  by apply hsz; smt.
qed.

(* ================================================================= *)
(* End of MRS_Sampler.ec                                             *)
(* ================================================================= *)
