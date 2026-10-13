(* ================================================================= *)
(*  MRS_AUTH.ec                                                       *)
(*  Time-based Authentication                                         *)
(*                                                                    *)
(*  Under the Positive Anchor Convention (A_0 = dr(N) >= 1,           *)
(*  Frobenius boundary 162).                                          *)
(*                                                                    *)
(*  Three main components:                                            *)
(*   I. Temporal Barrier (timing + zeroize)                           *)
(*  II. HMAC as PRF and EUF-CMA security                              *)
(* III. Forward Secrecy                                               *)
(* ================================================================= *)

require import AllCore Int IntDiv Real Distr List FSet SmtMap.
require import StdOrder StdBigop.
import IntOrder RealOrder.
require import MRS_Core.

(* ================================================================= *)
(* PART I: Temporal Barrier                                          *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* Digital-root lemmas for the temporal barrier                       *)
(* ----------------------------------------------------------------- *)

lemma dr_homomorphism (x y : int) :
  0 < x => 0 < y =>
  dr (x + y) = dr (dr x + dr y).
proof.
  move=> hx hy.
  have hxy_pos : 0 < x + y by smt().
  have hdx_pos : 0 < dr x by smt(dr_range).
  have hdy_pos : 0 < dr y by smt(dr_range).
  have hdxy_pos : 0 < dr x + dr y by smt().
  have h1 := dr_range (x + y) hxy_pos.
  have h2 := dr_range (dr x + dr y) hdxy_pos.
  have hcong1 := dr_cong9 (x + y) hxy_pos.
  have hcong2 := dr_cong9 (dr x + dr y) hdxy_pos.
  have hcongx := dr_cong9 x hx.
  have hcongsy := dr_cong9 y hy.
  smt().
qed.

lemma dr_step_9_invariant (n : int) :
  171 < n => dr (n - 171) = dr n.
proof.
  move=> hn.
  have hpos : 0 < n - 171 by smt().
  have hpos_n : 0 < n by smt().
  have hcong : (n - 171 - 1) %% 9 = (n - 1) %% 9.
    have ->: n - 171 - 1 = (n - 1) - 9 * 19 by ring.
    smt(modzDl modzNm modzMl).
  rewrite /dr.
  have h1 : ! (n - 171 <= 0) by smt().
  have h2 : ! (n <= 0) by smt().
  rewrite h1 h2 /=.
  smt().
qed.

lemma dr_step_9_chain (Bp k : int) :
  171 < Bp - 19 * k =>
  dr (Bp - 19 * (k + 9)) = dr (Bp - 19 * k).
proof.
  move=> hpos.
  have ->: Bp - 19 * (k + 9) = (Bp - 19 * k) - 171 by ring.
  by apply dr_step_9_invariant.
qed.

lemma dr_zero : dr 0 = 0.
proof. by rewrite /dr /=. qed.

lemma dr_nonpos (n : int) : n <= 0 => dr n = 0.
proof.
  move=> hn.
  rewrite /dr.
  have h : n <= 0 by smt().
  by rewrite h.
qed.

(* ================================================================= *)
(* Section 2: Time constants and fractal sampling                     *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* Abstract time model                                                *)
(* ----------------------------------------------------------------- *)

op step_to_time : int -> real.

axiom step_time_monotonic : forall (s1 s2 : int),
  s1 <= s2 => step_to_time s1 <= step_to_time s2.

axiom step_time_pos : forall (s : int),
  0 < s => 0%r < step_to_time s.

op TIMEOUT_THRESHOLD : real.

(* ----------------------------------------------------------------- *)
(* Step counts                                                        *)
(*                                                                    *)
(* These are abstract constants used in the temporal barrier.         *)
(* Their concrete values depend on the implementation and are not     *)
(* relevant to the correctness proof.                                 *)
(* ----------------------------------------------------------------- *)

op step_eea_particular : int.
op step_bounds : int.
op step_triangle_shift : int.
op step_sample_fractal : int.

axiom step_eea_particular_pos : 0 < step_eea_particular.
axiom step_bounds_pos : 0 < step_bounds.
axiom step_triangle_shift_pos : 0 < step_triangle_shift.
axiom step_sample_fractal_pos : 0 < step_sample_fractal.

op total_steps (N : int) : int =
  step_eea_particular + step_bounds + step_triangle_shift + step_sample_fractal.

lemma total_steps_const (N1 N2 : int) :
  total_steps N1 = total_steps N2.
proof.
  by rewrite /total_steps.
qed.

lemma total_steps_pos (N : int) :
  0 < total_steps N.
proof.
  rewrite /total_steps.
  have h1 := step_eea_particular_pos.
  have h2 := step_bounds_pos.
  have h3 := step_triangle_shift_pos.
  have h4 := step_sample_fractal_pos.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Fractal set                                                        *)
(*                                                                    *)
(* The fractal set contains all integers k in [first_k, k_max]        *)
(* such that (k - first_k) is divisible by 9.                         *)
(* ----------------------------------------------------------------- *)

op fractal_set (first_k k_max : int) : int fset =
  fset_filter (fun k => (k - first_k) %% 9 = 0)
              (FSet.oflist (range first_k (k_max + 1))).

op duniform_fractal (first_k k_max : int) : int distr =
  duniform (FSet.elems (fractal_set first_k k_max)).

(* ----------------------------------------------------------------- *)
(* Fractal-set properties                                             *)
(* ----------------------------------------------------------------- *)

lemma fractal_mem_iff (first_k k_max k : int) :
  k \in fractal_set first_k k_max <=>
  (first_k <= k /\ k <= k_max /\ (k - first_k) %% 9 = 0).
proof.
  rewrite /fractal_set mem_filter mem_oflist mem_range.
  smt().
qed.

lemma fractal_first_k_mem (first_k k_max : int) :
  first_k <= k_max =>
  first_k \in fractal_set first_k k_max.
proof.
  move=> hle.
  rewrite fractal_mem_iff.
  split; first by smt().
  split; first by smt().
  by rewrite subzz modz0.
qed.

lemma fractal_nonempty (first_k k_max : int) :
  first_k <= k_max =>
  1 <= FSet.card (fractal_set first_k k_max).
proof.
  move=> hle.
  have hmem := fractal_first_k_mem first_k k_max hle.
  have hcard := FSet.card_gt0 (fractal_set first_k k_max).
  smt().
qed.

lemma fractal_bounded (first_k k_max k : int) :
  k \in fractal_set first_k k_max =>
  first_k <= k /\ k <= k_max.
proof.
  move=> hmem.
  rewrite fractal_mem_iff in hmem.
  smt().
qed.

lemma fractal_congruent (first_k k_max k : int) :
  k \in fractal_set first_k k_max =>
  (k - first_k) %% 9 = 0.
proof.
  move=> hmem.
  rewrite fractal_mem_iff in hmem.
  smt().
qed.
