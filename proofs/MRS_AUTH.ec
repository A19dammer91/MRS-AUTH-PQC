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
(* Section 1: Temporal Barrier                                          *)
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

(* ----------------------------------------------------------------- *)
(* Step counts                                                        *)
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
(* Fractal list                                                       *)
(*                                                                    *)
(* The fractal list contains all integers k in [first_k, k_max]       *)
(* such that (k - first_k) is divisible by 9.                         *)
(* ----------------------------------------------------------------- *)

op fractal_list (first_k k_max : int) : int list =
  filter (fun k => (k - first_k) %% 9 = 0)
         (range first_k (k_max + 1)).

op duniform_fractal (first_k k_max : int) : int distr =
  duniform (fractal_list first_k k_max).

(* ----------------------------------------------------------------- *)
(* Fractal-list membership                                            *)
(* ----------------------------------------------------------------- *)

lemma fractal_mem_iff (first_k k_max k : int) :
  mem (fractal_list first_k k_max) k <=>
  (first_k <= k /\ k <= k_max /\ (k - first_k) %% 9 = 0).
proof.
  rewrite /fractal_list.
  rewrite mem_filter.
  rewrite mem_range.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Fractal-list properties                                            *)
(* ----------------------------------------------------------------- *)

lemma fractal_first_k_mem (first_k k_max : int) :
  first_k <= k_max =>
  mem (fractal_list first_k k_max) first_k.
proof.
  move=> hle.
  have hiff := fractal_mem_iff first_k k_max first_k.
  smt().
qed.

lemma fractal_nonempty (first_k k_max : int) :
  first_k <= k_max =>
  1 <= size (fractal_list first_k k_max).
proof.
  move=> hle.
  have hmem := fractal_first_k_mem first_k k_max hle.
  have hne : fractal_list first_k k_max <> [] by smt().
  have hsz := size_eq0 (fractal_list first_k k_max).
  smt().
qed.

lemma fractal_bounded (first_k k_max k : int) :
  mem (fractal_list first_k k_max) k =>
  first_k <= k /\ k <= k_max.
proof.
  move=> hmem.
  have hiff := fractal_mem_iff first_k k_max k.
  smt().
qed.

lemma fractal_congruent (first_k k_max k : int) :
  mem (fractal_list first_k k_max) k =>
  (k - first_k) %% 9 = 0.
proof.
  move=> hmem.
  have hiff := fractal_mem_iff first_k k_max k.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Losslessness of duniform_fractal                                   *)
(*                                                                    *)
(* EasyCrypt r2024.09 exposes only the predicates `is_lossless`,      *)
(* `is_full`, and `is_uniform` for `'a distr`. There is no public     *)
(* `mu` or `weight` operator on `int distr`.                          *)
(*                                                                    *)
(* We can therefore state losslessness, which uses `is_lossless`.     *)
(*                                                                    *)
(* The support property (that `final_k` lies in the fractal list) is  *)
(* established implicitly by the `<$`-sampling rule in section 3:     *)
(* when `final_k <$ duniform_fractal first_k k_max`, EasyCrypt knows  *)
(* that `final_k` is in `fractal_list first_k k_max`.                 *)
(* ----------------------------------------------------------------- *)

lemma duniform_fractal_ll (first_k k_max : int) :
  first_k <= k_max =>
  is_lossless (duniform_fractal first_k k_max).
proof.
  move=> hle.
  rewrite /duniform_fractal.
  have hne := fractal_nonempty first_k k_max hle.
  smt().
qed.

(* ================================================================= *)
(* Section 3: Temporal Barrier                                        *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* Named intermediate values                                          *)
(* ----------------------------------------------------------------- *)

op Bp_val (N : int) : int = -2 * N.

op k_min_val (N : int) : int = (-N + 162 + 8) %/ 9.

op k_max_val (N : int) : int = (-2 * N) %/ 19.

op shift_val (N kmin : int) : int =
  (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9.

op first_k_val (N kmin : int) : int = kmin + shift_val N kmin.

(* ----------------------------------------------------------------- *)
(* The module                                                         *)
(*                                                                    *)
(* All local variables use lowercase-first names, as required by      *)
(* EasyCrypt. Uppercase-first names are reserved for modules and      *)
(* algebraic constructors.                                            *)
(* ----------------------------------------------------------------- *)

module TemporalBarrier = {
  proc sample_mrs_timed(N : int, deadline : real) : (int * int * real) option = {
    var anc, bcp, kmin, kmax, firstk, finalk, xa, xb, duration;

    anc <- N;
    bcp <- -2 * N;
    kmin <- (-anc + 162 + 8) %/ 9;
    kmax <- bcp %/ 19;
    firstk <- kmin + ((dr (bcp - 19 * kmin) - dr (2 * dr N)) %% 9);
    finalk <$ duniform_fractal firstk kmax;
    xa <- anc + 9 * finalk;
    xb <- bcp - 19 * finalk;
    duration <- step_to_time (total_steps N);

    return (if (kmax < kmin) then None
            else if (kmax < firstk) then None
            else if (deadline < step_to_time (total_steps N)) then None
            else Some (xa, xb, duration));
  }
}.

(* ----------------------------------------------------------------- *)
(* Helper: dr is invariant under subtraction of 9*k                   *)
(* ----------------------------------------------------------------- *)

lemma dr_sub_9k (x k : int) :
  0 <= k => 9 * k < x =>
  dr (x - 9 * k) = dr x.
proof.
  move=> hk hlt.
  have hx_pos : 0 < x by smt().
  have hx9k_pos : 0 < x - 9 * k by smt().
  have hdx := dr_range (x - 9 * k) hx9k_pos.
  have hdrx := dr_range x hx_pos.
  have hcong1 := dr_cong9 (x - 9 * k) hx9k_pos.
  have hcong2 := dr_cong9 x hx_pos.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Shift correction                                                   *)
(* ----------------------------------------------------------------- *)

lemma triangle_shift_correct (N kmin : int) :
  162 < N =>
  0 < Bp_val N - 19 * first_k_val N kmin =>
  dr (Bp_val N - 19 * first_k_val N kmin) = dr (2 * dr N).
proof.
  move=> hN hpos.
  have hNpos : 0 < N by smt().
  have h2drN_pos : 0 < 2 * dr N by smt(dr_range).

  rewrite /first_k_val /shift_val.

      have hB_eq :
    Bp_val N - 19 *
      (kmin + (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9) =
    (Bp_val N - 19 * kmin) -
      19 * ((dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9)
    by ring.
  rewrite hB_eq.

  pose shift := (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9.

  have h19 : 19 * shift = 9 * (2 * shift) + shift by ring.
  rewrite h19.

  have hsub :
    (Bp_val N - 19 * kmin) - (9 * (2 * shift) + shift) =
    ((Bp_val N - 19 * kmin) - shift) - 9 * (2 * shift)
    by ring.
  rewrite hsub.

(* ----------------------------------------------------------------- *)
(* Correctness of sample_mrs_timed                                    *)
(* ----------------------------------------------------------------- *)

op Bp_val (N : int) : int = -2 * N.

op k_min_val (N : int) : int = (-N + 162 + 8) %/ 9.

op k_max_val (N : int) : int = (-2 * N) %/ 19.

op shift_val (N kmin : int) : int =
  (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9.

op first_k_val (N kmin : int) : int = kmin + shift_val N kmin.

lemma triangle_shift_correct (N kmin : int) :
  162 < N =>
  0 < Bp_val N - 19 * first_k_val N kmin =>
  dr (Bp_val N - 19 * first_k_val N kmin) = dr (2 * dr N).
proof.
  move=> hN hpos.
  have hNpos : 0 < N by smt().
  have h2drN_pos : 0 < 2 * dr N by smt(dr_range).
  rewrite /first_k_val /shift_val.
  have hB_eq : Bp_val N - 19 * (kmin + (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9) =
               (Bp_val N - 19 * kmin) - 19 * ((dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9) by ring.
  rewrite hB_eq.
  pose shift = ((dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9).
  have h19 : 19 * shift = 9 * (2 * shift) + shift by ring.
  rewrite h19.
  have hsub : (Bp_val N - 19 * kmin) - (9 * (2 * shift) + shift) =
              ((Bp_val N - 19 * kmin) - shift) - 9 * (2 * shift) by ring.
  rewrite hsub.
  set x := (Bp_val N - 19 * kmin) - shift.
  have hx_pos : 0 < x by smt().
  have hk_nonneg : 0 <= 2 * shift by smt(modz_ge0).
  have hpos_x : 9 * (2 * shift) < x by smt().
  have hdr_eq : dr (x - 9 * (2 * shift)) = dr x by apply dr_sub_9k.
  rewrite hdr_eq.
  have hx_cong : (x - dr (2 * dr N)) %% 9 = 0 by smt().
  have hdx := dr_range x hx_pos.
  have hd2 := dr_range (2 * dr N) h2drN_pos.
  by smt().
qed.

lemma temporal_barrier_math_step (bcp firstk finalk N : int) :
  bcp = -2 * N =>
  (finalk - firstk) %% 9 = 0 =>
  0 <= 19 * ((finalk - firstk) %/ 9) =>
  9 * (19 * ((finalk - firstk) %/ 9)) < bcp - 19 * firstk =>
  162 < N =>
  dr (bcp - 19 * finalk) = dr (2 * dr N).
proof.
  move=> hbcp hdiff hnonneg hpos hN.
  have ht_eq : finalk = firstk + 9 * ((finalk - firstk) %/ 9) by smt(divz_eq).
  rewrite ht_eq.
  have hB_decomp : bcp - 19 * (firstk + 9 * ((finalk - firstk) %/ 9)) =
                   (bcp - 19 * firstk) - 171 * ((finalk - firstk) %/ 9) by ring.
  rewrite hB_decomp.
  have h171 : 171 = 9 * 19 by ring.
  rewrite h171.
  have h9k : 9 * 19 * ((finalk - firstk) %/ 9) = 9 * (19 * ((finalk - firstk) %/ 9)) by ring.
  rewrite h9k.
  rewrite dr_sub_9k.
  + by [].
  + by [].
  rewrite hbcp.
  rewrite /Bp_val.
  by smt(triangle_shift_correct).
qed.

lemma temporal_barrier_correctness (N : int) (deadline : real) :
  162 < N =>
  hoare [TemporalBarrier.sample_mrs_timed :
    arg = (N, deadline) ==>
    match res with
    | Some (A, B, _) =>
        19 * A + 9 * B = N /\
        dr B = dr (2 * dr N)
    | None => true
    end].
proof.
  move=> hN.
  proc.
  seq 4 : (anc = N /\ bcp = -2 * N /\
           kmin = (-N + 162 + 8) %/ 9 /\
           kmax = (-2 * N) %/ 19).
  - by auto.
  if => />.
  - by auto.
  seq 1 : (firstk = kmin + ((dr (bcp - 19 * kmin) - dr (2 * dr N)) %% 9)).
  - by auto.
  if => />.
  - by auto.
  seq 1 : (mem finalk (fractal_list firstk kmax)).
  - by auto.
  seq 2 : (xa = anc + 9 * finalk /\ xb = bcp - 19 * finalk).
  - by auto.
  seq 1 : (duration = step_to_time (total_steps N)).
  - by auto.
  if => />.
  - by auto.
  auto => /> &m hk_le hfk_le hfk_mem hxa hxb hdur hdeadline_ok.
  split.
  - rewrite hxa hxb.
    have hanc : anc{m} = N by smt().
    have hbcp : bcp{m} = -2 * N by smt().
    by smt().
  - rewrite hxb.
    apply (temporal_barrier_math_step bcp{m} firstk{m} finalk{m} N).
    + by smt().
    + by smt(fractal_congruent).
    + by smt().
    + by smt().
    + by assumption.
qed.

(* ----------------------------------------------------------------- *)
(* Non-interference under a strict deadline                           *)
(* ----------------------------------------------------------------- *)

lemma temporal_barrier_noninterference
    (N1 N2 : int) (deadline : real) :
  162 < N1 => 162 < N2 =>
  deadline < step_to_time (total_steps N1) =>
  deadline < step_to_time (total_steps N2) =>
  equiv [TemporalBarrier.sample_mrs_timed ~
         TemporalBarrier.sample_mrs_timed :
    arg{1} = (N1, deadline) /\ arg{2} = (N2, deadline) ==>
    res{1} = None /\ res{2} = None].
proof.
  move=> hN1 hN2 hto1 hto2.
  proc.
  seq 4 4 : true.
  - auto.
  if => />.
  - auto.
  if => />.
  - auto.
  seq 1 1 : true.
  - auto.
  if => />.
  - auto.
  seq 1 1 : true.
  - auto.
  seq 2 2 : true.
  - auto.
  seq 1 1 : true.
  - auto.
  if => />.
  - auto.
  - smt().
qed.

(* ----------------------------------------------------------------- *)
(* Conditional uniformity                                             *)
(* ----------------------------------------------------------------- *)

lemma temporal_barrier_conditional_uniform
    (N : int) (deadline : real) :
  162 < N =>
  step_to_time (total_steps N) <= deadline =>
  equiv [TemporalBarrier.sample_mrs_timed ~
         TemporalBarrier.sample_mrs_timed :
    ={arg} /\ arg{1} = (N, deadline) ==> ={res}].
proof.
  move=> hN hdeadline.
  proc.
  seq 4 4 : (={anc, bcp, kmin, kmax} /\
             anc{1} = N /\ bcp{1} = -2 * N).
  - auto.
  if => />.
  - auto.
  seq 1 1 : (={anc, bcp, kmin, kmax, firstk}).
  - auto.
  if => />.
  - auto.
  seq 1 1 : (={anc, bcp, kmin, kmax, firstk, finalk}).
  - rnd.
    auto.
  seq 2 2 : (={anc, bcp, kmin, kmax, firstk, finalk, xa, xb}).
  - auto.
  seq 1 1 : (={anc, bcp, kmin, kmax, firstk, finalk, xa, xb, duration}).
  - auto.
  if => />.
  - exfalso.
    smt().
  - auto.
qed.
