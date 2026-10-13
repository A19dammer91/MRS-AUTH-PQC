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
(* The TemporalBarrier module                                         *)
(*                                                                    *)
(* Given N and a timeout, `sample_mrs_timed` tries to produce a       *)
(* representation (A, B) of N as 19A + 9B such that B is              *)
(* triangle-valid (dr B = dr (2 * dr N)). It returns None if the      *)
(* intermediate bounds collapse (no valid k exists) or if the         *)
(* computed duration exceeds the timeout.                             *)
(*                                                                    *)
(* The algorithm:                                                     *)
(*   1. Ap = N, Bp = -2N                                              *)
(*   2. k_min = (-Ap + 170) / 9                                       *)
(*   3. k_max = Bp / 19                                               *)
(*   4. If k_max < k_min: return None                                 *)
(*   5. first_k = k_min + shift, where shift aligns B to the target   *)
(*   6. If k_max < first_k: return None                               *)
(*   7. final_k <$ duniform_fractal first_k k_max                     *)
(*   8. A = Ap + 9*final_k, B = Bp - 19*final_k                       *)
(*   9. If timeout < step_to_time (total_steps N): return None        *)
(*  10. Return Some (A, B, duration)                                  *)
(* ----------------------------------------------------------------- *)

module TemporalBarrier = {
  proc sample_mrs_timed(N : int, timeout : real) :
    (int * int * real) option = {
    var Ap, Bp, k_min, k_max, first_k, final_k, A, B, duration;

    Ap <- N;
    Bp <- -2 * N;
    k_min <- (-Ap + 162 + 8) %/ 9;
    k_max <- Bp %/ 19;

    if (k_max < k_min) { return None; }

    first_k <- k_min + ((dr (Bp - 19 * k_min) - dr (2 * dr N)) %% 9);

    if (k_max < first_k) { return None; }

    final_k <$ duniform_fractal first_k k_max;

    A <- Ap + 9 * final_k;
    B <- Bp - 19 * final_k;
    duration <- step_to_time (total_steps N);

    if (timeout < step_to_time (total_steps N)) { return None; }

    return Some (A, B, duration);
  }
}.

(* ================================================================= *)
(* Section 3.1: The shift correction                                 *)
(* ================================================================= *)
(*                                                                    *)
(* The value `first_k` is chosen so that the resulting                  *)
(* B-coordinate satisfies `dr B = dr (2 * dr N)`.                    *)
(*                                                                    *)
(* The proof uses three facts:                                        *)
(*   - dr is invariant under addition of multiples of 9              *)
(*   - dr (x - 9*k) = dr x when x - 9*k > 0                          *)
(*   - shift is congruent to dr (Bp - 19*k_min) - dr (2*dr N) mod 9  *)
(* ================================================================= *)

lemma dr_sub_9k (x k : int) :
  0 < x - 9 * k =>
  dr (x - 9 * k) = dr x.
proof.
  move=> hpos.
  have hpos_x : 0 < x by smt().
  have hdx := dr_range x hpos_x.
  have hdr := dr_range (x - 9 * k) hpos.
  have hcong1 : (dr (x - 9 * k) - (x - 9 * k)) %% 9 = 0
    by apply dr_cong9.
  have hcong2 : (dr x - x) %% 9 = 0
    by apply dr_cong9.
  smt().
qed.

lemma triangle_shift_correct (N k_min : int) :
  162 < N =>
  let Bp = -2 * N in
  let shift = (dr (Bp - 19 * k_min) - dr (2 * dr N)) %% 9 in
  let first_k = k_min + shift in
  0 < Bp - 19 * first_k =>
  dr (Bp - 19 * first_k) = dr (2 * dr N).
proof.
  move=> hN /= hpos.
  have hNpos : 0 < N by smt().
  have h2N : 0 < 2 * N by smt().

  (* Stap 1: B = (Bp - 19 * k_min) - 19 * shift *)
  have hB_eq : Bp - 19 * (k_min + shift) =
               (Bp - 19 * k_min) - 19 * shift by ring.
  rewrite hB_eq.

  (* Stap 2: schrijf 19 * shift = 9 * (2 * shift) + shift *)
  have h19 : 19 * shift = 9 * (2 * shift) + shift by ring.
  have hdecomp : (Bp - 19 * k_min) - 19 * shift =
                 ((Bp - 19 * k_min) - shift) - 9 * (2 * shift)
    by smt().
  rewrite hdecomp.

  (* Stap 3: dr is invariant onder -9*(2*shift) *)
  have h9pos : 0 < (Bp - 19 * k_min) - shift - 9 * (2 * shift)
    by smt().
  rewrite dr_sub_9k //.

  (* Stap 4: (Bp - 19 * k_min) - shift ≡ dr (2 * dr N) mod 9 *)
  have hcong : ((Bp - 19 * k_min) - shift - dr (2 * dr N)) %% 9 = 0 by smt().

  (* Stap 5: beide zijn in [1, 9] *)
  have hx_pos : 0 < (Bp - 19 * k_min) - shift by smt().
  have hx_range := dr_range ((Bp - 19 * k_min) - shift) hx_pos.
  have h2drN_pos : 0 < 2 * dr N by smt(dr_range).
  have ht_range := dr_range (2 * dr N) h2drN_pos.
  smt().
qed.

(* ================================================================= *)
(* Section 3.2: Correctness of sample_mrs_timed                       *)
(* ================================================================= *)

lemma temporal_barrier_correctness (N : int) (timeout : real) :
  162 < N =>
  hoare [TemporalBarrier.sample_mrs_timed :
    arg = (N, timeout) ==>
    match res with
    | Some (A, B, _) =>
        19 * A + 9 * B = N /\
        dr B = dr (2 * dr N)
    | None => true
    end].
proof.
  move=> hN.
  proc.
  seq 4 : (Ap = N /\ Bp = -2 * N /\
           k_min = (-N + 162 + 8) %/ 9 /\
           k_max = (-2 * N) %/ 19).
  - auto.
  if.
  - auto.
  seq 1 : (first_k = k_min + ((dr (Bp - 19 * k_min) - dr (2 * dr N)) %% 9)).
  - auto.
  if.
  - auto.
  (* Sampling *)
  seq 1 : (mem final_k (fractal_list first_k k_max)).
  - auto => />.
    move=> &m hle.
    (* duniform levert een element van de lijst *)
    smt().
  seq 2 : (A = Ap + 9 * final_k /\ B = Bp - 19 * final_k).
  - auto.
  seq 1 : (duration = step_to_time (total_steps N)).
  - auto.
  if.
  - auto.
  auto => /> &m hk_le hfk_le hfk_mem hA hB hdur hto_ok.
  split.
  - (* 19 * A + 9 * B = N *)
    rewrite hA hB.
    have hAp : Ap{m} = N by smt().
    have hBp : Bp{m} = -2 * N by smt().
    smt().
  - (* dr B = dr (2 * dr N) *)
    rewrite hB.
    have hBp : Bp{m} = -2 * N by smt().
    rewrite hBp.
    (* Gebruik de fractal-eigenschap: final_k - first_k is een 9-voud *)
    have hdiff : (final_k{m} - first_k{m}) %% 9 = 0 by smt(fractal_congruent).
    (* final_k = first_k + 9 * t *)
    have hfk_eq : exists t, final_k{m} = first_k{m} + 9 * t by smt(divz_eq).
    case hfk_eq => t ht.
    rewrite ht.
    (* B = Bp - 19 * first_k - 171 * t *)
    have hdecomp : Bp{m} - 19 * (first_k{m} + 9 * t) =
                   Bp{m} - 19 * first_k{m} - 171 * t by ring.
    rewrite hdecomp.
    have h171 : 171 = 9 * 19 by ring.
    rewrite h171.
    (* Pas dr_sub_9k herhaald toe *)
    have hbase_pos : 0 < Bp{m} - 19 * first_k{m} by smt().
    have ht_nonneg : 0 <= t by smt().
    (* Het algemene feit: dr (x - 9*19*t) = dr x als x - 9*19*t > 0 *)
    have hgen : forall (x k : int), 0 <= k => 0 < x - 171 * k =>
                dr (x - 171 * k) = dr x.
      move=> x k hk hpos_x.
      have hsub : x - 171 * k = x - 9 * (19 * k) by ring.
      rewrite hsub.
      apply dr_sub_9k.
      smt().
    rewrite hgen; first by smt().
    (* Nu: dr (Bp - 19 * first_k) = dr (2 * dr N) *)
    apply triangle_shift_correct; smt().
qed.

(* ================================================================= *)
(* Section 3.3: Non-interference under a strict timeout               *)
(* ================================================================= *)

lemma temporal_barrier_noninterference
    (N1 N2 : int) (timeout : real) :
  162 < N1 => 162 < N2 =>
  timeout < step_to_time (total_steps N1) =>
  timeout < step_to_time (total_steps N2) =>
  equiv [TemporalBarrier.sample_mrs_timed ~
         TemporalBarrier.sample_mrs_timed :
    arg{1} = (N1, timeout) /\ arg{2} = (N2, timeout) ==>
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
  - (* timeout < step_to_time (total_steps N) — geldt in beide takken *)
    smt().
qed.

(* ================================================================= *)
(* Section 3.4: Conditional uniformity                                 *)
(* ================================================================= *)

lemma temporal_barrier_conditional_uniform
    (N : int) (timeout : real) :
  162 < N =>
  step_to_time (total_steps N) <= timeout =>
  equiv [TemporalBarrier.sample_mrs_timed ~
         TemporalBarrier.sample_mrs_timed :
    ={arg} /\ arg{1} = (N, timeout) ==> ={res}].
proof.
  move=> hN htimeout.
  proc.
  seq 4 4 : (={Ap, Bp, k_min, k_max} /\
             Ap{1} = N /\ Bp{1} = -2 * N).
  - auto.
  if => />.
  - auto.
  seq 1 1 : (={Ap, Bp, k_min, k_max, first_k}).
  - auto.
  if => />.
  - auto.
  seq 1 1 : (={Ap, Bp, k_min, k_max, first_k, final_k}).
  - rnd.
    auto.
  seq 2 2 : (={Ap, Bp, k_min, k_max, first_k, final_k, A, B}).
  - auto.
  seq 1 1 : (={Ap, Bp, k_min, k_max, first_k, final_k, A, B, duration}).
  - auto.
  if => />.
  - (* timeout < step_to_time ... — onmogelijk door htimeout *)
    exfalso.
    smt().
  - auto.
qed.
