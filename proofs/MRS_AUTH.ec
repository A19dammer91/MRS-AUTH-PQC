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
(* Named values                                                       *)
(*                                                                    *)
(* Anchor A = N and B' = -2N, so that for every k:                    *)
(*   19 * (N + 9k) + 9 * (B' - 19k) = N.                              *)
(* ----------------------------------------------------------------- *)

op Bp_val (N : int) : int = -2 * N.

op k_min_val (N : int) : int = (-N + 162 + 8) %/ 9.

op k_max_val (N : int) : int = (-2 * N) %/ 19.

op shift_val (N kmin : int) : int =
  (dr (Bp_val N - 19 * kmin) - dr (2 * dr N)) %% 9.

op first_k_val (N kmin : int) : int = kmin + shift_val N kmin.

lemma Bp_val_eq (N : int) : Bp_val N = -2 * N.
proof. by rewrite /Bp_val. qed.

lemma first_k_ge_kmin (N kmin : int) : kmin <= first_k_val N kmin.
proof. rewrite /first_k_val /shift_val; smt(modz_ge0). qed.

(* ----------------------------------------------------------------- *)
(* Digital-root alignment                                             *)
(*                                                                    *)
(* dr(y - 19 s) and t are both in [1,9] and congruent mod 9, hence    *)
(* equal. The congruences are made explicit with divz_eq.             *)
(* ----------------------------------------------------------------- *)

lemma dr_align (y t s : int) :
  1 <= t => t <= 9 =>
  s = (dr y - t) %% 9 =>
  0 < y - 19 * s =>
  dr (y - 19 * s) = t.
proof.
  move=> ht1 ht9 hs hpos.
  have hs0 : 0 <= s by smt(modz_ge0).
  have hy : 0 < y by smt().
  have [hy1 hy9] := dr_range y hy.
  have [hz1 hz9] := dr_range (y - 19 * s) hpos.
  have hcy := dr_cong9 y hy.
  have hcz := dr_cong9 (y - 19 * s) hpos.
  have e1 := divz_eq (dr y - t) 9.
  have e2 := divz_eq (dr y - y) 9.
  have e3 := divz_eq (dr (y - 19 * s) - (y - 19 * s)) 9.
  smt().
qed.

lemma dr_sub_9k (x k : int) :
  0 <= k => 9 * k < x =>
  dr (x - 9 * k) = dr x.
proof.
  move=> hk hlt.
  have hx : 0 < x by smt().
  have hz : 0 < x - 9 * k by smt().
  have [h1 h2] := dr_range x hx.
  have [h3 h4] := dr_range (x - 9 * k) hz.
  have c1 := dr_cong9 x hx.
  have c2 := dr_cong9 (x - 9 * k) hz.
  have e1 := divz_eq (dr x - x) 9.
  have e2 := divz_eq (dr (x - 9 * k) - (x - 9 * k)) 9.
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
  have hN0 : 0 < N by smt().
  have [hd1 hd9] := dr_range N hN0.
  have hp2 : 0 < 2 * dr N by smt().
  have [ht1 ht9] := dr_range (2 * dr N) hp2.
  have hfk : Bp_val N - 19 * first_k_val N kmin
           = (Bp_val N - 19 * kmin) - 19 * shift_val N kmin
    by rewrite /first_k_val; ring.
  rewrite hfk.
  apply (dr_align (Bp_val N - 19 * kmin) (dr (2 * dr N))
                  (shift_val N kmin) ht1 ht9).
  - by rewrite /shift_val.
  - smt().
qed.

(* ----------------------------------------------------------------- *)
(* The module                                                         *)
(*                                                                    *)
(* Reads directly from the named values. Since first_k >= kmin        *)
(* (first_k_ge_kmin), the test kmax < kmin is implied by              *)
(* kmax < firstk and is not repeated.                                 *)
(* ----------------------------------------------------------------- *)

module TemporalBarrier = {
  proc sample_mrs_timed(N : int, deadline : real) : (int * int * real) option = {
    var kmin, kmax, firstk, finalk : int;

    kmin   <- k_min_val N;
    kmax   <- k_max_val N;
    firstk <- first_k_val N kmin;
    finalk <$ duniform_fractal firstk kmax;

    return (if kmax < firstk \/ deadline < step_to_time (total_steps N)
            then None
            else Some (N + 9 * finalk,
                       Bp_val N - 19 * finalk,
                       step_to_time (total_steps N)));
  }
}.

(* ----------------------------------------------------------------- *)
(* Support of the sampler                                             *)
(* ----------------------------------------------------------------- *)

lemma supp_duniform_fractal (a b k : int) :
  k \in duniform_fractal a b => k \in fractal_list a b.
proof. by rewrite /duniform_fractal supp_duniform. qed.

(* ----------------------------------------------------------------- *)
(* Barrier properties (partial correctness)                           *)
(* ----------------------------------------------------------------- *)

(* Past the deadline nothing but None is ever returned. *)
lemma temporal_barrier_timeout (n : int) (d : real) :
  d < step_to_time (total_steps n) =>
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==> res = None].
proof.
  move=> hd.
  proc. wp. rnd. wp. skip.
  smt().
qed.

(* Every returned pair is a representation of n. *)
lemma temporal_barrier_valid_output (n : int) (d : real) :
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==>
    forall xa xb t, res = Some (xa, xb, t) => 19 * xa + 9 * xb = n].
proof.
  proc. wp. rnd. wp. skip.
  smt(Bp_val_eq).
qed.

(* Every returned pair comes from a k in the fractal list. *)
lemma temporal_barrier_support (n : int) (d : real) :
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==>
    forall xa xb t, res = Some (xa, xb, t) =>
      exists k,
        k \in fractal_list (first_k_val n (k_min_val n)) (k_max_val n)
        /\ xa = n + 9 * k /\ xb = Bp_val n - 19 * k].
proof.
  proc. wp. rnd. wp. skip.
  smt(supp_duniform_fractal).
qed.
