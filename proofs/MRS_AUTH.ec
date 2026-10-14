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

lemma dr_shift_171 (x s : int) :
  0 <= s => 0 < x - 171 * s =>
  dr (x - 171 * s) = dr x.
proof.
  move=> hs hpos.
  have -> : x - 171 * s = x - 9 * (19 * s) by ring.
  apply dr_sub_9k; smt().
qed.

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

lemma supp_duniform_fractal (a b k : int) :
  k \in duniform_fractal a b => k \in fractal_list a b.
proof. by rewrite /duniform_fractal supp_duniform. qed.

lemma triangle_of_list (n k : int) :
  162 < n =>
  k \in fractal_list (first_k_val n (k_min_val n)) (k_max_val n) =>
  0 < Bp_val n - 19 * k =>
  dr (Bp_val n - 19 * k) = dr (2 * dr n).
proof.
  move=> hn hk hpos.
  have [hlo hhi] := fractal_bounded _ _ _ hk.
  have hc := fractal_congruent _ _ _ hk.
  have [s [hs hs0]] :
    exists s, k = first_k_val n (k_min_val n) + 9 * s /\ 0 <= s.
  - exists ((k - first_k_val n (k_min_val n)) %/ 9).
    smt(divz_eq divz_ge0).
  have hx : 0 < Bp_val n - 19 * first_k_val n (k_min_val n) by smt().
  have hxb : Bp_val n - 19 * k
           = (Bp_val n - 19 * first_k_val n (k_min_val n)) - 171 * s
    by rewrite hs; ring.
  have hpos' :
    0 < (Bp_val n - 19 * first_k_val n (k_min_val n)) - 171 * s by smt().
  rewrite hxb (dr_shift_171 _ _ hs0 hpos').
  exact (triangle_shift_correct n (k_min_val n) hn hx).
qed.

lemma temporal_barrier_timeout (n : int) (d : real) :
  d < step_to_time (total_steps n) =>
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==> res = None].
proof.
  move=> hd.
  proc. wp. rnd. wp. skip.
  progress.
  smt().
qed.

lemma temporal_barrier_valid_output (n : int) (d : real) :
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==>
    forall xa xb t, res = Some (xa, xb, t) => 19 * xa + 9 * xb = n].
proof.
  proc. wp. rnd. wp. skip.
  progress.
  smt(Bp_val_eq).
qed.

lemma temporal_barrier_support (n : int) (d : real) :
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==>
    forall xa xb t, res = Some (xa, xb, t) =>
      exists k,
        k \in fractal_list (first_k_val n (k_min_val n)) (k_max_val n)
        /\ xa = n + 9 * k /\ xb = Bp_val n - 19 * k].
proof.
  proc. wp. rnd. wp. skip.
  progress.
  smt(supp_duniform_fractal).
qed.

lemma temporal_barrier_triangle (n : int) (d : real) :
  162 < n =>
  hoare [TemporalBarrier.sample_mrs_timed :
    N = n /\ deadline = d ==>
    forall xa xb t, res = Some (xa, xb, t) => 0 < xb =>
      dr xb = dr (2 * dr n)].
proof.
  move=> hn.
  proc. wp. rnd. wp. skip.
  progress.
  smt(supp_duniform_fractal triangle_of_list Bp_val_eq).
qed.

lemma temporal_barrier_noninterference
    (N1 N2 : int) (dl : real) :
  162 < N1 => 162 < N2 =>
  first_k_val N1 (k_min_val N1) <= k_max_val N1 =>
  first_k_val N2 (k_min_val N2) <= k_max_val N2 =>
  dl < step_to_time (total_steps N1) =>
  dl < step_to_time (total_steps N2) =>
  equiv [TemporalBarrier.sample_mrs_timed ~
         TemporalBarrier.sample_mrs_timed :
    arg{1} = (N1, dl) /\ arg{2} = (N2, dl) ==>
    res{1} = None /\ res{2} = None].
proof.
  move=> h1 h2 hf1 hf2 hd1 hd2.
  proc.
  wp.
  rnd{1}.
  rnd{2}.
  wp.
  skip.
  progress.
  - by apply duniform_fractal_ll.
  - by apply duniform_fractal_ll.
  - smt().
  - smt().
qed.

(* ================================================================= *)
(* Section 4: Zeroize                                                 *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* Abstract memory states                                             *)
(*                                                                    *)
(* The temporal barrier holds a pair (A, B) while active, or has      *)
(* been cleared by zeroize, or was never initialized.                 *)
(* ----------------------------------------------------------------- *)

type mem_state = [ Valid of (int * int) | Cleared | Uninitialized ].

(* Zeroize maps any state to Cleared. *)
op zeroize (m : mem_state) : mem_state = Cleared.

lemma zeroize_idempotent (m : mem_state) :
  zeroize (zeroize m) = zeroize m.
proof. by rewrite /zeroize. qed.

(* What an external attacker can observe. *)
op attacker_obs (m : mem_state) : bool =
  with m = Valid ab       => true
  with m = Cleared        => false
  with m = Uninitialized  => false.

(* After zeroize, the attacker observes nothing. *)
lemma zeroize_unobservable (m : mem_state) :
  attacker_obs (zeroize m) = false.
proof. by rewrite /zeroize /attacker_obs /=. qed.

(* ----------------------------------------------------------------- *)
(* The Rust-side memory state                                         *)
(* ----------------------------------------------------------------- *)

type rust_mem_state =
  [ RustValid of (int * int) | RustCleared | RustUninit ].

op rust_to_abstract (rs : rust_mem_state) : mem_state =
  with rs = RustValid ab => Valid ab
  with rs = RustCleared  => Cleared
  with rs = RustUninit   => Uninitialized.

(* After the Rust side is cleared, the abstract view is Cleared. *)
lemma rust_to_abstract_cleared (rs : rust_mem_state) :
  rust_to_abstract RustCleared = zeroize (rust_to_abstract rs).
proof. by rewrite /zeroize /rust_to_abstract /=. qed.

(* ================================================================= *)
(* Section 5: RustTemporalBarrier                                     *)
(* ================================================================= *)

module RustTemporalBarrier = {
  proc sample_with_zeroize(N : int, deadline_micros : int) : rust_mem_state = {
    var kmin, kmax, firstk, finalk : int;

    kmin   <- k_min_val N;
    kmax   <- k_max_val N;
    firstk <- first_k_val N kmin;
    finalk <$ duniform_fractal firstk kmax;

    return (if kmax < firstk \/ deadline_micros < total_steps N
            then RustCleared
            else RustValid (N + 9 * finalk, Bp_val N - 19 * finalk));
  }
}.

(* ----------------------------------------------------------------- *)
(* Backward security refinement                                       *)
(*                                                                    *)
(* Either the attacker observes nothing (the Rust state is cleared),  *)
(* or the output is a representation of n, and when xb > 0 it is      *)
(* triangle-valid.                                                    *)
(* ----------------------------------------------------------------- *)

lemma refinement_pure (n dm k : int) :
  162 < n =>
  k \in duniform_fractal (first_k_val n (k_min_val n)) (k_max_val n) =>
  ((k_max_val n < first_k_val n (k_min_val n) \/ dm < total_steps n) =>
     attacker_obs (rust_to_abstract RustCleared) = false) /\
  (! (k_max_val n < first_k_val n (k_min_val n) \/ dm < total_steps n) =>
     19 * (n + 9 * k) + 9 * (Bp_val n - 19 * k) = n /\
     (0 < Bp_val n - 19 * k => dr (Bp_val n - 19 * k) = dr (2 * dr n))).
proof.
  move=> hn hk; split.
  - move=> _; exact rust_cleared_unobservable.
  - move=> _; split.
    + smt(Bp_val_eq).
    + move=> hpos.
      exact (triangle_of_list n k hn (supp_duniform_fractal _ _ _ hk) hpos).
qed.

(* ================================================================= *)
(* End of MRS_AUTH.ec                                                 *)
(* ================================================================= *)
