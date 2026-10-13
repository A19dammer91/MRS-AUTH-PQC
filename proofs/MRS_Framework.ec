(* ================================================================= *)
(*  MRS_Framework.ec                                                  *)
(*  General framework for linear Diophantine representation systems   *)
(*  N = p*A + q*B, with p = 1 (mod q), p > q                          *)
(*                                                                    *)
(*  Primary instance: (p, q) = (19, 9)                                *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(*                                                                    *)
(*  Naming convention:                                                *)
(*    - The digital root in {1, ..., q} is `dr_q q N`.                *)
(*    - The ordinary residue in {0, ..., q-1} is `residue_q q N`.     *)
(*    - `Astart q N` is the smallest positive representative of N      *)
(*      modulo q (the "anchor").                                      *)
(*    - `A0 q N` is the ordinary residue N mod q.                     *)
(*                                                                    *)
(*  Proof strategy:                                                   *)
(*    - Fragile `rewrite` / `smt()` patterns expanded.                 *)
(*    - Modular arithmetic uses `modzMDl` / `modzMl` / `modzMr`.     *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* ================================================================= *)
(* Section 1: Digital root and modular residue                        *)
(* ================================================================= *)

(* Digital root in the range 1,...,q, for positive N and q.           *)
op dr_q (q N : int) : int =
  1 + ((N - 1) %% q).

(* Ordinary modular residue: always in the range 0,...,q-1.           *)
op residue_q (q N : int) : int =
  N %% q.

(* The digital root for the primary modulus 9.                        *)
op dr_9 (N : int) : int =
  dr_q 9 N.

(* ================================================================= *)
(* Section 2: First required value and representation                 *)
(* ================================================================= *)

(* A0 is the ordinary modular residue.                                *)
op A0 (q N : int) : int =
  N %% q.

(* Astart is the smallest positive representative of the residue      *)
(* class of N modulo q. Under the Positive Anchor Convention, this    *)
(* equals dr_q q N.                                                   *)
op Astart (q N : int) : int =
  dr_q q N.

(* A representation of N by p*A + q*B, with A >= 1 and B >= 0.        *)
pred is_rep (p q N A B : int) =
  1 <= A /\
  0 <= B /\
  p * A + q * B = N.

(* A candidate A-value for the system p*A + q*B = N.                  *)
pred is_valid_A (p q N A : int) =
  1 <= A /\
  p * A <= N /\
  (N - p * A) %% q = 0.

(* ================================================================= *)
(* Section 3: Basic modular properties                                *)
(* ================================================================= *)

lemma residue_q_def (q N : int) :
  residue_q q N = N %% q.
proof. by rewrite /residue_q. qed.

lemma A0_def (q N : int) :
  A0 q N = N %% q.
proof. by rewrite /A0. qed.

lemma dr_9_def (N : int) :
  dr_9 N = dr_q 9 N.
proof. by rewrite /dr_9. qed.

(* The digital root is congruent to N modulo q.                       *)
lemma dr_q_cong (q N : int) :
  0 < q =>
  0 < N =>
  (dr_q q N - N) %% q = 0.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hNdiv : N = (N %/ q) * q + N %% q by smt(divz_eq).
  case (N %% q = 0) => [hzero | hnonzero].
  - (* Case N ≡ 0 (mod q) *)
    have hprev : (N - 1) %% q = q - 1.
      have hN_eq : N = (N %/ q) * q by smt().
      have hdecomp : N - 1 = (N %/ q - 1) * q + (q - 1) by smt().
      rewrite hdecomp.
      have hmod : ((N %/ q - 1) * q + (q - 1)) %% q = (q - 1) %% q.
        by apply modzMDl.
      rewrite hmod.
      have hrange : 0 <= q - 1 < q by smt().
      by smt().
    rewrite hprev.
    have hN_eq : N = (N %/ q) * q by smt().
    rewrite hN_eq.
    have hfac : 1 + (q - 1) - (N %/ q) * q = (1 - N %/ q) * q by ring.
    rewrite hfac; by apply modzMl.
  - (* Case N ≢ 0 (mod q) *)
    have hprev : (N - 1) %% q = N %% q - 1.
      have hdecomp : N - 1 = (N %/ q) * q + (N %% q - 1) by smt().
      rewrite hdecomp.
      have hmod : ((N %/ q) * q + (N %% q - 1)) %% q = (N %% q - 1) %% q.
        by apply modzMDl.
      rewrite hmod.
      have hrange : 0 <= N %% q - 1 < q by smt().
      by smt().
    rewrite hprev.
    have hrearrange : 1 + (N %% q - 1) - N = -((N %/ q) * q)
      by smt(divz_eq).
    rewrite hrearrange.
    have hfac : -((N %/ q) * q) = (- (N %/ q)) * q by ring.
    rewrite hfac; by apply modzMl.
qed.

(* Specialization to the modulus 9.                                   *)
lemma dr_9_cong (N : int) :
  0 < N =>
  (dr_9 N - N) %% 9 = 0.
proof.
  move=> hN.
  have hq : 0 < 9 by trivial.
  have h := dr_q_cong 9 N hq hN.
  by rewrite /dr_9.
qed.

(* The digital root lies between 1 and q.                             *)
lemma dr_q_range (q N : int) :
  0 < q =>
  0 < N =>
  1 <= dr_q q N /\ dr_q q N <= q.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hmod : 0 <= (N - 1) %% q < q by smt(divz_eq).
  split; smt().
qed.

(* For modulus 9, the digital root lies between 1 and 9.              *)
lemma dr_9_range (N : int) :
  0 < N =>
  1 <= dr_9 N /\ dr_9 N <= 9.
proof.
  move=> hN.
  have hq : 0 < 9 by trivial.
  have h := dr_q_range 9 N hq hN.
  by rewrite /dr_9.
qed.

(* The ordinary residue is zero exactly when q divides N.             *)
lemma residue_zero_iff (q N : int) :
  0 < q =>
  (N %% q = 0 <=> exists k, N = k * q).
proof.
  move=> hq.
  by smt(divz_eq).
qed.

(* ================================================================= *)
(* Section 4: Digital root versus ordinary residue                    *)
(* ================================================================= *)

lemma dr_q_residue_cases (q N : int) :
  0 < q =>
  0 < N =>
  (N %% q <> 0 => dr_q q N = N %% q) /\
  (N %% q = 0 => dr_q q N = q).
proof.
  move=> hq hN.
  rewrite /dr_q.
  split.
  - move=> hrem.
    have h : (N - 1) %% q = N %% q - 1 by smt(divz_eq).
    by rewrite h; ring.
  - move=> hrem.
    have h : (N - 1) %% q = q - 1 by smt(divz_eq).
    by rewrite h; ring.
qed.

(* ================================================================= *)
(* Section 5: Representation identities                               *)
(* ================================================================= *)

lemma is_rep_equation (p q N A B : int) :
  is_rep p q N A B =>
  p * A + q * B = N.
proof.
  by rewrite /is_rep => -[_ [_ ->]].
qed.

lemma is_rep_bounds (p q N A B : int) :
  is_rep p q N A B =>
  1 <= A /\ 0 <= B.
proof.
  by rewrite /is_rep => -[-> [-> _]].
qed.

lemma is_rep_implies_valid_A (p q N A B : int) :
  0 < q =>
  p * A + q * B = N =>
  1 <= A =>
  0 <= B =>
  is_valid_A p q N A.
proof.
  move=> hq hEq hA hB.
  rewrite /is_valid_A.
  split; first by exact hA.
  split.
  - (* p * A <= N *)
    have : p * A <= p * A + q * B by smt().
    by rewrite -hEq.
  - (* (N - p * A) %% q = 0 *)
    have -> : N - p * A = q * B by rewrite -hEq; ring.
    by apply modzMr.
qed.

(* The B-coordinate corresponding to a valid A.                       *)
op B_from_A (p q N A : int) : int =
  (N - p * A) %/ q.

lemma B_from_A_equation (p q N A : int) :
  0 < q =>
  is_valid_A p q N A =>
  p * A + q * B_from_A p q N A = N.
proof.
  move=> hq.
  rewrite /is_valid_A /B_from_A.
  move=> [hA [hbound hmod]].
  (* hmod : (N - p*A) %% q = 0
     ⇒ N - p*A = q * ((N - p*A) %/ q) *)
  have heq : N - p * A = q * ((N - p * A) %/ q)
    by smt(divz_eq).
  by rewrite -heq; ring.
qed.

lemma is_valid_A_gives_rep (p q N A : int) :
  0 < q =>
  is_valid_A p q N A =>
  0 <= B_from_A p q N A =>
  is_rep p q N A (B_from_A p q N A).
proof.
  move=> hq hvalid hB.
  rewrite /is_rep.
  split.
  - rewrite /is_valid_A in hvalid; smt().
  split; first by exact hB.
  exact (B_from_A_equation p q N A hq hvalid).
qed.

(* ================================================================= *)
(* Section 6: The primary (19, 9) system                              *)
(* ================================================================= *)

op p19 : int = 19.
op q9  : int = 9.

pred is_rep_19_9 (N A B : int) =
  is_rep 19 9 N A B.

op A0_19_9 (N : int) : int =
  A0 9 N.

op Astart_19_9 (N : int) : int =
  dr_q 9 N.

op B_19_9 (N A : int) : int =
  B_from_A 19 9 N A.

lemma dr_19_9_cong (N : int) :
  0 < N =>
  (Astart_19_9 N - N) %% 9 = 0.
proof.
  move=> hN.
  rewrite /Astart_19_9.
  have hq : 0 < 9 by trivial.
  exact (dr_q_cong 9 N hq hN).
qed.

lemma A0_19_9_def (N : int) :
  A0_19_9 N = N %% 9.
proof. by rewrite /A0_19_9 /A0. qed.

lemma Astart_19_9_range (N : int) :
  0 < N =>
  1 <= Astart_19_9 N /\ Astart_19_9 N <= 9.
proof.
  move=> hN.
  rewrite /Astart_19_9.
  have hq : 0 < 9 by trivial.
  exact (dr_q_range 9 N hq hN).
qed.

lemma rep_19_9_equation (N A B : int) :
  is_rep_19_9 N A B =>
  19 * A + 9 * B = N.
proof.
  by rewrite /is_rep_19_9 /is_rep => -[_ [_ ->]].
qed.

(* ================================================================= *)
(* Section 7: Representation count formula                            *)
(* ================================================================= *)

op R_19_9 (N : int) : int =
  ((N %/ 19 - dr_q 9 N) %/ 9) + 1.

lemma A_upper_bound_19_9 (N A B : int) :
  is_rep_19_9 N A B =>
  19 * A <= N.
proof.
  rewrite /is_rep_19_9 /is_rep.
  move=> [_ [hB hEq]].
  have : 19 * A <= 19 * A + 9 * B by smt().
  by rewrite -hEq.
qed.

lemma rep_19_9_congruence (N A B : int) :
  is_rep_19_9 N A B =>
  (A - N) %% 9 = 0.
proof.
  rewrite /is_rep_19_9 /is_rep.
  move=> [hA [hB hEq]].
  have h19 : 19 %% 9 = 1 by trivial.
  have hmod9 : (19 * A) %% 9 = A %% 9.
    have -> : 19 = 2 * 9 + 1 by trivial.
    have -> : (2 * 9 + 1) * A = (2 * A) * 9 + A by ring.
    by rewrite (modzMDl (2 * A) A 9).
  have h9B : (9 * B) %% 9 = 0 by apply modzMr.
  have hNmod : N %% 9 = A %% 9.
    rewrite -hEq.
    have -> : (19 * A + 9 * B) %% 9 = ((19 * A) %% 9 + (9 * B) %% 9) %% 9
      by smt(modzDml).
    rewrite hmod9 h9B.
    by smt().
  have : (A - N) %% 9 = 0 by smt().
  done.
qed.

(* ================================================================= *)
(* Section 8: Numerical checks                                        *)
(* ================================================================= *)

lemma dr_9_1991 :
  dr_9 1991 = 2.
proof.
  rewrite /dr_9 /dr_q.
  by trivial.
qed.

lemma residue_9_1991 :
  A0 9 1991 = 2.
proof.
  rewrite /A0.
  by trivial.
qed.

lemma dr_9_958 :
  dr_9 958 = 4.
proof.
  rewrite /dr_9 /dr_q.
  by trivial.
qed.

lemma rep_958_4_98 :
  is_rep_19_9 958 4 98.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

lemma rep_958_13_79 :
  is_rep_19_9 958 13 79.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

lemma rep_958_22_60 :
  is_rep_19_9 958 22 60.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

lemma rep_958_31_41 :
  is_rep_19_9 958 31 41.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

lemma rep_958_40_22 :
  is_rep_19_9 958 40 22.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

lemma rep_958_49_3 :
  is_rep_19_9 958 49 3.
proof.
  rewrite /is_rep_19_9 /is_rep.
  by trivial.
qed.

(* ================================================================= *)
(* End of MRS_Framework.ec                                            *)
(* ================================================================= *)
