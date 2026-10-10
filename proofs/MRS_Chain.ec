(* ================================================================= *)
(*  MRS_Chain.ec                                                      *)
(*  Chain construction and verification under the Positive Anchor    *)
(*  Convention (A_0 = dr(N) >= 1, Frobenius boundary 162).           *)
(*                                                                    *)
(*  Module MRSRep (defined in MRS_Core.ec) is used via dot notation   *)
(*  — procedures are called as MRSRep.sample_basic(...) and           *)
(*  MRSRep.sample_triangle(...). There is no `import MRSRep.`         *)
(*  because EasyCrypt modules are not theories and cannot be opened   *)
(*  with `import`. The top-level lemmas sample_basic_correct and      *)
(*  sample_triangle_correct are reachable through `require import     *)
(*  MRS_Core.` alone.                                                 *)
(*                                                                    *)
(*  Ordering convention: all comparisons use the canonical form       *)
(*  `constant < variable` or `constant <= variable`.                  *)
(* ================================================================= *)

require import MRS_Core.

module MRSChain = {
  proc build(N : int, depth : int, tri : int list) : int list = {
    var chain, current, layer, a, b;
    chain   <- [N];
    current <- N;
    layer   <- 0;
    while (layer < depth) {
      if (mem layer tri) {
        (a, b) <@ MRSRep.sample_triangle(current);
      } else {
        (a, b) <@ MRSRep.sample_basic(current);
      }
      chain   <- chain ++ [a; b];
      current <- a;
      layer   <- layer + 1;
    }
    return chain;
  }

  proc verify(chain : int list, tri : int list) : bool = {
    var ok, i, X, a, b;
    ok <- true;
    i  <- 0;
    while (i < size chain - 2) {
      X  <- nth 0 chain i;
      a  <- nth 0 chain (i + 1);
      b  <- nth 0 chain (i + 2);
      ok <- ok && (19 * a + 9 * b = X);
      ok <- ok && (dr a = dr X);
      if (mem (i %/ 2) tri) {
        ok <- ok && (dr b = dr (2 * dr X));
      }
      i <- i + 2;
    }
    return ok;
  }
}.

(* ----------------------------------------------------------------- *)
(* Loop invariant for build                                           *)
(* ----------------------------------------------------------------- *)
pred build_invariant
    (chain : int list) (current : int) (layer depth N : int) (tri : int list) =
  layer <= depth /\
  size chain = 2 * layer + 1 /\
  nth 0 chain 0 = N /\
  current = nth 0 chain (2 * layer) /\
  162 < current /\
  (forall j, 0 <= j < layer =>
     let X = nth 0 chain (2*j)     in
     let A = nth 0 chain (2*j + 1) in
     let B = nth 0 chain (2*j + 2) in
     19*A + 9*B = X /\
     dr A = dr X /\
     (mem j tri => dr B = dr (2 * dr X))).

(* ----------------------------------------------------------------- *)
(* Auxiliary lemmas about lists                                       *)
(* ----------------------------------------------------------------- *)

lemma nth_cat_lo (x : 'a) (s t : 'a list) (i : int) :
  0 <= i < size s => nth x (s ++ t) i = nth x s i.
proof. by move=> hi; rewrite nth_cat hi. qed.

lemma nth_cat_hi (x : 'a) (s t : 'a list) (i : int) :
  size s <= i => nth x (s ++ t) i = nth x t (i - size s).
proof. by move=> hi; rewrite nth_cat; smt(). qed.

lemma size_cat_two (s : int list) (a b : int) :
  size (s ++ [a; b]) = size s + 2.
proof. by rewrite size_cat /=. qed.

(* ----------------------------------------------------------------- *)
(* Correctness of build                                               *)
(* ----------------------------------------------------------------- *)
lemma build_correct (N : int) (depth : int) (tri : int list) :
  162 < N => 0 <= depth =>
  hoare [MRSChain.build :
    arg = (N, depth, tri) ==>
    let chain = res in
    size chain = 2 * depth + 1 /\
    nth 0 chain 0 = N /\
    (forall j, 0 <= j < depth =>
       let X = nth 0 chain (2*j)     in
       let A = nth 0 chain (2*j + 1) in
       let B = nth 0 chain (2*j + 2) in
       19*A + 9*B = X /\
       dr A = dr X /\
       (mem j tri => dr B = dr (2 * dr X)))].
proof.
  move=> hN hd.
  proc.
  while (build_invariant chain current layer depth N tri).

  - move=> &hr.
    rewrite /build_invariant.
    move=> [hlay [hsz [hn0 [hcur [hcurN hforall]]]]].
    case (mem layer{hr} tri{hr}).

    + move=> hmem.
      call (sample_triangle_correct current{hr} hcurN).
      auto => />.
      move=> &m a b res_ok.
      case res_ok.
      * move=> [ha0 hb0].
        exfalso.
        have hk0 := triangle_k0_le_kmax current{hr} hcurN.
        smt().
      * move=> [hlin [hdrA hdrB]].
        rewrite /build_invariant.
        set chain' := chain{hr} ++ [a; b].
        split; first by smt().
        split; first by rewrite size_cat_two; smt().
        split.
        - rewrite /chain' nth_cat_lo /=; smt().
        split.
        - rewrite /chain'.
          rewrite nth_cat_hi; first by smt(size_cat_two).
          simp; smt().
        split; first by smt(dr_rep_A a0_range).
        move=> j hj.
        case (j < layer{hr}).
        - move=> hjl.
          have := hforall j.
          smt(nth_cat_lo size_cat_two).
        - move=> hjge.
          have -> : j = layer{hr} by smt().
          rewrite /chain'.
          rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
          rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
          rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
          simp.
          split.
          + rewrite hlin //.
          split.
          + rewrite hdrA //.
          + move=> _.
            rewrite hdrB //.

    + move=> hnotmem.
      call (sample_basic_correct current{hr} hcurN).
      auto => />.
      move=> &m a b hlin hdrA.
      rewrite /build_invariant.
      set chain' := chain{hr} ++ [a; b].
      split; first by smt().
      split; first by rewrite size_cat_two; smt().
      split.
      - rewrite /chain' nth_cat_lo /=; smt().
      split.
      - rewrite /chain' nth_cat_hi; first by smt(size_cat_two).
        simp; smt().
      split; first by smt(dr_rep_A a0_range).
      move=> j hj.
      case (j < layer{hr}).
      - move=> hjl.
        have := hforall j.
        smt(nth_cat_lo size_cat_two).
      - move=> hjge.
        have -> : j = layer{hr} by smt().
        rewrite /chain'.
        rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
        rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
        rewrite (nth_cat_hi _ chain{hr}); first by smt(size_cat_two).
        simp.
        split.
        + rewrite hlin //.
        split.
        + rewrite hdrA //.
        + move=> hmem. exfalso; smt().

  - auto => />.
    rewrite /build_invariant /=.
    split; first by smt().
    split; first by done.
    split; first by done.
    split; first by done.
    split; first by exact hN.
    by move=> j hj; smt().

  - move=> &m.
    rewrite /build_invariant.
    move=> [hlay [hsz [hn0 [hcur [_ hforall]]]]].
    split.
    + smt().
    split.
    + exact hn0.
    + move=> j hj.
      have := hforall j.
      smt().
qed.

(* ----------------------------------------------------------------- *)
(* Equivalence of build                                               *)
(* ----------------------------------------------------------------- *)
lemma build_equiv (N : int) (depth : int) (tri : int list) :
  162 < N =>
  equiv [MRSChain.build ~ MRSChain.build :
    ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  while (={layer, chain, current, depth, tri}).
  - seq 1 1 : (={layer, chain, current, depth, tri, a, b}).
    + if => />.
      * call (sample_triangle_equiv current{1} hN).
        auto.
      * call (sample_basic_equiv current{1} hN).
        auto.
    + auto.
  - auto.
qed.
