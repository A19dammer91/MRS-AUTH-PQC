(* MRS_Chain.ec *)
require import AllCore Int IntDiv List.
require import MRS_Core.
require import MRS_Distr.
require import MRS_Equiv.

module MRSChain = {
  proc build(N : int, depth : int, tri : int list) : int list = {
    var chain, current, a, b, i;

    chain   <- [N];
    current <- N;
    i       <- 0;

    while (i < depth) {
      if (mem tri i) {
        (a, b) <@ MRSRep.sample_triangle(current);
      } else {
        (a, b) <@ MRSRep.sample_basic(current);
      }

      chain   <- chain ++ [a; b];
      current <- a;
      i       <- i + 1;
    }

    return chain;
  }
}.

lemma build_equiv (N depth : int) (tri : int list) :
  equiv [MRSChain.build ~ MRSChain.build :
    arg{1} = (N, depth, tri) /\
    arg{2} = (N, depth, tri) ==> ={res}].
proof.
  proc.
  while (={i, chain, current, N, depth, tri}).
  - if => //.
    + call (_ : true ==> ={res}).
      auto.
    + call (_ : true ==> ={res}).
      auto.
  - auto.
qed.
