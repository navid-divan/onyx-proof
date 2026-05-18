require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import NIZK.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H2_dFHE.
require import H3_Ballot.

module ReduceH2H3_to_NIZK_ZK(A : PCR_REAL_ADV) : NIZK_ZK_ADV = {
  var x : nizk_statement
  var w : nizk_witness

  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness = {
    x <- witness;
    w <- witness;
    return (x, w);
  }

  proc distinguish(pi : nizk_proof) : bool = {
    var b : bool;
    b <- false;
    return b;
  }
}.

lemma red_nizk_zk_advantage (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  exists (REAL HYB SIM : real),
    `| Pr[Hybrid_H2(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
     - Pr[Hybrid_H3(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
    <= 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
     + (q_b)%r * advantage_NIZK_zk lambda.
proof.
admit.
qed.
