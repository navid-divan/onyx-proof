require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H2_dFHE.
require import H3_Ballot.

module ReduceH2H3_to_dFHE_INDCPA(A : PCR_REAL_ADV) : DFHE_INDCPA_ADV = {
  var m0 : dFHE_message
  var m1 : dFHE_message

  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message = {
    m0 <- witness;
    m1 <- witness;
    return (m0, m1);
  }

  proc guess(c : dFHE_ciphertext) : bool = {
    var b : bool;
    b <- false;
    return b;
  }
}.

lemma red_dfhe_indcpa_advantage (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H2(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H3(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
   + (q_b)%r * advantage_NIZK_zk lambda.
proof.
admit.
qed.
