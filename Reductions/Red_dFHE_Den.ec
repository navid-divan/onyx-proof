require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H1_NIZK.
require import H2_dFHE.

module ReduceH1H2_to_dFHE_Den_Vote(A : PCR_REAL_ADV) : DFHE_DEN_ADV = {
  var m_real : dFHE_message
  var m_claim : dFHE_message

  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message = {
    m_real <- witness;
    m_claim <- witness;
    return (m_real, m_claim);
  }

  proc guess(target : dFHE_message, r : dFHE_randomness, c : dFHE_ciphertext) : bool = {
    var b : bool;
    b <- false;
    return b;
  }
}.

module ReduceH1H2_to_dFHE_Den_Cred(A : PCR_REAL_ADV) : DFHE_DEN_ADV = {
  var m_real : dFHE_message
  var m_claim : dFHE_message

  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message = {
    m_real <- witness;
    m_claim <- witness;
    return (m_real, m_claim);
  }

  proc guess(target : dFHE_message, r : dFHE_randomness, c : dFHE_ciphertext) : bool = {
    var b : bool;
    b <- false;
    return b;
  }
}.

lemma red_dfhe_den_advantage_vote (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H1(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H2(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_d)%r * advantage_dFHE_den lambda.
proof.
admit.
qed.
