require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G5_NIZK_ZK.
require import G6_dFHE_CPA.

module B_C(A : PCR_REAL_ADV) : DFHE_INDCPA_ADV = {
  var stored_pk : dFHE_pkey
  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message = {
    stored_pk <- pk;
    return (0, 0);
  }
  proc guess(c : dFHE_ciphertext) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_dFHE_CPA_correctness (A <: PCR_REAL_ADV {-B_C}) &m lambda nT t nV nA nC :
  `| Pr[G5_NIZK_ZK(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G6_dFHE_CPA(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_b)%r * `| Pr[DFHE_INDCPA_Game(B_C(A)).main() @ &m : res] - 1%r / 2%r |.
