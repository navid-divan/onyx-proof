require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G6_dFHE_CPA.
require import G7_DiscRand.

module B_D(A : PCR_REAL_ADV) : DFHE_DEN_ADV = {
  var stored_pk : dFHE_pkey
  proc choose(pk : dFHE_pkey) : dFHE_message * dFHE_message = {
    stored_pk <- pk;
    return (0, 0);
  }
  proc guess(target : dFHE_message, r : dFHE_randomness, c : dFHE_ciphertext) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_dFHE_Den_correctness (A <: PCR_REAL_ADV {-B_D}) &m lambda nT t nV nA nC :
  `| Pr[G6_dFHE_CPA(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G7_DiscRand(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_d)%r * `| Pr[DFHE_DEN_Game0(B_D(A)).main() @ &m : res]
                      - Pr[DFHE_DEN_Game1(B_D(A)).main() @ &m : res] |
   + (q_d)%r * advantage_NIZK_rd lambda.
