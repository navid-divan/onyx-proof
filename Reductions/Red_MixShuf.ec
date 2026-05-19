require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import MixNet.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G1_UT.
require import G2_MixShuf.

module B_M(A : PCR_REAL_ADV) : MixNet_SHUF_ADV = {
  var stored_pp : mixnet_pp
  proc choose(pp : mixnet_pp) : mixnet_ciphertext list = {
    stored_pp <- pp;
    return [];
  }
  proc distinguish(orig : mixnet_ciphertext list, mixed : mixnet_ciphertext list,
                   pf : mixnet_proof) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_MixShuf_correctness (A <: PCR_REAL_ADV {-B_M}) &m lambda nT t nV nA nC :
  `| Pr[G1_UT(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G2_MixShuf(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= `| Pr[MixNet_Shuffle_Real(B_M(A)).main() @ &m : res]
      - Pr[MixNet_Shuffle_Sim(B_M(A)).main() @ &m : res] |.
