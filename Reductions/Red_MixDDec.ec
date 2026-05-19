require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import MixNet.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G2_MixShuf.
require import G3_MixDDec.

module B_DD(A : PCR_REAL_ADV) : MixNet_DDEC_ADV = {
  var stored_pp : mixnet_pp
  proc choose_corrupt(pp : mixnet_pp) : int fset = {
    stored_pp <- pp;
    return fset0;
  }
  proc choose_cts() : mixnet_ciphertext list = {
    return [];
  }
  proc distinguish(parts : (mixnet_partial list * mixnet_ddec) list) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_MixDDec_correctness (A <: PCR_REAL_ADV {-B_DD}) &m lambda nT t nV nA nC :
  `| Pr[G2_MixShuf(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G3_MixDDec(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= (n_T)%r * `| Pr[MixNet_DDec_Real(B_DD(A)).main() @ &m : res]
                - Pr[MixNet_DDec_Sim(B_DD(A)).main() @ &m : res] |.
