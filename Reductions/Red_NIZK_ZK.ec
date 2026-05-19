require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import NIZK.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G4_Hash.
require import G5_NIZK_ZK.

module B_Z(A : PCR_REAL_ADV) : NIZK_ZK_ADV = {
  var stored_crs : nizk_crs
  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness = {
    stored_crs <- crs;
    return (witness, witness);
  }
  proc distinguish(pi : nizk_proof) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_NIZK_ZK_correctness (A <: PCR_REAL_ADV {-B_Z}) &m lambda nT t nV nA nC :
  `| Pr[G4_Hash(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[G5_NIZK_ZK(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= (q_b)%r * `| Pr[NIZK_ZK_Real(B_Z(A)).main() @ &m : res]
                - Pr[NIZK_ZK_Sim(B_Z(A)).main() @ &m : res] |.
