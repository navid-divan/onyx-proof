require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import NIZK.
require import VotingScheme.
require import PCR.
require import Onyx.
require import G6_dFHE_CPA.
require import G7_DiscRand.

module B_N(A : PCR_REAL_ADV) : NIZK_RD_ADV = {
  var stored_crs : nizk_crs
  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness * nizk_witness = {
    stored_crs <- crs;
    return (witness, witness, witness);
  }
  proc distinguish(w_disclosed : nizk_witness, r : nizk_randomness,
                   pi : nizk_proof) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

axiom Red_NIZK_RD_correctness (A <: PCR_REAL_ADV {-B_N}) &m (lambda : int) :
  (q_d)%r * advantage_NIZK_rd lambda
  <= (q_d)%r * `| Pr[NIZK_RD_Real(B_N(A)).main() @ &m : res]
                - Pr[NIZK_RD_Fake(B_N(A)).main() @ &m : res] |.
