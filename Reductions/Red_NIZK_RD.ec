require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import NIZK.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H0_Real.
require import H1_NIZK.

module ReduceH0H1_to_NIZK_RD(A : PCR_REAL_ADV) : NIZK_RD_ADV = {
  var pcr_state : pcr_state_map
  var stmt_target : nizk_statement
  var wit_real : nizk_witness
  var wit_claim : nizk_witness

  proc choose(crs : nizk_crs) : nizk_statement * nizk_witness * nizk_witness = {
    stmt_target <- witness;
    wit_real <- witness;
    wit_claim <- witness;
    return (stmt_target, wit_real, wit_claim);
  }

  proc distinguish(w_disclosed : nizk_witness, r : nizk_randomness,
                   pi : nizk_proof) : bool = {
    var b : bool;
    b <- false;
    return b;
  }
}.

lemma red_nizk_rd_advantage (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H0(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H1(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= (q_d)%r * advantage_NIZK_rd lambda.
proof.
admit.
qed.
