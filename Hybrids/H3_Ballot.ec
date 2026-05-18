require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import NIZK.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H2_dFHE.

module Hybrid_H3(A : PCR_REAL_ADV) = {
  var bb : election_bb
  var st : pcr_state_map
  var disc : int fset
  var beta_bit : bool
  var pk_v : election_pk
  var shares_v : (election_sk_share * election_hint) list
  var creds : election_credential list
  var reg_R : election_register_record
  var corrupt_D : int fset
  var coerce_H : int fset
  var alphas : (int, int) fmap

  proc cast_claim_ballot(i : int, v_true : vote, c_true : credential,
                         v_claim : vote, c_claim : credential) : election_ballot = {
    var rv_hon, rc_hon, rpi_hon : randomness;
    var cv_claim, cc_claim : ciphertext;
    var stmt : nizk_statement;
    var wit : nizk_witness;
    var pi_claim : nizk_proof;

    rv_hon <$ dFHE_rand_distr;
    rc_hon <$ dFHE_rand_distr;
    rpi_hon <$ nizk_rand_distr;
    cv_claim <- dFHE_enc witness v_claim rv_hon;
    cc_claim <- dFHE_enc witness (credential_to_int c_claim) rc_hon;
    stmt <- (cv_claim, cc_claim, witness);
    wit <- (v_claim, c_claim, rv_hon, rc_hon);
    pi_claim <- nizk_prove witness witness stmt wit rpi_hon;
    return (cv_claim, cc_claim, pi_claim);
  }

  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

lemma hybrid_H2_H3_bound (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H2(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H3(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_b)%r * advantage_dFHE_indcpa lambda_sec
   + (q_b)%r * advantage_NIZK_zk lambda_sec.
proof.
admit.
qed.
