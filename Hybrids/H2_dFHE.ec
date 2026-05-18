require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import VotingScheme.
require import PCR.
require import Onyx.
require import H1_NIZK.

module Hybrid_H2(A : PCR_REAL_ADV) = {
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

  proc oracle_reveal_h2(j : int) :
    election_credential * pcr_state_entry list = {
    var triples : pcr_state_entry list;
    var c_out : election_credential;
    var triples_out : pcr_state_entry list;
    var rv_honest, rc_honest : randomness;
    var k : int;
    var triples_updated : pcr_state_entry list;

    disc <- disc `|` fset1 j;
    triples <- odflt [] st.[j];
    if (beta_bit) {
      c_out <- nth witness creds (j-1);
      triples_out <- triples;
    } else {
      c_out <- witness;
      triples_updated <- [];
      k <- 0;
      while (k < size triples) {
        rv_honest <$ dFHE_rand_distr;
        rc_honest <$ dFHE_rand_distr;
        triples_updated <- triples_updated ++ [nth witness triples k];
        k <- k + 1;
      }
      triples_out <- triples_updated;
    }
    return (c_out, triples_out);
  }

  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    d <- false;
    return d;
  }
}.

lemma hybrid_H1_H2_bound (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[Hybrid_H1(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[Hybrid_H2(A).main(lambda, nT, t, nV, nA, nC) @ &m : res] |
  <= 2%r * (q_d)%r * advantage_dFHE_den lambda_sec.
proof.
admit.
qed.
