require import AllCore Distr Real List FSet FMap Bool DBool.
require import Preamble.
require import VotingScheme.

module type CR_ADV = {
  proc corrupt(reg_R : election_register_record) : int fset
  proc coerce_choose(creds : election_credential list) : int * int
  proc board_phase(bb : election_bb) : bb_message list
  proc final_post(bb : election_bb) : bb_message list
  proc final_guess(r : election_result, pi : election_tally_proof,
                   c_dagger : election_credential) : bool
}.

module CR_Experiment(V : VotingScheme, A : CR_ADV) = {
  var bb : election_bb
  var pk_v : election_pk
  var shares_v : (election_sk_share * election_hint_t) list
  var creds : election_credential list
  var reg_R : election_register_record
  var corrupt_D : int fset
  var j_coerce : int
  var alpha_j : int
  var beta_bit : bool

  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    var msgs : bb_message list;
    var r_result : election_result;
    var pi_result : election_tally_proof;
    var c_dagger : election_credential;

    bb <- [];
    (pk_v, shares_v) <@ V.setup(lambda, nT, t);
    (creds, reg_R) <@ V.register(lambda, pk_v, nV);
    corrupt_D <@ A.corrupt(reg_R);
    (j_coerce, alpha_j) <@ A.coerce_choose(creds);
    beta_bit <$ {0,1};
    msgs <@ A.board_phase(bb);
    msgs <@ A.final_post(bb);
    (r_result, pi_result) <@ V.tally(bb, reg_R, pk_v, shares_v, t);
    if (beta_bit) {
      c_dagger <- nth witness creds (j_coerce - 1);
    } else {
      c_dagger <@ V.fakecred(pk_v);
    }
    d <@ A.final_guess(r_result, pi_result, c_dagger);
    return d;
  }
}.

op cr_secure : (int -> real) -> bool.

axiom cr_secure_def (f : int -> real) :
  cr_secure f <=> negligible f.
