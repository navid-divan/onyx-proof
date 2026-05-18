require import AllCore Distr Real List FSet FMap Bool DBool Int.
require import Preamble.
require import VotingScheme.

type pcr_state_entry = vote * randomness * ballot.
type pcr_state_map = (int, pcr_state_entry list) fmap.

module type PCR_BOARD_ORACLE = {
  proc publish() : election_bb
}.

module type PCR_REVEAL_ORACLE = {
  proc reveal(j : int) : election_credential * pcr_state_entry list
}.

module type PCR_REAL_ADV = {
  proc corrupt(reg_R : election_register_record) : int fset
  proc coerce_choose(creds : election_credential list) : int fset * (int, int) fmap
  proc board_phase(bb : election_bb) : bb_message list
  proc final_post(bb : election_bb) : bb_message list
  proc post_tally(r : election_result, pi : election_tally_proof) : unit
  proc final_guess() : bool
}.

module type PCR_IDEAL_ADV = {
  proc setup() : int fset
  proc coerce_choose() : int fset * (int, int) fmap
  proc fill_corrupt(sz : int) : (int, int) fmap * bool
  proc final_guess(r : election_result, claims : (int * int) list) : bool
}.

op msg_to_ballot : bb_message -> ballot option.

op extract_valid_ballots :
  election_pk -> bb_message list -> election_bb -> ballot list.

op behavioral_distribution : behavior_distribution.

op fakecred_distr : election_pk -> election_credential distr.

axiom fakecred_distr_ll (pk : election_pk) : is_lossless (fakecred_distr pk).

module PCR_Real_Experiment(V : VotingScheme, A : PCR_REAL_ADV) = {
  var bb : election_bb
  var st : pcr_state_map
  var disc : int fset
  var beta_bit : bool
  var pk_v : election_pk
  var shares_v : (election_sk_share * election_hint_t) list
  var creds : election_credential list
  var reg_R : election_register_record
  var corrupt_D : int fset
  var coerce_H : int fset
  var alphas : (int, int) fmap

  proc main(lambda : int, nT : int, t : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    var msgs : bb_message list;
    var valid_msgs : ballot list;
    var ballot_seq : behavior_list;
    var i : int;
    var v : vote;
    var rho : randomness;
    var b_cur : election_ballot;
    var r_result : election_result;
    var pi_result : election_tally_proof;
    var gated : bool;
    var b_post : bool;

    bb <- [];
    st <- empty;
    disc <- fset0;
    (pk_v, shares_v) <@ V.setup(lambda, nT, t);
    (creds, reg_R) <@ V.register(lambda, pk_v, nV);
    corrupt_D <@ A.corrupt(reg_R);
    (coerce_H, alphas) <@ A.coerce_choose(creds);
    ballot_seq <- [];
    beta_bit <$ {0,1};
    ballot_seq <- coerce_adjust ballot_seq coerce_H alphas beta_bit;
    i <- 0;
    d <- false;
    while (i < size ballot_seq) {
      msgs <@ A.board_phase(bb);
      valid_msgs <- extract_valid_ballots pk_v msgs bb;
      bb <- bb ++ valid_msgs;
      v <- snd (nth witness ballot_seq i);
      rho <- witness;
      b_cur <@ V.vote(pk_v, nth witness creds (fst (nth witness ballot_seq i) - 1), v, rho);
      bb <- bb ++ [b_cur];
      i <- i + 1;
    }
    msgs <@ A.final_post(bb);
    valid_msgs <- extract_valid_ballots pk_v msgs bb;
    bb <- bb ++ valid_msgs;
    (r_result, pi_result) <@ V.tally(bb, reg_R, pk_v, shares_v, t);
    A.post_tally(r_result, pi_result);
    gated <- coerce_H \subset disc;
    if (! gated) {
      b_post <$ {0,1};
      d <- b_post;
    } else {
      d <@ A.final_guess();
    }
    return d;
  }
}.

module PCR_Ideal_Experiment(A : PCR_IDEAL_ADV) = {
  var beta_bit : bool
  var corrupt_D : int fset
  var coerce_H : int fset
  var alphas : (int, int) fmap
  var board : behavior_list
  var dishonest_extra : (int, int) fmap

  proc main(lambda : int, nV : int, nA : int, nC : int) : bool = {
    var d : bool;
    var ballot_seq : behavior_list;
    var observed_size : int;
    var beta_adv : bool;
    var r_result : election_result;
    var claims_list : (int * int) list;
    var i : int;
    var bi : behavior_entry;
    var aug_board : behavior_list;
    var corruptions : int list;

    corrupt_D <@ A.setup();
    (coerce_H, alphas) <@ A.coerce_choose();
    ballot_seq <- [];
    beta_bit <$ {0,1};
    ballot_seq <- coerce_adjust ballot_seq coerce_H alphas beta_bit;
    board <- [];
    i <- 0;
    while (i < size ballot_seq) {
      bi <- nth witness ballot_seq i;
      board <- board ++ [bi];
      i <- i + 1;
    }
    observed_size <- size board;
    (dishonest_extra, beta_adv) <@ A.fill_corrupt(observed_size);
    aug_board <- board;
    corruptions <- elems (fdom dishonest_extra);
    i <- 0;
    while (i < size corruptions) {
      aug_board <- aug_board ++ [(nth witness corruptions i, oget dishonest_extra.[nth witness corruptions i])];
      i <- i + 1;
    }
    claims_list <- map (fun j => (j, oget alphas.[j])) (elems coerce_H);
    r_result <- result_func aug_board;
    d <@ A.final_guess(r_result, claims_list);
    return d;
  }
}.
