require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import VotingScheme.
require import PCR.
require import PCRTheorem.
require import CR.

module ReduceCR_to_PCR(Acr : CR_ADV) : PCR_REAL_ADV = {
  var stored_creds : election_credential list

  proc corrupt(reg_R : election_register_record) : int fset = {
    var ds : int fset;
    ds <@ Acr.corrupt(reg_R);
    return ds;
  }

  proc coerce_choose(creds_in : election_credential list) : int fset * (int, int) fmap = {
    var j : int;
    var alpha : int;
    var hs : int fset;
    var amap : (int, int) fmap;
    stored_creds <- creds_in;
    (j, alpha) <@ Acr.coerce_choose(creds_in);
    hs <- fset1 j;
    amap <- empty.[j <- alpha];
    return (hs, amap);
  }

  proc board_phase(bb : election_bb) : bb_message list = {
    var msgs : bb_message list;
    msgs <@ Acr.board_phase(bb);
    return msgs;
  }

  proc final_post(bb : election_bb) : bb_message list = {
    var msgs : bb_message list;
    msgs <@ Acr.final_post(bb);
    return msgs;
  }

  proc post_tally(r : election_result, pi : election_tally_proof) : unit = {
  }

  proc final_guess() : bool = {
    var d : bool;
    var dummy_result : election_result;
    var dummy_proof : election_tally_proof;
    var dummy_cred : election_credential;
    dummy_result <- witness;
    dummy_proof <- witness;
    dummy_cred <- witness;
    d <@ Acr.final_guess(dummy_result, dummy_proof, dummy_cred);
    return d;
  }
}.

(* THEOREM STATEMENT: Theorem 1 - PCR implies CR *)
lemma pcr_implies_cr (f g : int -> real) :
  pcr_secure f => cr_secure g.
proof.
move => Hpcr.
rewrite cr_secure_def.
rewrite pcr_secure_def in Hpcr.
admit.
qed.
