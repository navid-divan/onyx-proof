require import AllCore Distr Real List FSet FMap Bool DBool.
require import Preamble.
require import Negligible.
require import DFHE.
require import UT.
require import VSS.
require import MixNet.
require import NIZK.
require import Hash.
require import VotingScheme.

op encode_credential : int -> credential.

op credential_to_int : credential -> int.

op onyx_relation : (ciphertext * ciphertext * setup_public_params) ->
                   (vote * credential * randomness * randomness) -> bool.

op onyx_setup_state : election_pk -> nizk_crs -> nizk_td -> ut_pp -> mixnet_pp -> election_setup_state.

op merge_ep : dFHE_pkey -> ut_pp -> nizk_crs -> mixnet_pp -> int -> election_pk.

op cred_distr : credential distr.
axiom cred_distr_ll : is_lossless cred_distr.

op int_distr : int distr.
axiom int_distr_ll : is_lossless int_distr.

module Onyx : VotingScheme = {
  proc setup(lambda : int, nT : int, t : int) :
    election_pk * (election_sk_share * election_hint_t) list = {
    var dpk : dFHE_pkey;
    var dsk : dFHE_skey;
    var pp_ut : ut_pp;
    var sks_ut : ut_share list;
    var crs : nizk_crs;
    var td : nizk_td;
    var pp_mn : mixnet_pp;
    var sks_mn : mixnet_skey list;
    var ep : election_pk;
    var shares_out : (election_sk_share * election_hint_t) list;

    (dpk, dsk) <$ dFHE_keygen lambda;
    (pp_ut, sks_ut) <$ ut_setup lambda nT t [];
    (crs, td) <$ nizk_setup lambda;
    (pp_mn, sks_mn) <$ mixnet_setup lambda 4 4;
    ep <- merge_ep dpk pp_ut crs pp_mn n_C;
    shares_out <- [];
    return (ep, shares_out);
  }

  proc register(lambda : int, pk : election_pk, nV : int) :
    election_credential list * election_register_record = {
    var creds_out : election_credential list;
    var roster : election_register_record;
    var i : int;
    var c_id : credential;

    creds_out <- [];
    i <- 0;
    while (i < nV) {
      c_id <$ cred_distr;
      creds_out <- creds_out ++ [c_id];
      i <- i + 1;
    }
    roster <- witness;
    return (creds_out, roster);
  }

  proc vote(pk : election_pk, c : election_credential, v : vote, r : randomness) :
    election_ballot = {
    var rv, rc, rpi : randomness;
    var cv_ct, cc_ct : ciphertext;
    var stmt : nizk_statement;
    var wit : nizk_witness;
    var pi : nizk_proof;
    var b : election_ballot;

    rv <- witness;
    rc <- witness;
    rpi <- witness;
    cv_ct <- dFHE_enc witness v rv;
    cc_ct <- dFHE_enc witness (credential_to_int c) rc;
    stmt <- (cv_ct, cc_ct, witness);
    wit <- (v, c, rv, rc);
    pi <- nizk_prove witness witness stmt wit rpi;
    b <- (cv_ct, cc_ct, pi);
    return b;
  }

  proc valid(pk : election_pk, b : election_ballot, bb : election_bb) : bool = {
    var cv_ct, cc_ct : ciphertext;
    var pi : proof_type;
    var stmt : nizk_statement;
    var e1, e2 : bool;

    (cv_ct, cc_ct, pi) <- b;
    stmt <- (cv_ct, cc_ct, witness);
    e1 <- nizk_verify witness stmt pi;
    e2 <- ! (b \in bb);
    return e1 /\ e2;
  }

  proc tally(bb : election_bb, reg : election_register_record, pk : election_pk,
             shares : (election_sk_share * election_hint_t) list, t : int) :
    election_result * election_tally_proof = {
    var r : election_result;
    var pi_t : election_tally_proof;

    r <- witness;
    pi_t <- witness;
    return (r, pi_t);
  }

  proc verify(pk : election_pk, bb : election_bb, reg : election_register_record,
              r : election_result, pi : election_tally_proof) : bool = {
    return true;
  }

  proc fake(ls : election_local_state, v_star : vote, c_star : election_credential,
            vs : election_voter_state) :
    election_credential * vote * randomness * randomness * randomness = {
    var rv_star, rc_star, rpi_star : randomness;
    var v : vote;
    var c : credential;
    var rv, rc, rpi : randomness;

    v <- witness;
    c <- witness;
    rv <- witness;
    rc <- witness;
    rpi <- witness;
    rv_star <- dFHE_fake witness v rv v_star;
    rc_star <- dFHE_fake witness (credential_to_int c) rc (credential_to_int c_star);
    rpi_star <- nizk_fake witness witness witness (v, c, rv, rc) rpi
                  (v_star, c_star, rv_star, rc_star);
    return (c_star, v_star, rv_star, rc_star, rpi_star);
  }

  proc fakecred(pk : election_pk) : election_credential = {
    var c : credential;
    c <$ cred_distr;
    return c;
  }
}.
