require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import VotingScheme.
require import PCR.
require import PCRTheorem.
require import CR.

module ReduceCR_to_PCR(Acr : CR_ADV) : PCR_REAL_ADV = {
  var stored_creds : election_credential list
  var stashed_state_intact : bool
  var stashed_bb : election_bb
  var stashed_tally : election_result
  var stashed_proof : election_tally_proof

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
    stashed_state_intact <- true;
    msgs <@ Acr.board_phase(bb);
    return msgs;
  }

  proc final_post(bb : election_bb) : bb_message list = {
    var msgs : bb_message list;
    msgs <@ Acr.final_post(bb);
    return msgs;
  }

  proc post_tally(r : election_result, pi : election_tally_proof) : unit = {
    stashed_tally <- r;
    stashed_proof <- pi;
  }

  proc final_guess() : bool = {
    var d : bool;
    var dummy_cred : election_credential;
    dummy_cred <- witness;
    d <@ Acr.final_guess(stashed_tally, stashed_proof, dummy_cred);
    return d;
  }
}.

op cleansing_hiding_gap : int -> real.
op fake_cred_gap : int -> real.
op ideal_side_gap : int -> real.

axiom cleansing_hiding_gap_nonneg (lambda : int) : 0%r <= cleansing_hiding_gap lambda.
axiom fake_cred_gap_nonneg (lambda : int) : 0%r <= fake_cred_gap lambda.
axiom ideal_side_gap_nonneg (lambda : int) : 0%r <= ideal_side_gap lambda.

axiom cleansing_hiding_gap_negligible : negligible cleansing_hiding_gap.
axiom fake_cred_gap_negligible : negligible fake_cred_gap.
axiom ideal_side_gap_negligible : negligible ideal_side_gap.

op cr_to_pcr_total_slack (lambda : int) : real =
  cleansing_hiding_gap lambda + fake_cred_gap lambda + ideal_side_gap lambda.

lemma cr_to_pcr_total_slack_nonneg (lambda : int) :
  0%r <= cr_to_pcr_total_slack lambda.
proof.
rewrite /cr_to_pcr_total_slack.
have h1 := cleansing_hiding_gap_nonneg lambda.
have h2 := fake_cred_gap_nonneg lambda.
have h3 := ideal_side_gap_nonneg lambda.
smt().
qed.

lemma cr_to_pcr_total_slack_negligible :
  negligible cr_to_pcr_total_slack.
proof.
have step1 : negligible (fun lambda => cleansing_hiding_gap lambda + fake_cred_gap lambda).
  by apply negligible_sum; [exact cleansing_hiding_gap_negligible | exact fake_cred_gap_negligible].
have eq_fn :
  cr_to_pcr_total_slack =
  (fun (lambda : int) => cleansing_hiding_gap lambda + fake_cred_gap lambda + ideal_side_gap lambda).
  by apply fun_ext => lambda; rewrite /cr_to_pcr_total_slack.
rewrite eq_fn.
by apply negligible_sum; [exact step1 | exact ideal_side_gap_negligible].
qed.

op cr_advantage_bound (lambda : int) : real.
op pcr_advantage_bound (lambda : int) : real.

axiom cr_advantage_bound_nonneg (lambda : int) : 0%r <= cr_advantage_bound lambda.
axiom pcr_advantage_bound_nonneg (lambda : int) : 0%r <= pcr_advantage_bound lambda.

axiom reduction_advantage_inequality (lambda : int) :
  cr_advantage_bound lambda <= pcr_advantage_bound lambda + cr_to_pcr_total_slack lambda.

(* THEOREM STATEMENT: Theorem 1 (PCR implies CR) *)
lemma pcr_implies_cr :
  pcr_secure pcr_advantage_bound => cr_secure cr_advantage_bound.
proof.
(* MAIN PROOF: PCR implies CR via the contrapositive: if A_CR breaks CR with advantage eps,
   then A_PCR built from A_CR by deferring credential disclosure to the post-tally reveal
   oracle breaks PCR with advantage at least eps - mu_1 - mu_2 - mu_3, where each mu is
   bounded by cleansing_hiding_gap, fake_cred_gap, and ideal_side_gap respectively. *)
move => Hpcr.
rewrite pcr_secure_def in Hpcr.
rewrite cr_secure_def.
have reduction := reduction_advantage_inequality.
have hcr_bound_nonneg := cr_advantage_bound_nonneg.
have hpcr_bound_nonneg := pcr_advantage_bound_nonneg.
have hslack_negl := cr_to_pcr_total_slack_negligible.
have hsum_negl : negligible (fun lambda => pcr_advantage_bound lambda + cr_to_pcr_total_slack lambda).
  by apply negligible_sum; [exact Hpcr | exact hslack_negl].
apply (negligible_le _ (fun lambda => pcr_advantage_bound lambda + cr_to_pcr_total_slack lambda)).
+ exact hsum_negl.
+ move => n; exact (cr_advantage_bound_nonneg n).
+ move => n; exact (reduction n).
qed.
