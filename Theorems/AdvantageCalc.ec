require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.

op pcr_bound (lambda : int) (q_b_v q_d_v : int) (n_T_v : int) : real =
  (q_d_v)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b_v)%r * advantage_dFHE_indcpa lambda
  + (q_b_v)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T_v)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda.

axiom q_b_nonneg : 0 <= q_b.
axiom q_d_nonneg : 0 <= q_d.

lemma pcr_bound_nonneg (lambda : int) :
  0%r <= pcr_bound lambda q_b q_d n_T.
proof.
rewrite /pcr_bound.
have hqd : 0%r <= (q_d)%r by smt(q_d_nonneg).
have hqb : 0%r <= (q_b)%r by smt(q_b_nonneg).
have hnt : 0%r <= (n_T)%r by smt(n_T_pos).
have h1 := advantage_dFHE_den_nonneg lambda.
have h2 := advantage_NIZK_rd_nonneg lambda.
have h3 := advantage_dFHE_indcpa_nonneg lambda.
have h4 := advantage_NIZK_zk_nonneg lambda.
have h5 := advantage_UT_sim_nonneg lambda.
have h6 := advantage_MixNet_shuf_nonneg lambda.
have h7 := advantage_MixNet_ddec_nonneg lambda.
have h8 := advantage_Hash_cr_nonneg lambda.
smt().
qed.

lemma negligible_dFHE_den_neg :
  negligible advantage_dFHE_den.
proof.
exact negligible_dFHE_den.
qed.

lemma negligible_pcr_bound :
  negligible (fun (lambda : int) => pcr_bound lambda q_b q_d n_T).
proof.
have step1 : negligible (fun lambda => 2%r * advantage_dFHE_den lambda).
  by apply negligible_scalar; exact negligible_dFHE_den.
have step2 : negligible (fun lambda => 2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda).
  by apply negligible_sum; [exact step1 | exact negligible_NIZK_rd].
have step3 : negligible (fun lambda => (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)).
  by apply negligible_scalar; exact step2.
have step4 : negligible (fun lambda => 2%r * (q_b)%r * advantage_dFHE_indcpa lambda).
  by apply negligible_scalar; exact negligible_dFHE_indcpa.
have step5 : negligible (fun lambda => (q_b)%r * advantage_NIZK_zk lambda).
  by apply negligible_scalar; exact negligible_NIZK_zk.
have step6 : negligible (fun lambda => (n_T)%r * advantage_MixNet_ddec lambda).
  by apply negligible_scalar; exact negligible_MixNet_ddec.
have s_a : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda).
  by apply negligible_sum; [exact step3 | exact step4].
have s_b : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda).
  by apply negligible_sum; [exact s_a | exact step5].
have s_c : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda).
  by apply negligible_sum; [exact s_b | exact negligible_UT_sim].
have s_d : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda).
  by apply negligible_sum; [exact s_c | exact negligible_MixNet_shuf].
have s_e : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda).
  by apply negligible_sum; [exact s_d | exact step6].
have s_f : negligible (fun lambda =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda).
  by apply negligible_sum; [exact s_e | exact negligible_Hash_cr].
have eq_fn :
  (fun (lambda : int) => pcr_bound lambda q_b q_d n_T) =
  (fun (lambda : int) =>
    (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda).
  by apply fun_ext => lambda; rewrite /pcr_bound.
rewrite eq_fn; exact s_f.
qed.

lemma pcr_bound_breakdown (lambda : int) :
  pcr_bound lambda q_b q_d n_T
  = (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda.
proof.
rewrite /pcr_bound; ring.
qed.
