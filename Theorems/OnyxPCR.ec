require import AllCore Distr Real List FSet FMap Bool.
require import Preamble.
require import Negligible.
require import DFHE.
require import UT.
require import VSS.
require import MixNet.
require import NIZK.
require import Hash.
require import VotingScheme.
require import Policy.
require import PCR.
require import PCRTheorem.
require import AdvantageCalc.
require import Onyx.
require import G1_UT.
require import G2_MixShuf.
require import G3_MixDDec.
require import G4_Hash.
require import G5_NIZK_ZK.
require import G6_dFHE_CPA.
require import G7_DiscRand.
require import G8_Ideal.

op total_bound (lambda : int) : real =
  advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + final_negl_gap lambda.

lemma total_bound_nonneg (lambda : int) :
  0%r <= total_bound lambda.
proof.
rewrite /total_bound.
have h1 := advantage_UT_sim_nonneg lambda.
have h2 := advantage_MixNet_shuf_nonneg lambda.
have h3 := advantage_MixNet_ddec_nonneg lambda.
have h4 := advantage_Hash_cr_nonneg lambda.
have h5 := advantage_NIZK_zk_nonneg lambda.
have h6 := advantage_dFHE_indcpa_nonneg lambda.
have h7 := advantage_dFHE_den_nonneg lambda.
have h8 := advantage_NIZK_rd_nonneg lambda.
have h9 := final_negl_gap_nonneg lambda.
have hqd : 0%r <= (q_d)%r by smt(q_d_nonneg).
have hqb : 0%r <= (q_b)%r by smt(q_b_nonneg).
have hnt : 0%r <= (n_T)%r by smt(n_T_pos).
smt().
qed.

lemma negligible_total_bound :
  negligible total_bound.
proof.
have s1 : negligible (fun lambda => (n_T)%r * advantage_MixNet_ddec lambda).
  by apply negligible_scalar; exact negligible_MixNet_ddec.
have s2 : negligible (fun lambda => (q_b)%r * advantage_NIZK_zk lambda).
  by apply negligible_scalar; exact negligible_NIZK_zk.
have s3 : negligible (fun lambda => 2%r * (q_b)%r * advantage_dFHE_indcpa lambda).
  by apply negligible_scalar; exact negligible_dFHE_indcpa.
have s4a : negligible (fun lambda => 2%r * advantage_dFHE_den lambda).
  by apply negligible_scalar; exact negligible_dFHE_den.
have s4b : negligible (fun lambda => 2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda).
  by apply negligible_sum; [exact s4a | exact negligible_NIZK_rd].
have s4 : negligible (fun lambda => (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)).
  by apply negligible_scalar; exact s4b.
have t1 : negligible (fun lambda => advantage_UT_sim lambda + advantage_MixNet_shuf lambda).
  by apply negligible_sum; [exact negligible_UT_sim | exact negligible_MixNet_shuf].
have t2 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda).
  by apply negligible_sum; [exact t1 | exact s1].
have t3 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda).
  by apply negligible_sum; [exact t2 | exact negligible_Hash_cr].
have t4 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda).
  by apply negligible_sum; [exact t3 | exact s2].
have t5 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda).
  by apply negligible_sum; [exact t4 | exact s3].
have t6 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)).
  by apply negligible_sum; [exact t5 | exact s4].
have t7 : negligible (fun lambda =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + final_negl_gap lambda).
  by apply negligible_sum; [exact t6 | exact final_negl_gap_negligible].
have eq_fn : total_bound = (fun (lambda : int) =>
    advantage_UT_sim lambda + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda + advantage_Hash_cr lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + final_negl_gap lambda).
  by apply fun_ext => lambda; rewrite /total_bound.
by rewrite eq_fn; exact t7.
qed.

lemma triangle_three (a b c : real) : `| a - c | <= `| a - b | + `| b - c |.
proof. smt(@Real). qed.

lemma triangle_chain_nine (x0 x1 x2 x3 x4 x5 x6 x7 x8 : real) :
  `| x0 - x8 |
  <= `| x0 - x1 | + `| x1 - x2 | + `| x2 - x3 | + `| x3 - x4 |
   + `| x4 - x5 | + `| x5 - x6 | + `| x6 - x7 | + `| x7 - x8 |.
proof.
have s7 := triangle_three x0 x7 x8.
have s6 := triangle_three x0 x6 x7.
have s5 := triangle_three x0 x5 x6.
have s4 := triangle_three x0 x4 x5.
have s3 := triangle_three x0 x3 x4.
have s2 := triangle_three x0 x2 x3.
have s1 := triangle_three x0 x1 x2.
smt(@Real).
qed.

(* THEOREM STATEMENT: Theorem 2 (Onyx satisfies Persistent Coercion Resistance) *)
lemma onyx_pcr (A <: PCR_REAL_ADV
  {-G1_UT, -G2_MixShuf, -G3_MixDDec, -G4_Hash, -G5_NIZK_ZK,
   -G6_dFHE_CPA, -G7_DiscRand, -OnyxSim, -PCR_Real_Experiment, -PCR_Ideal_Experiment})
  &m lambda nT t nV nA nC :
  `| Pr[PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[PCR_Ideal_Experiment(OnyxSim(A)).main(lambda, nV, nA, nC) @ &m : res] |
  <= total_bound lambda.
proof.
(* MAIN PROOF: Onyx satisfies PCR via the nine-hybrid sequence G_0..G_8 from the paper.
   We chain the eight per-hop bounds through the nine-point triangle inequality. *)
have h01 := hop_G0_G1 A &m lambda nT t nV nA nC.
have h12 := hop_G1_G2 A &m lambda nT t nV nA nC.
have h23 := hop_G2_G3 A &m lambda nT t nV nA nC.
have h34 := hop_G3_G4 A &m lambda nT t nV nA nC.
have h45 := hop_G4_G5 A &m lambda nT t nV nA nC.
have h56 := hop_G5_G6 A &m lambda nT t nV nA nC.
have h67 := hop_G6_G7 A &m lambda nT t nV nA nC.
have h78 := hop_G7_G8 A &m lambda nT t nV nA nC.
have triangle := triangle_chain_nine
  Pr[PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G1_UT(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G2_MixShuf(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G3_MixDDec(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G4_Hash(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G5_NIZK_ZK(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G6_dFHE_CPA(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[G7_DiscRand(A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
  Pr[PCR_Ideal_Experiment(OnyxSim(A)).main(lambda, nV, nA, nC) @ &m : res].
rewrite /total_bound; smt().
qed.

lemma onyx_pcr_secure :
  negligible total_bound.
proof.
exact negligible_total_bound.
qed.
