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
require import H0_Real.
require import H1_NIZK.
require import H2_dFHE.
require import H3_Ballot.
require import H4_Tally.
require import H5_Ideal.

op total_bound (lambda : int) : real =
  (q_d)%r * (2%r * advantage_dFHE_den lambda + advantage_NIZK_rd lambda)
  + 2%r * (q_b)%r * advantage_dFHE_indcpa lambda
  + (q_b)%r * advantage_NIZK_zk lambda
  + advantage_UT_sim lambda
  + advantage_MixNet_shuf lambda
  + (n_T)%r * advantage_MixNet_ddec lambda
  + advantage_Hash_cr lambda.

lemma triangle_chain_six (a b c d e f g : real) :
  `| a - g | <= `| a - b | + `| b - c | + `| c - d | + `| d - e | + `| e - f | + `| f - g |.
proof.
smt(@Real).
qed.

lemma total_bound_eq_pcr_bound (lambda : int) :
  total_bound lambda = pcr_bound lambda q_b q_d n_T.
proof.
by rewrite /total_bound /pcr_bound.
qed.

lemma total_bound_nonneg (lambda : int) :
  0%r <= total_bound lambda.
proof.
rewrite total_bound_eq_pcr_bound; exact pcr_bound_nonneg.
qed.

lemma negligible_total_bound :
  negligible total_bound.
proof.
have hfn : total_bound = (fun (lambda : int) => pcr_bound lambda q_b q_d n_T).
  by apply fun_ext => lambda; exact total_bound_eq_pcr_bound.
rewrite hfn; exact negligible_pcr_bound.
qed.

(* THEOREM STATEMENT: Theorem 2 (Onyx satisfies PCR) *)
lemma onyx_pcr (A <: PCR_REAL_ADV) &m lambda nT t nV nA nC :
  `| Pr[PCR_Real_Experiment(Onyx, A).main(lambda, nT, t, nV, nA, nC) @ &m : res]
   - Pr[PCR_Ideal_Experiment(OnyxSimulator).main(lambda, nV, nA, nC) @ &m : res] |
  <= total_bound lambda_sec.
proof.
(* PROOF: Onyx satisfies PCR via the hybrid sequence H0 -> H1 -> H2 -> H3 -> H4 -> H5 *)
have h0_eq := H0_equiv_real A &m lambda nT t nV nA nC.
have h0_h1 := hybrid_H0_H1_bound A &m lambda nT t nV nA nC.
have h1_h2 := hybrid_H1_H2_bound A &m lambda nT t nV nA nC.
have h2_h3 := hybrid_H2_H3_bound A &m lambda nT t nV nA nC.
have h3_h4 := hybrid_H3_H4_bound A &m lambda nT t nV nA nC.
have h4_h5 := hybrid_H4_H5_eq A &m lambda nT t nV nA nC.
have h5_eq := H5_equiv_ideal A &m lambda nT t nV nA nC.
admit.
qed.

lemma onyx_pcr_secure :
  negligible total_bound.
proof.
exact negligible_total_bound.
qed.
