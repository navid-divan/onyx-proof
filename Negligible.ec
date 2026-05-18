require import AllCore Real.
require import Preamble.

op advantage_dFHE_den : int -> real.
op advantage_dFHE_indcpa : int -> real.
op advantage_NIZK_rd : int -> real.
op advantage_NIZK_zk : int -> real.
op advantage_NIZK_ks : int -> real.
op advantage_UT_sim : int -> real.
op advantage_UT_robust : int -> real.
op advantage_MixNet_shuf : int -> real.
op advantage_MixNet_ddec : int -> real.
op advantage_MixNet_verif : int -> real.
op advantage_VSS_verif : int -> real.
op advantage_VSS_unpredict : int -> real.
op advantage_Hash_cr : int -> real.

axiom advantage_dFHE_den_nonneg (lambda : int) : 0%r <= advantage_dFHE_den lambda.
axiom advantage_dFHE_indcpa_nonneg (lambda : int) : 0%r <= advantage_dFHE_indcpa lambda.
axiom advantage_NIZK_rd_nonneg (lambda : int) : 0%r <= advantage_NIZK_rd lambda.
axiom advantage_NIZK_zk_nonneg (lambda : int) : 0%r <= advantage_NIZK_zk lambda.
axiom advantage_NIZK_ks_nonneg (lambda : int) : 0%r <= advantage_NIZK_ks lambda.
axiom advantage_UT_sim_nonneg (lambda : int) : 0%r <= advantage_UT_sim lambda.
axiom advantage_UT_robust_nonneg (lambda : int) : 0%r <= advantage_UT_robust lambda.
axiom advantage_MixNet_shuf_nonneg (lambda : int) : 0%r <= advantage_MixNet_shuf lambda.
axiom advantage_MixNet_ddec_nonneg (lambda : int) : 0%r <= advantage_MixNet_ddec lambda.
axiom advantage_MixNet_verif_nonneg (lambda : int) : 0%r <= advantage_MixNet_verif lambda.
axiom advantage_VSS_verif_nonneg (lambda : int) : 0%r <= advantage_VSS_verif lambda.
axiom advantage_VSS_unpredict_nonneg (lambda : int) : 0%r <= advantage_VSS_unpredict lambda.
axiom advantage_Hash_cr_nonneg (lambda : int) : 0%r <= advantage_Hash_cr lambda.

axiom negligible_dFHE_den : negligible advantage_dFHE_den.
axiom negligible_dFHE_indcpa : negligible advantage_dFHE_indcpa.
axiom negligible_NIZK_rd : negligible advantage_NIZK_rd.
axiom negligible_NIZK_zk : negligible advantage_NIZK_zk.
axiom negligible_NIZK_ks : negligible advantage_NIZK_ks.
axiom negligible_UT_sim : negligible advantage_UT_sim.
axiom negligible_UT_robust : negligible advantage_UT_robust.
axiom negligible_MixNet_shuf : negligible advantage_MixNet_shuf.
axiom negligible_MixNet_ddec : negligible advantage_MixNet_ddec.
axiom negligible_MixNet_verif : negligible advantage_MixNet_verif.
axiom negligible_VSS_verif : negligible advantage_VSS_verif.
axiom negligible_VSS_unpredict : negligible advantage_VSS_unpredict.
axiom negligible_Hash_cr : negligible advantage_Hash_cr.

axiom dFHE_den_bound :
  forall (lambda : int), advantage_dFHE_den lambda <= 1%r / delta_sec.

axiom delta_superpoly :
  forall (c : int), exists (lambda0 : int),
    forall (lambda : int), lambda0 <= lambda =>
      (lambda ^ c)%r <= delta_sec.

op smudging_distance : int -> real.
op rejsamp_distance : int -> real.

axiom smudging_distance_nonneg (lambda : int) : 0%r <= smudging_distance lambda.
axiom rejsamp_distance_nonneg (lambda : int) : 0%r <= rejsamp_distance lambda.

axiom negligible_smudging : negligible smudging_distance.
axiom negligible_rejsamp : negligible rejsamp_distance.

axiom nizk_rd_bound (lambda : int) :
  advantage_NIZK_rd lambda <= smudging_distance lambda + rejsamp_distance lambda.
