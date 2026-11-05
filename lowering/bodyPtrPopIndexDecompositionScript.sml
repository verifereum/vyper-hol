Theory bodyPtrPopIndexDecomposition
Ancestors
  exprLoweringProps exprLowering compileEnv context

Theorem pop_subscript_index_decomposition:
  !f ce bt idx sa out sb.
    (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
    compile_get_target_ptr f ce (SubscriptTarget bt idx) sa = (out,sb) ==>
    ?sc sd cv.
      cs_extends sa sc /\ f ce (expr_type idx) idx sc = (cv,sd) /\
      cs_extends sc sd /\ cs_extends sd sb
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr f ce bt sa` >>
  PairCases_on `q` >>
  `ci_mono sa r` by
    (mp_tac ci_mono_compile_get_target_ptr_cfn >>
     disch_then (qspecl_then [`f`,`bt`,`ce`,`sa`] mp_tac) >> simp[]) >>
  Cases_on `f ce (expr_type idx) idx r` >>
  rename1 `f ce (expr_type idx) idx r = (cv,sd)` >>
  `ci_mono r sd` by metis_tac[pairTheory.SND] >>
  Cases_on `unwrap_value ce cv sd` >>
  rename1 `unwrap_value ce cv sd = (op,su)` >>
  `ci_mono sd su` by
    (mp_tac ci_mono_unwrap_value >>
     disch_then (qspecl_then [`ce`,`cv`,`sd`] mp_tac) >> simp[]) >>
  `lower_value f ce (expr_type idx) idx r = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  qexistsl_tac [`r`,`sd`,`cv`] >>
  simp[] >> conj_tac >- gvs[ci_mono_def] >>
  conj_tac >- gvs[ci_mono_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _` mp_tac >>
  Cases_on `q2` >>
  simp[Once compile_get_target_ptr_def, comp_bind_def]
  >- (pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      `ci_mono su cs'` by
        metis_tac[ci_mono_compile_array_subscript,
                  ci_mono_compile_ptr_load, pairTheory.SND] >>
      gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  Cases_on `x` >> simp[comp_bind_def]
  >- (pairarg_tac >> simp[] >> pairarg_tac >>
      simp[comp_return_def] >> strip_tac >> gvs[] >>
      `ci_mono cs' cs''` by
        metis_tac[ci_mono_compile_mapping_subscript, pairTheory.SND] >>
      `ci_mono su cs'` by
        (Cases_on `is_bytestring_type t` >> gvs[comp_return_def]
         >- metis_tac[ci_mono_compile_keccak256_key, pairTheory.SND] >>
         simp[ci_mono_refl]) >>
      gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  `ci_mono su cs'` by
    metis_tac[ci_mono_compile_array_subscript,
              ci_mono_compile_ptr_load, pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED
