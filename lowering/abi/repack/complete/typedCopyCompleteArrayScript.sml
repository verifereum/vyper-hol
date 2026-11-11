(* TOP-LEVEL: compatible-copy completeness lifts through both array
   constructors. Complete evaluations supply their count/capacity bounds. *)
Theory typedCopyCompleteArray
Ancestors
  vyperEventArgCompat
  typedCopyCompleteDefs typedCopyArrayTypeContracts typedArrayLoopValues typedSArrayDynSafety
  vyperTypeValues vyperValue context compileEnv compileVyper vyperTypeContract vyperContext
  list words arithmetic

Theorem evaluate_type_fixed_count_bound:
  !tenv ty tv copy_count.
    evaluate_type tenv (ArrayT ty (Fixed copy_count)) = SOME (ArrayTV tv (Fixed copy_count)) ==>
    copy_count < dimword(:256)
Proof
  rpt gen_tac >> DISCH_TAC >> drule evaluate_type_ArrayT_cases >>
  disch_then (qx_choose_then `candidate_tv` strip_assume_tac) >>
  `candidate_tv = tv` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  asm_simp_tac (srw_ss()) [LET_THM, type_slot_size_def] >> strip_tac >>
  mp_tac (Q.SPECL [`copy_count`, `type_slot_size tv`, `0`] array_copy_count_bound) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]
QED

Theorem typed_copy_complete_fixed:
  !tops in_deploy layouts addr art ctx func cenv fty copy_count.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    typed_copy_complete (type_env tops) ctx func cenv fty ==>
    typed_copy_complete (type_env tops) ctx func cenv (ArrayT fty (Fixed copy_count))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  qpat_assum `event_arg_compatible _ _`
    (qx_choose_then `source_elem` strip_assume_tac o MATCH_MP compatible_fixed_array_source) >>
  qpat_x_assum `aty = ArrayT source_elem _` SUBST_ALL_TAC >>
  qpat_assum `evaluate_type _ (ArrayT fty _) = SOME ftv`
    (qx_choose_then `elem_ftv` strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >>
  qpat_assum `evaluate_type _ (ArrayT source_elem _) = SOME atv`
    (qx_choose_then `elem_atv` strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >>
  qpat_x_assum `ftv = ArrayTV elem_ftv _` SUBST_ALL_TAC >>
  qpat_x_assum `atv = ArrayTV elem_atv _` SUBST_ALL_TAC >>
  drule evaluate_type_fixed_count_bound >> DISCH_TAC >>
  drule_all typed_copy_complete_instance >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fty`, `source_elem`,
    `elem_ftv`, `elem_atv`, `copy_count`] typed_copy_type_contract_sarray) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, DISCH_TAC >> first_assum MATCH_ACCEPT_TAC]) >> simp[]
QED

Theorem typed_copy_complete_dynamic:
  !tops in_deploy layouts addr art ctx func cenv fty dst_capacity.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    typed_copy_complete (type_env tops) ctx func cenv fty ==>
    typed_copy_complete (type_env tops) ctx func cenv (ArrayT fty (Dynamic dst_capacity))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  qpat_assum `event_arg_compatible _ _`
    (qx_choose_then `source_elem` (qx_choose_then `src_capacity` strip_assume_tac) o MATCH_MP compatible_dynamic_array_source) >>
  qpat_x_assum `aty = ArrayT source_elem _` SUBST_ALL_TAC >>
  qpat_assum `evaluate_type _ (ArrayT fty _) = SOME ftv`
    (qx_choose_then `elem_ftv` strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >>
  qpat_assum `evaluate_type _ (ArrayT source_elem _) = SOME atv`
    (qx_choose_then `elem_atv` strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >>
  qpat_x_assum `ftv = ArrayTV elem_ftv _` SUBST_ALL_TAC >>
  qpat_x_assum `atv = ArrayTV elem_atv _` SUBST_ALL_TAC >>
  qpat_assum `evaluate_type _ (ArrayT fty _) = _`
    (strip_assume_tac o MATCH_MP evaluate_type_dynarray_count_bound) >>
  drule_all typed_copy_complete_instance >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fty`, `source_elem`,
    `elem_ftv`, `elem_atv`, `dst_capacity`, `src_capacity`] typed_copy_type_contract_dynarray) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, DISCH_TAC >> first_assum MATCH_ACCEPT_TAC]) >> simp[]
QED
