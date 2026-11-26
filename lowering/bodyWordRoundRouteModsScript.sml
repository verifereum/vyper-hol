(* Close the linked rounding prefix with one physical suffix endpoint. *)
Theory bodyWordRoundRouteMods
Ancestors
  bodyWordRoundPrefixMods bodyWordRoundReadResultMods bodyWordRoundPostFrameMods
  bodyWordRoundSuffixRunMods stateRelProj bodyFullPostsMods exprSimWordArgs
  bodyFullShadowBodyInv bodyPtrDefs vyperValue gasOutcomeFullPostMods
  exprSimUnopComposeProps vyperStorageFootprint compileEnv list

(* A canonical horizon fixes the source value and the physical run. *)
Theorem rounding_continuation_mods[local]:
  ^(fst (dest_imp (concl word_rounding_prefix_mods)))
Proof
  BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `mid with gas_obs := [] = mid` (fn gas_nil =>
    qpat_assum `!tail. bind _ _ (_ with gas_obs := _ ++ tail) = (_, _ with gas_obs := tail)`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL, gas_nil]))) >>
  drule_all_then strip_assume_tac word_rounding_read_result_mods >>
  `alloca_inv t` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then assume_tac expr_post_state >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all word_rounding_suffix_run >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_operand op z = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v')` by
    (qpat_assum `typed_val_to_w256 (BaseTV (IntT 256)) v' = _`
       (fn word_eq => pure_rewrite_tac[word_eq]) >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`, `mid`, `INL v'`, `z`, `tn'`] >>
  conj_tac >- simp[unop_result_gas_obs] >>
  qx_gen_tac `H` >> disch_tac >> BETA_TAC >>
  conj_tac >- (qpat_assum `!D ex. gas_origin_ptr_path (D,_,ex,_,_,_) _ _ _` irule) >>
  qpat_assum `mid with gas_obs := [] = mid` SUBST1_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o SYM o SRULE [sumTheory.INL_11]) >>
  qexists_tac `v'` >> pure_rewrite_tac[sumTheory.INL_11, REFL_CLAUSE, AND_CLAUSES] >>
  irule word_rounding_post_frame_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`t.vs_inst_idx + LENGTH (emitted_insts s1 sb)`,
                `s1`,`t`,`tn1`,`u`,`v`,`x`] >>
  `post_value_type cenv e = BaseT DecimalT` by
    simp[loweringPostsTheory.post_value_type_word, is_word_type_def] >>
  pop_assum (fn ty_eq => pure_rewrite_tac[ty_eq]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[is_word_type_def])
QED

(* The prefix supplies the value and VV simulations without a conversion premise. *)
Theorem word_rounding_sim_mods:
  ^(snd (dest_imp (concl word_rounding_prefix_mods)))
Proof
  mp_tac word_rounding_prefix_mods >> rewrite_tac[rounding_continuation_mods]
QED
