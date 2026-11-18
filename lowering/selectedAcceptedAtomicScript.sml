Theory selectedAcceptedAtomic
Ancestors
  selectedAcceptedInterfaces calldataExactScalarAccepted calldataExactBytesJoint
  defaultWordDecodeExec calldataScalarSourceExact calldataSourceWord
  calldataReconstruction calldataRegistration abiDecoderCoherence
  abiDecoderContract entryDecodeStaticProps exprPtrCleanBufferPost
  calldataSourceCorrespondence compileEnv vyperValue vyperCalldata
  venomExecSemantics ptrDiscipline ptrSafetyTransport fragGasOriginPtr
  fragGasPathFrameMem fragGasPathMem words finite_map list arithmetic

Theorem selected_word_accepts[local]:
  is_word_type ty ==> selected_decoder_accepts ce env sf ty tv
Proof
  rewrite_tac[selected_decoder_accepts_def] >>
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?cl. type_to_abi_dec_info sf ce ty = DecPrimWord cl` by
    metis_tac[word_type_decoder_primitive] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_size tv = 32` by metis_tac[word_type_memory_size] >>
  qpat_assum `type_memory_size tv = 32`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  `d+32 <= initial.vs_alloca_next` by
    (irule abiCallerAllocationTheory.abi_caller_allocation_end >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all default_word_decode_exact_sequence >> strip_tac >>
  `!cd pos. cd_decode F cd tv pos = cd_word_value tv (cd_word cd pos)` by
    (qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_word_type ty` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[is_word_type_def, cd_decode_def]) >>
  `cd_word_value tv (abi_decode_load CALLDATALOAD p initial) = SOME x` by
    metis_tac[calldata_decode_load_word] >>
  `abi_clamp_ok cl (abi_decode_load CALLDATALOAD p initial)` by
    (drule_all calldata_scalar_source_exact >>
     disch_then (qspec_then `abi_decode_load CALLDATALOAD p initial` mp_tac) >>
     simp[]) >>
  `compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
     (DecPrimWord cl) st = ((),last)` by metis_tac[] >>
  drule_all calldata_word_accepted_resource_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t = v with vs_inst_idx := initial.vs_inst_idx` by metis_tac[exec_result_11] >>
  pop_assum SUBST_ALL_TAC >>
  `v.vs_code = initial.vs_code` by
    (qpat_assum `(v with vs_inst_idx := _) = _`
      (mp_tac o Q.AP_TERM `\s. s.vs_code`) >> simp[]) >>
  `allocas_from lower v` by
    (qpat_assum `allocas_from lower initial` mp_tac >>
     qpat_assum `v.vs_allocas = initial.vs_allocas`
       (fn th => rewrite_tac[allocas_from_def, th])) >>
  `val_in_memory tv x d v.vs_memory` by
    (qpat_assum `val_in_memory tv x d (v with vs_inst_idx := _).vs_memory` mp_tac >>
     simp[NoAsms]) >>
  drule_all word_type_memory_size >> strip_tac >>
  `!mem. mem_agree_outside u.t_mem v.vs_memory mem ==> val_in_memory tv x d mem` by
    (rpt strip_tac >> irule clean_window_value_robust >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`u.t_mem`,`v.vs_memory`,`32`] >>
     qpat_assum `type_memory_size tv = 32`
       (fn th => rewrite_tac[th, arithmeticTheory.LESS_EQ_REFL]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`v`,`[]`,`H`,`u`] >>
  qpat_assum `type_memory_size tv = 32` (fn th => rewrite_tac[th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[NoAsms]]
QED

Theorem selected_bytes_accepts[local]:
  is_bytestring_type ty ==> selected_decoder_accepts ce env sf ty tv
Proof
  rewrite_tac[selected_decoder_accepts_def] >>
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_exact_bytes_joint_limit >>
  disch_then (qspec_then `PG` mp_tac) >>
  qpat_assum `cd_decode F _ _ _ = SOME x` (fn th => simp[NoAsms, th]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `sc`
    (qx_choose_then `H` (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))))) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`ARB`,`{}`] assume_tac) >>
  `v.vs_code = initial.vs_code` by
    (drule selected_zero_path_mem >>
     disch_then (mp_tac o MATCH_MP gas_path_mem_exec) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_tac o MATCH_MP gas_path_code_labels) >>
     simp[NoAsms]) >>
  `allocas_from lower v` by
    (drule gas_origin_ptr_path_projections >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (mp_tac o MATCH_MP member_path_allocas_from) >>
     disch_then (qspecl_then [`lower`,`v`] mp_tac) >>
     impl_tac >- (rewrite_tac[LESS_EQ_REFL] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  qexistsl [`v`,`sc`,`H`,`u`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem selected_atomic_accepts:
  is_word_type ty \/ is_bytestring_type ty ==>
  selected_decoder_accepts ce env sf ty tv
Proof
  metis_tac[selected_word_accepts, selected_bytes_accepts]
QED
