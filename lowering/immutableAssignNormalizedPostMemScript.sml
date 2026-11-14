(* Statement restoration at the actual counted normalization witnesses. *)
Theory immutableAssignNormalizedPostMem
Ancestors
  immutableAssignNormalizedPathMem immutableNormalizedCompiler immutableFixedOptionMem
  immutableStoreOptionMem immutableCopyExecution immutableAssignCompose
  immutableAssignNormalizeFrame immutableDeployAssignRestore placeStoreDynPrepare
  typedMemoryCopy exprSimAlloc fragGasPathFrameMem stmtSimDeclCompose stmtSimDefs
  typedNormalizeEntryBoundary abiEncoderExitPhi abiDecoderPhi
  exprLoweringProps exprOperandVar localPtrsProps loweringHalt stmtLoweringMono
  fragExec fragGasMode compileEnv context emitHelper emitHelperProps
  venomState venomExecSemantics venomInst loweringStateRelDefs
  finite_map list rich_list arithmetic words pair

Theorem immutable_normalized_fixed_nonempty[local]:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\ 0 < n ==>
  sb.cs_current_insts <> []
Proof
  Cases_on `n` >> simp[immutable_store_suc, comp_ignore_bind_def,
    immutable_comp_bind_cases] >> rpt strip_tac >>
  drule immutable_fixed_words_code_option >> strip_tac >>
  qpat_x_assum `immutable_store_one _ _ _ _ _ = _` mp_tac >>
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> rpt strip_tac >>
  imp_res_tac immutable_byte_offset_extends >>
  imp_res_tac emitted_insts_emit_op >>
  drule immutable_store_option_code >> strip_tac >>
  gvs[APPEND_eq_NIL]
QED

Theorem immutable_normalized_phi_boundary[local]:
  compile_alloc_buffer sz sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
  compile_imm_store_words imm buf.buf_operand dst n 0 sn = ((),sb) /\
  0 < n /\ fn_has_code sm sb func ==>
  (emitted_blocks sm sb <> [] ==> ?bb.
    lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule immutable_fixed_words_code_option >> strip_tac >>
  rename1 `sb.cs_current_insts = sn.cs_current_insts ++ code` >>
  `cs_extends sm mid /\ cs_extends mid sn /\ cs_extends sn sb` by
    (conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     conj_tac >- metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, SND] >>
     metis_tac[externalEntryShapeTheory.compile_imm_store_words_labels, SND]) >>
  `fn_has_code sn sb func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  strip_tac >>
  `emitted_blocks mid sn <> []` by
    gvs[emitted_blocks_def,same_blocks_def] >>
  `phi_prefix_length sn.cs_current_insts = 0` by
    metis_tac[normalize_typed_changed_prefix_zero] >>
  `phi_prefix_length code = 0` by
    (Cases_on `code` >> simp[phi_prefix_length_def] >>
     fs[EVERY_DEF] >> gvs[phi_prefix_length_def,mk_inst_def]) >>
  `phi_prefix_length sb.cs_current_insts = 0` by
    metis_tac[abi_decoder_phi_append] >>
  `sb.cs_current_insts <> []` by metis_tac[immutable_normalized_fixed_nonempty] >>
  fs[fn_has_code_def,IS_PREFIX_APPEND] >>
  irule abi_encoder_nonempty_prefix_phi >>
  qexists_tac `sb.cs_current_insts` >> simp[IS_PREFIX_APPEND,APPEND_ASSOC]
QED

Theorem immutable_normalized_actual_state[local]:
  compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ sz < dimword (:256) /\
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sm.cs_next_var)]) s (n2w sz : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts /\
  u.vs_memory = s.vs_memory /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,sz) /\
  (r with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := mid.cs_current_bb; vs_inst_idx := LENGTH mid.cs_current_insts;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sm x ==> lookup_var x r = lookup_var x s) /\
  (!q k. q+k <= b \/ b+sz <= q ==>
    mem_bytes_at q k r.vs_memory = mem_bytes_at q k s.vs_memory) /\
  gas_marked_path T ctx func u 0 (OK r) ==>
  stmt_state_rel ctx func ce cx es r /\ alloca_frame ce es sm s ce es r /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP r.vs_allocas aid = SOME entry)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >>
  disch_then (qx_choose_then `raw` (qx_choose_then `w`
    (map_every assume_tac o CONJUNCTS))) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `raw = u with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ s = OK raw` mp_tac >>
     simp[emitted_insts_def,DROP_LENGTH_APPEND,run_inst_seq_def,
       step_inst_base_opcode_eqs,eval_operand_def]) >>
  `stmt_state_rel ctx func ce cx es u` by
    metis_tac[stmt_state_rel_inst_idx] >>
  `w2n w = b` by gvs[] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x raw = lookup_var x s`
       (qspec_then `x` mp_tac) >> simp[lookup_var_def]) >>
  `typed_copy_state_frame sm b sz u r` by
    (simp_tac bool_ss [typed_copy_state_frame_def,typed_copy_frame_def] >>
     conj_tac >- gvs[venom_state_component_equality] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     metis_tac[gas_marked_path_def,gas_path_mem_memory_length]) >>
  suspend "restore"
QED

Resume immutable_normalized_actual_state[restore]:
  `stmt_state_rel ctx func ce cx es r` by
    (irule place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     qexistsl_tac [`sz`, `mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sm.cs_next_var)]`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     rename1 `local_region ce es.scopes u name lb lsz` >>
     qpat_x_assum `!name q k. local_region _ _ raw _ _ _ ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `local_region ce es.scopes u name lb lsz` mp_tac >>
     fs[local_region_def,lookup_var_def,loweringStateRelDefsTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def]) >>
  `r.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `_ = u` (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP r.vs_allocas aid = SOME entry` by
    (rpt strip_tac >>
     qpat_x_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
       (qspecl_then [`aid`,`entry`] mp_tac) >> simp[]) >>
  simp[] >> irule alloca_frame_of_mem_frame >> simp[] >>
  reverse conj_tac >- metis_tac[lookup_var_def] >> rpt strip_tac >>
  rename1 `mem_bytes_at off len r.vs_memory = _` >>
  `regions_disjoint b sz off len` by
    (qpat_x_assum `!aid q k. aid < sm.cs_next_id /\ _ ==> _`
      (qspecl_then [`aid`,`off`,`len`] mp_tac) >> simp[]) >>
  first_x_assum irule >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def,
     venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Finalise immutable_normalized_actual_state[local]

Theorem immutable_assign_normalized_mem_stmt_post:
  compile_assign_value ce (Lit (n2w off)) LocCode src F sl dty sty
    (type_memory_bytes ce dty) sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  expr_val_at ce cx sty sa sm es v src s /\ expr_val_rel cx sty v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  immutable_value_admissible dtv v /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  0 < type_memory_size dtv /\ type_memory_size dtv MOD 32 = 0 /\
  type_memory_size dtv < dimword (:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand src s = SOME p /\
  (!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sm x) /\
  off + type_memory_size dtv <= s.vs_alloca_next /\
  off + type_memory_size dtv < dimword (:256) /\
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
     regions_disjoint off (type_memory_size dtv) q k) /\
  expr_sim_inv ce cx env es /\ ce.ce_is_ctor /\ ~block_is_terminated sb /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME dty /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),fin)
  ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_post ctx func cx lctx ce ce sm sb es s (INL ()) fin t /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce dty = type_memory_size dtv` by metis_tac[] >>
  drule_all immutable_normalized_compiler_parts_option >> strip_tac >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size dtv`,
    `imm` |-> `ce.ce_imm_alloca`, `dst` |-> `Lit (n2w off)`]
    immutable_normalized_phi_boundary) >> simp[] >> disch_then assume_tac >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   (!x. src = Var x \/ Lit (n2w off) = Var x ==> not_fresh_at sm x)` by
    simp[eval_operand_def] >>
  drule_all immutable_assign_normalized_mem_path_endpoint >>
  disch_then (qx_choose_then `buf1` (qx_choose_then `mid1`
    (qx_choose_then `sn1` (qx_choose_then `u` (qx_choose_then `r`
      (qx_choose_then `t` (qx_choose_then `b`
        (map_every assume_tac o CONJUNCTS)))))))) >>
  `buf1 = buf /\ mid1 = mid` by
    (qpat_assum `compile_alloc_buffer _ sm = (buf,mid)` mp_tac >>
     qpat_assum `compile_alloc_buffer _ sm = (buf1,mid1)` mp_tac >>
     qpat_assum `type_memory_bytes ce dty = type_memory_size dtv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_x_assum `buf1 = buf` SUBST_ALL_TAC >>
  qpat_x_assum `mid1 = mid` SUBST_ALL_TAC >>
  `sn1 = sn` by
    (qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = ((),sn)` mp_tac >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = ((),sn1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_x_assum `sn1 = sn` SUBST_ALL_TAC >>
  qpat_assum `type_memory_bytes ce dty = type_memory_size dtv`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all immutable_normalized_code_windows_option >> strip_tac >>
  `u.vs_inst_idx = LENGTH mid.cs_current_insts` by
    (qpat_assum `_ = u` (mp_tac o Q.AP_TERM `\z. z.vs_inst_idx`) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  drule_all immutable_normalized_actual_state >> strip_tac >>
  suspend "suffix"
QED

Resume immutable_assign_normalized_mem_stmt_post[suffix]:
  `ci_mono sm mid` by metis_tac[ci_mono_compile_alloc_buffer,SND] >>
  `ci_mono mid sn` by metis_tac[cj 1 ci_mono_typed_memory_family,SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_trans] >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (qpat_assum `ci_mono sm sn` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `LENGTH r.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[gas_marked_path_def,gas_path_mem_memory_length] >>
  `(t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
    vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r` by
    (qpat_assum `t = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[venom_state_component_equality]) >>
  `!a k. regions_disjoint a k off (type_memory_size dtv) ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k r.vs_memory` by
    (qpat_assum `!q k. q+k <= off \/ off+type_memory_size dtv <= q ==> _`
       mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> metis_tac[ADD_COMM]) >>
  `stmt_post ctx func cx lctx ce ce sn sb es r (INL ()) fin t` by
    (`t with vs_inst_idx := LENGTH sb.cs_current_insts = t` by
       (qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality]) >>
     pop_assum (fn th => ONCE_REWRITE_TAC[GSYM th]) >>
     irule immutable_assign_suffix_stmt_post >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`env`,`id`,`dtv`,`dty`,`off`,`v`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule stmt_post_entry_frame >> qexistsl_tac [`es`,`r`,`sn`] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> conj_tac
    >- metis_tac[compiler_ci_mono_not_fresh] >> metis_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise immutable_assign_normalized_mem_stmt_post
