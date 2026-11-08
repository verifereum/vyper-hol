(* Continuing scalar event encoder frame; allocation resources live below the runner. *)
Theory stmtSimLogEncodeFrame
Ancestors
  stmtSimLogScalarEncode stmtSimLogAllocResource stmtSimLogEncodeFields
  stmtSimLogExecFields localPtrsProps loweringSlice abiDecoderFrame
  valueEncodingProps compileEnv loweringStateRelDefs exprLoweringProps venomState venomMemProps
  venomExecSemantics venomInst venomMemDefs abiBuiltinAllocation finite_map words list arithmetic

Theorem log_encode_local_frame[local]:
  local_ptrs_rel func ce scopes s /\
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_footprint_frame fp s t /\
  (!name lo sz. local_region ce scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) ==>
  local_ptrs_rel func ce scopes t
Proof
  strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `s` >>
  asm_simp_tac bool_ss [] >>
  (reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> rpt gen_tac >> strip_tac >>
  `local_region ce scopes s name (w2n w) sz` by
    (simp[local_region_def] >> qexistsl_tac [`entry`,`p`,`w`] >> simp[]) >>
  `abi_footprint_disjoint (w2n w) sz fp` by metis_tac[] >>
  `mem_bytes_at (w2n w) sz t.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by
    (irule abi_decode_footprint_frame_slice >> goal_assum (drule_at Any) >> simp[]) >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`sz`,`s.vs_memory`] >> simp[]
QED

Theorem log_encode_immutable_frame[local]:
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
  abi_decode_footprint_frame fp s t /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) ==>
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- fs[abi_decode_footprint_frame_def] >>
  rpt strip_tac >> irule abi_decode_footprint_frame_slice >>
  qexists_tac `fp` >> simp[] >> first_x_assum drule_all >> simp[]
QED

Theorem log_encode_step_memory_mono[local]:
  log_encode_safe_opcode i.inst_opcode /\ step_inst_base i s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp_tac bool_ss [log_encode_safe_opcode_def] >> strip_tac
  >- gvs[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs(), update_var_def]
  >- gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs(), update_var_def]
  >- gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs(), update_var_def]
  >- gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs(), update_var_def]
  >- (gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
      simp[mstore_memory_nondecreasing])
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs(), mcopy_def] >>
      simp[write_memory_with_expansion_nondecreasing])
  >- gvs[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs(), update_var_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[write_memory_with_expansion_nondecreasing]
QED

Theorem log_encode_run_memory_mono:
  !code s t. EVERY (\i. log_encode_safe_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==> LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all log_encode_step_memory_mono >> strip_tac >>
  first_x_assum drule_all >> decide_tac
QED

Theorem log_encode_state_frame[local]:
  state_rel func ce cx es s /\ log_encode_external t = log_encode_external s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_footprint_frame fp s t /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) ==>
  state_rel func ce cx es t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `local_ptrs_rel func ce es.scopes s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s` by
    fs[state_rel_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (irule log_encode_local_frame >> qexistsl_tac [`fp`,`s`] >>
     asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t` by
    (irule log_encode_immutable_frame >> qexistsl_tac [`fp`,`s`] >>
     asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule log_encode_external_fields >> strip_tac >>
  irule state_rel_frame >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`es`,`s`] >> asm_simp_tac (srw_ss()) []
QED

Theorem log_encode_local_region_frame[local]:
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) ==>
  (local_region ce scopes t name lo sz <=> local_region ce scopes s name lo sz)
Proof
  strip_tac >> simp[local_region_def] >>
  eq_tac >> strip_tac >> qexistsl_tac [`entry`,`p`,`w`] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem log_encode_immutable_sep_frame[local]:
  immutable_alloca_sep func ce cx es s /\
  (!name lo sz. local_region ce es.scopes t name lo sz ==>
    local_region ce es.scopes s name lo sz) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  immutable_alloca_sep func ce cx es t
Proof
  strip_tac >> drule immutable_alloca_sep_frame >> disch_then irule >>
  rpt conj_tac >> TRY (fs[] >> NO_TAC) >> rpt strip_tac
  >~ [`FLOOKUP _.vs_allocas _ = SOME _ \/ _`]
  >- (Cases_on `FLOOKUP s.vs_allocas aid` >> res_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem log_encode_allocate_metadata[local]:
  !site n s. (abi_builtin_allocate_state site n s).vs_alloca_next >= s.vs_alloca_next /\
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==>
    FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas id = SOME r) /\
  (!id b sz. FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas id = SOME (b,sz) /\
    FLOOKUP s.vs_allocas id = NONE ==> s.vs_alloca_next <= b)
Proof
  rpt gen_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `id = site` >> gvs[]
QED

Theorem log_encode_allocate_inv[local]:
  alloca_inv s ==> alloca_inv (abi_builtin_allocate_state site n s)
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def] >>
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    FLOOKUP_UPDATE] >> gvs[AllCaseEqs()]
  >- (disj2_tac >> first_x_assum irule >> goal_assum (drule_at Any))
  >- (disj1_tac >> first_x_assum irule >> goal_assum (drule_at Any))
  >- (qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> simp[]) >>
  first_x_assum drule_all >> decide_tac
QED

Theorem log_encode_allocate_sizes[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) ==>
  !i v b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit v] /\
    FLOOKUP (abi_builtin_allocate_state inst.inst_id n s).vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n v
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id = NONE` >>
  asm_simp_tac (srw_ss()) [abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac
  >- (Cases_on `i.inst_id = inst.inst_id`
      >- (`i = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[w2n_n2w]) >>
      gvs[] >> fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[]) >>
  fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[]
QED

Theorem log_encode_allocation_frame[local]:
  stmt_state_rel ctx func ce cx es s /\ state_rel func ce cx es t /\
  immutable_alloca_sep func ce cx es t /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) /\
  t.vs_allocas = (abi_builtin_allocate_state inst.inst_id n s).vs_allocas /\
  t.vs_alloca_next = (abi_builtin_allocate_state inst.inst_id n s).vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ immutable_base_zero ce t ==>
  stmt_state_rel ctx func ce cx es t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv s /\ alloca_room ctx func s /\ fmp_room ctx func s` by
    fs[stmt_state_rel_def] >>
  `alloca_inv (abi_builtin_allocate_state inst.inst_id n s)` by
    (irule log_encode_allocate_inv >> simp[]) >>
  `alloca_room ctx func (abi_builtin_allocate_state inst.inst_id n s)` by
    (irule log_event_buffer_room >> goal_assum (drule_at Any) >> simp[]) >>
  simp_tac bool_ss [stmt_state_rel_def] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (irule alloca_inv_fields >>
      qexists_tac `abi_builtin_allocate_state inst.inst_id n s` >> simp[]) >>
  conj_tac
  >- (irule alloca_room_fields >>
      qexists_tac `abi_builtin_allocate_state inst.inst_id n s` >> simp[]) >>
  conj_tac
  >- (`fmp_room ctx func (abi_builtin_allocate_state inst.inst_id n s)` by
        metis_tac[log_event_buffer_fmp_room] >>
      `(abi_builtin_allocate_state inst.inst_id n s).vs_fmp = s.vs_fmp` by
        rw[abi_builtin_allocate_state_def] >>
      irule fmp_room_fields >>
      qexists_tac `abi_builtin_allocate_state inst.inst_id n s` >> gvs[]) >>
  rpt strip_tac >> drule_all log_encode_allocate_sizes >> simp[]
QED

Theorem log_encode_continuation:
  stmt_state_rel ctx func ce cx es s /\
  log_encode_external t = log_encode_external s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> lookup_var x t = lookup_var x s) /\
  abi_decode_footprint_frame fp s t /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) /\
  t.vs_allocas = (if dyn then abi_builtin_allocate_state site n s else s).vs_allocas /\
  t.vs_alloca_next = (if dyn then abi_builtin_allocate_state site n s else s).vs_alloca_next /\
  (dyn ==> fn_inst_ids_distinct func /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w n)] /\ inst.inst_id = site /\ n < dimword (:256)) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `(!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP t.vs_allocas aid = SOME r) /\
   (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
     FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
   s.vs_alloca_next <= t.vs_alloca_next` by
    (Cases_on `dyn` >> gvs[] >>
     qspecl_then [`inst.inst_id`,`n`,`s`] mp_tac (GEN_ALL log_encode_allocate_metadata) >>
     simp[] >> metis_tac[]) >>
  `state_rel func ce cx es s /\ immutable_alloca_sep func ce cx es s` by
    fs[stmt_state_rel_def] >>
  `state_rel func ce cx es t` by
    (qpat_x_assum `t.vs_allocas = _` kall_tac >>
     qpat_x_assum `t.vs_alloca_next = _` kall_tac >>
     irule log_encode_state_frame >> qexistsl_tac [`fp`,`s`] >>
     asm_simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_alloca_sep func ce cx es t` by
    (qpat_x_assum `t.vs_allocas = _` kall_tac >>
     qpat_x_assum `t.vs_alloca_next = _` kall_tac >>
     `!name lo sz. local_region ce es.scopes t name lo sz ==>
       local_region ce es.scopes s name lo sz` by
       (drule log_encode_local_region_frame >> metis_tac[]) >>
     irule log_encode_immutable_sep_frame >> qexists_tac `s` >>
     asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_base_zero ce t` by
    (`immutable_base_zero ce s` by fs[stmt_state_rel_def] >>
     irule exprLoweringPropsTheory.immutable_base_zero_frame >>
     qexists_tac `s` >>
     qpat_x_assum `log_encode_external t = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_labels`) >>
     simp[log_encode_external_def]) >>
  Cases_on `dyn` >> gvs[]
  >- (irule log_encode_allocation_frame >> asm_simp_tac bool_ss [] >>
      qexistsl_tac [`inst`,`n`,`s`] >> simp[] >>
      qpat_x_assum `log_encode_external t = _`
        (mp_tac o Q.AP_TERM `\x. x.vs_fmp`) >>
      simp[log_encode_external_def]) >>
  irule stmt_state_rel_allocas_frame >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`es`,`s`] >> simp[] >>
  qpat_x_assum `log_encode_external t = _`
    (mp_tac o Q.AP_TERM `\x. x.vs_fmp`) >>
  simp[log_encode_external_def]
QED

Theorem log_encode_local_operands[local]:
  stmt_state_rel ctx func ce cx es s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_decoder_operand_live nv (Var p)) /\
  (!op w. abi_decoder_operand_live nv op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  !name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp_tac bool_ss [local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `abi_decoder_operand_live nv (Var p)` by metis_tac[] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def]
QED

Theorem log_scalar_tuple_continue:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db)) /\
  stmt_state_rel ctx func ce cx es initial /\
  (!name entry v sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
    abi_decoder_operand_live st.cs_next_var (Var v)) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==>
    abi_decoder_operand_live st.cs_next_var (Var x)) /\
  (!name lo sz. local_region ce es.scopes initial name lo sz ==>
    abi_footprint_disjoint lo sz
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else []))) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv)
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else []))) /\
  ((?infos. ei = AbiComplex infos) ==> fn_inst_ids_distinct func /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w 32)] /\ inst.inst_id = st.cs_next_id) ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_scalar_tuple_run >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st end_st)` by
    (irule log_scalar_encode_safe >> goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `log_encode_external actual = log_encode_external initial` by
    (irule log_encode_run_external >> goal_assum (drule_at Any) >> simp[]) >>
  `LENGTH initial.vs_memory <= LENGTH actual.vs_memory` by
    (irule log_encode_run_memory_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `!name entry v sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
    lookup_var v actual = lookup_var v initial` by
    (match_mp_tac (Q.INST [`nv` |-> `st.cs_next_var`] log_encode_local_operands) >>
     asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==> lookup_var x actual = lookup_var x initial` by
    (rpt strip_tac >>
     `immutable_base_zero ce initial` by fs[stmt_state_rel_def] >>
     `eval_operand (Var x) initial = SOME 0w` by fs[immutable_base_zero_def] >>
     `eval_operand (Var x) actual = SOME 0w` by metis_tac[] >>
     fs[eval_operand_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule log_encode_continuation >>
  qexistsl_tac [`(?infos. ei = AbiComplex infos)`,
    `(db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])`,
    `32`,`initial`,`st.cs_next_id`] >>
  asm_simp_tac (srw_ss()) [] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> qpat_x_assum `_ ==> fn_inst_ids_distinct func /\ _` mp_tac >> simp[] >>
  strip_tac >> qexists_tac `inst` >> simp[dimword_def]
QED
