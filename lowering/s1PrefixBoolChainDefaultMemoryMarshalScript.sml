(* The non-stack singleton default allocates a slot and stores the raw GAS word. *)
Theory s1PrefixBoolChainDefaultMemoryMarshal
Ancestors
  s1PrefixIntCallStageSingleton bodyFullAllocaFresh bodyFullHashAllocFrame
  bodyFullHashKeccakFixed bodyFullAbiEncodeStore exprSimAlloc wordLoadStorePtr
  typedCopyOriginPtrDynArray exprPtrUnwrapCopyEdges fragGasOriginPtrLoop
  bodyPtrDefs gasShadowCompileCallSupport vyperTypeSystem vyperStorageFootprint
  exprLowering exprLoweringProps compileEnv emitHelperProps loweringHalt fragExec
  fragGasOriginPtrExec loweringStateRelDefs bodyFullPathHistory stateRelProj
  venomInst venomState venomExecSemantics venomMemProps ptrDiscipline
  unitTransformDefs memSafeRun codegenRel contextCodegenRel pred_set words finite_map pair

Theorem msggas_memory_singleton_cut[local]:
  compile_stage_intcall_args
    (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out))) ce
    [e] [F] [env_item_type MsgGas] cg = ([h],cm) /\
  fn_has_code cg cm func ==>
  ?buf ca. compile_alloc_buffer 32 cg = (buf,ca) /\
    h = buf.buf_operand /\ emit_void MSTORE [h;Var out] ca = ((),cm) /\
    fn_has_code cg ca func /\ fn_has_code ca cm func
Proof
  Cases_on `compile_alloc_buffer 32 cg` >> rename1 `_ = (buf,ca)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand;Var out] ca` >>
  rename1 `emit_void MSTORE _ _ = (unit_result,cb)` >> Cases_on `unit_result` >>
  simp[compile_stage_intcall_args_def, env_item_type_def, is_word_type_def,
       type_memory_bytes_def, unwrap_value_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  `cs_extends cg ca` by metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, SND] >>
  `cs_extends ca cb` by metis_tac[ci_mono_emit_void, ci_mono_def, SND] >>
  metis_tac[fn_has_code_split]
QED

Theorem bool_chain_default_msggas_memory_marshal:
  compile_stage_intcall_args
    (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out))) ce
    [Builtin (env_item_type MsgGas) (Env MsgGas) []] [F] [dt] cg = ([h],cm) /\
  compile_stage_intcall_args
    (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out)))
    (gas_shadow_env T ce)
    [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
    [F] [dt] sh_cg = ([h],sh_cm) /\
  type_widens_to (get_tenv cx) (env_item_type MsgGas) dt /\ is_word_type dt /\
  fn_has_code cg cm func /\ fn_has_code sh_cg sh_cm sh_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce cg /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at cg x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at cg x) /\
  alloca_history func u /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es u /\
    ghost_inv_at (DF H) lo d ce cx es G1 tn1 u) /\
  ~u.vs_halted /\ u.vs_current_bb = cg.cs_current_bb /\
  u.vs_inst_idx = LENGTH cg.cs_current_insts /\ u.vs_gas_readings = ws /\
  not_fresh_at cg out /\ eval_operand (Var out) u = SOME w /\
  op_taint tn1 (Var out) = {} ==>
  ?t G2 tn2 q a.
    h = Var q /\ eval_operand h t = SOME a /\
    ptr_covers G2 tn2 q t 32 /\ mload (w2n a) t = w /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn2.t_mem) /\
    (!mem. mem_agree_outside tn2.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (UintT 256)) (IntV (&w2n w)) (w2n a) mem) /\
    FLOOKUP t.vs_allocas cg.cs_next_id = SOME (w2n a,32) /\
    ~t.vs_halted /\ t.vs_current_bb = cm.cs_current_bb /\
    t.vs_inst_idx = LENGTH cm.cs_current_insts /\ t.vs_gas_readings = ws /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,G1,tn1) [] (OK t,G2,tn2) /\
      stmt_state_rel H ctx func ce cx es t /\
      ghost_inv_at (DF H) lo d ce cx es G2 tn2 t) /\
    ghost_kept_at lo ce es cg G1 tn1 u G2 tn2 /\
    (?sh_buf sh_ca. compile_alloc_buffer 32 sh_cg = (sh_buf,sh_ca) /\
      h = sh_buf.buf_operand /\ emit_void MSTORE [h;Var out] sh_ca = ((),sh_cm) /\
      fn_has_code sh_cg sh_ca sh_func /\ fn_has_code sh_ca sh_cm sh_func)
Proof
  strip_tac >>
  `dt = env_item_type MsgGas` by metis_tac[type_widens_to_word] >>
  qpat_x_assum `dt = _` SUBST_ALL_TAC >>
  qpat_assum `compile_stage_intcall_args _ ce _ _ _ cg = _`
    (mp_then Any mp_tac msggas_memory_singleton_cut) >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`buf`,`ca`] strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
         fcpTheory.index_one, fcpTheory.finite_one] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn1`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`]
    (qx_choosel_then [`q`,`a`,`v`,`Ga`,`tna`,`r`] strip_assume_tac)) >>
  `~v.vs_halted /\ v.vs_gas_readings = ws` by
    (qpat_assum `_ = u` (mp_tac o Q.AP_TERM `\s. (s.vs_halted,s.vs_gas_readings)`) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es v` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `eval_operand (Var out) v = SOME w /\ op_taint tna (Var out) = {}` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  suspend "store"
QED

Resume bool_chain_default_msggas_memory_marshal[store]:
  `emit_inst MSTORE [Var q;Var out] [] ca = ((),cm)` by
    gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
  drule emit_inst_extends >> strip_tac >>
  qabbrev_tac `i = mk_inst ca.cs_next_id MSTORE [Var q;Var out] []` >>
  qabbrev_tac `z = mstore (w2n a) w v` >>
  qabbrev_tac `t = z with vs_inst_idx := SUC v.vs_inst_idx` >>
  qabbrev_tac `tz = step_taint i v z tna` >>
  `step_inst_base i v = OK z` by
    (qunabbrev_tac `i` >> qunabbrev_tac `z` >> irule step_MSTORE >>
     qpat_assum `eval_operand (Var out) v = _` mp_tac >>
     qpat_assum `lookup_var q v = _` mp_tac >> simp[eval_operand_def]) >>
  `step_prov PG Ga i z = Ga /\ tz.t_var = tna.t_var /\
   tz.t_mem = tna.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}` by
    (simp[Abbr `i`, Abbr `z`, Abbr `tz`] >> drule_all mstore_ghost_frame >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (v,Ga,tna) [] (OK t,Ga,tz)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (v,Ga,tna) [] (OK t,step_prov PG Ga i z,tz)` suffices_by simp[] >>
     map_every qunabbrev_tac [`t`,`tz`,`i`] >>
     irule typed_copy_emit_inst_origin_ptr_path >>
     `lookup_var out v = SOME w` by fs[eval_operand_def] >>
     qpat_x_assum `v = r with vs_inst_idx := _` kall_tac >>
     qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
     qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
     simp[is_terminator_def, inst_dload_in_section_def,
          instMemFrontierTheory.below_frontier_MSTORE, eval_operand_def,
          SimpLHS, mk_inst_def] >>
     rewrite_tac[GSYM mk_inst_def] >>
     irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (u,G1,tn1) [] (OK t,Ga,tz)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Ga`,`v`,`tna`] >> simp[]) >>
  `alloca_history func t` by
    (`alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) [] (OK t,Ga,tz)`
       (qspec_then `ARB` (mp_then Any irule body_full_path_alloca_history)) >> simp[]) >>
  suspend "state_and_ghost"
QED

Resume bool_chain_default_msggas_memory_marshal[state_and_ghost]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  `q = STRING #"%" (toString cg.cs_next_var)` by metis_tac[operand_11] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `lo <= w2n a` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst cg.cs_next_id ALLOCA [Lit 32w] [q]) u = OK r` by
    (`emitted_insts cg ca = [mk_inst cg.cs_next_id ALLOCA [Lit 32w] [q]]` by
      (drule compile_alloc_buffer_emission >> strip_tac >>
       drule emitted_insts_emit_inst >> simp[emitted_insts_def] >> strip_tac >> gvs[]) >>
     qpat_assum `run_inst_seq _ u = _` mp_tac >>
     qpat_assum `emitted_insts cg ca = _` (fn th => rewrite_tac[th,run_inst_seq_def]) >>
     Cases_on `step_inst_base (mk_inst cg.cs_next_id ALLOCA [Lit 32w] [q]) u` >> simp[]) >>
  `ghost_kept_at lo ce es cg G1 tn1 u Ga tna` by
    (qpat_assum `Ga = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_assum `tna = step_taint _ _ _ _` SUBST1_TAC >>
     irule (INST_TYPE [alpha |-> ``:256``] hash_compile_alloc_entry_kept_at) >> simp[] >>
     qexistsl [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es v /\ ghost_inv_at (DF H) lo d ce cx es Ga tna v` by
    (rpt strip_tac >- metis_tac[] >>
     qpat_x_assum `v = r with vs_inst_idx := _` kall_tac >>
     qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
     qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >> simp[] >>
     qexistsl [`G1`,`H`,`ctx`,`w2n a + 32`,`func`,`u`,`cg`,`tn1`] >>
     simp[] >> qpat_assum `_ = u` mp_tac >> simp[venom_state_component_equality]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t` by
    (rpt strip_tac >> qpat_x_assum `v = r with vs_inst_idx := _` kall_tac >>
     simp[Abbr `t`,Abbr `z`,stmt_state_rel_inst_idx] >>
     irule literal_mstore_state_rel >> simp[] >>
     qexistsl [`w2n a`,`mk_inst cg.cs_next_id ALLOCA [Lit 32w] [q]`,`32`] >>
     simp[mk_inst_def] >> rewrite_tac[GSYM mk_inst_def] >>
     qpat_assum `!name b len. local_region ce es.scopes v name b len ==> _`
       mp_tac >> simp[regions_disjoint_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx es Ga tz t /\
    ghost_kept_at lo ce es cg G1 tn1 u Ga tz` by
    (rpt gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func ce cx es v /\ ghost_inv_at (DF H) lo d ce cx es Ga tna v`
       by metis_tac[] >>
     `local_ptrs_rel func ce es.scopes v` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     qpat_x_assum `v = r with vs_inst_idx := _` kall_tac >>
     map_every qunabbrev_tac [`t`,`tz`,`z`,`i`] >>
     drule_all abi_encode_mstore_frame_at >>
     disch_then (qspec_then `ca.cs_next_id` strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "representation"
QED

Resume bool_chain_default_msggas_memory_marshal[representation]:
  qpat_x_assum `v = r with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
  `mload (w2n a) t = w` by
    simp[Abbr `t`, Abbr `z`, abiEncoderPathPropsTheory.mload_inst_idx, mload_mstore_same] >>
  `!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tz.t_mem` by simp[] >>
  `!mem. mem_agree_outside tz.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (UintT 256)) (IntV (&w2n w)) (w2n a) mem` by
    (rpt strip_tac >> drule_all logStoreDataOriginPtrTheory.mem_agree_outside_window >>
     simp[valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.val_to_w256_def,
          valueEncodingDefsTheory.mem_word_at_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
     qpat_x_assum `mload (w2n a) t = _` mp_tac >>
     simp[mload_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
     strip_tac >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `ghost_kept_at lo ce es cg G1 tn1 u Ga tz` by metis_tac[] >>
  `h = Var q` by metis_tac[] >>
  qpat_x_assum `buf.buf_operand = Var (STRING _ _)` kall_tac >>
  qpat_x_assum `q = STRING _ _` kall_tac >>
  `eval_operand (Var q) t = SOME a` by
    (qpat_x_assum `lookup_var q v = _` mp_tac >>
     simp[Abbr `t`, Abbr `z`, mstore_def, eval_operand_def, lookup_var_def]) >>
  `ptr_covers Ga tz q t 32` by
    (qpat_x_assum `ptr_covers Ga tna q v 32` mp_tac >>
     simp[Abbr `t`, Abbr `z`, mstore_def, ptr_covers_def, lookup_var_def, op_taint_def]) >>
  qexistsl [`t`,`Ga`,`tz`,`q`,`a`] >> simp[] >>
  simp[Abbr `t`, Abbr `z`, mstore_def, arithmeticTheory.ADD1] >>
  qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr _] [F] _ sh_cg = ([h],sh_cm)`
    (mp_then Any mp_tac msggas_memory_singleton_cut) >>
  disch_then (qspec_then `sh_func` mp_tac) >> simp[]
QED

Finalise bool_chain_default_msggas_memory_marshal
