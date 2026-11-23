Theory bodyFullNameWord
Ancestors
  bodySimFull gasOutcomeFullCompose bodyFullGhostFrame bodyPtrMakeArrayMloadFrame
  bodyNameWordTypeMemory bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimNameValue exprSimNameWord
  exprSimProps entryDecodeStaticProps
  exprLoweringProps exprLowering loweringSlice loweringPosts bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr exprPtrCtorImmStore wordLoadStorePtr
  representationCleanPtr valueEncodingProps vyperStorageTrace
  venomExecSemantics venomInst venomState vyperInterpreter vyperState
  vyperAST vyperTyping finite_map list words emitHelper compileEnv fragExec
  instMemFrontier fragExecMem bodyMemoryDefs memSafeRun
  exprSimFullBundleProps emitHelperProps fragGasOrigin

Theorem name_word_ghost_inputs[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel H ctx func ce cx es s /\
  ghost_inv_at D lo d ce cx es G tn s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
    mload (w2n w) s = typed_val_to_w256 entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all body_name_source_region >> strip_tac >>
  `type_memory_size entry.type = 32` by metis_tac[word_type_memory_size] >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (gvs[ghost_inv_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n w) mem = typed_val_to_w256 entry.type entry.value` by
    metis_tac[val_in_memory_word_type] >>
  drule robust_mem_word_at_clean >> strip_tac >>
  qexistsl [`entry`, `p`, `sz`, `w`] >>
  simp[] >> conj_tac >- (gvs[ptr_covers_def]) >>
  metis_tac[mem_word_at_eq_mload, mem_agree_outside_def]
QED

Theorem name_word_full_ghost_frame[local]:
  lower_value compile_expr ce ty (Name ann id) sa = (Var out,sb) /\
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv_at D lo d ce cx (es with gas_obs := [])
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s (update_var out w s) tn)
    (update_var out w s with vs_inst_idx := k) /\
  ghost_kept_at lo ce es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      simp[mload_ghost_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[mload_ghost_frame]) >>
  simp[ghost_kept_at_def, mload_ghost_frame] >> metis_tac[mload_ghost_frame]
QED

(* Expose the actual fetched edge and its posts before either the ordinary
   or the confined outcome packages that edge as a path. *)
Theorem name_word_full_edge:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  storage_trace_domain cx st0 es.storage_trace ==>
  ?v t G tn bb inst.
    (!tail. bind (eval_expr cx (Name ann id)) (read_result cx)
              (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
    ~(s0.vs_current_bb = sb.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sb.cs_current_insts) /\
    lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s0.vs_inst_idx = SOME inst /\
    sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_edge (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) [] (OK t,G,tn) /\
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Name ann id)
        (es,sa,sb,s0,op,G0,tn0) H (INL v : (value,exception) sum)
        (es with gas_obs := []) G tn t
Proof
  rw[expr_sim_full_hypotheses_def,expr_sim_full_code_def] >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  first_assum drule >> strip_tac >>
  drule_all body_name_wordtype_counted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_history func t` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MLOAD [Var p] [out]` >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 entry.type entry.value) s0` >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ [inst]` by gvs[Abbr `inst`] >>
  qpat_x_assum `sb.cs_current_insts = _ ++ [mk_inst _ _ _ _]` kall_tac >>
  `LENGTH sb.cs_current_insts = SUC s0.vs_inst_idx` by simp[] >>
  `sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id` by
    simp[Abbr `inst`,mk_inst_def] >>
  drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qexistsl_tac [`entry.value`,`t`,`step_prov PG G0 inst u`,
               `step_taint inst s0 u tn0`,`bb`,`inst`] >>
  conj_tac
  >- (gen_tac >> qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
       mp_tac eval_name_word >> simp[vyperStateTheory.bind_def]) >>
  simp[expr_sim_full_post_def,expr_sim_full_endpoint_def] >>
  (`~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = SUC (LENGTH sa.cs_current_insts) /\
    t.vs_alloca_next = s0.vs_alloca_next` by simp[Abbr `t`,Abbr `u`,update_var_def]) >>
  simp[vyperASTTheory.expr_type_def] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> rpt conj_tac >>
  all_tac >~ [`gas_origin_ptr_edge _ _ _ _`]
  >- suspend "name_load_edge" >>
  all_tac >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- (drule_all body_name_wordtype_post >>
      disch_then (qspec_then `entry.value` mp_tac) >>
      simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  all_tac >~ [`expr_store_bound _ _ _ _ _`]
  >- simp[exprSimMemDefsTheory.expr_store_bound_def, vyperASTTheory.expr_type_def] >>
  qpat_x_assum `op = Var out` SUBST_ALL_TAC >>
  drule_all name_word_full_ghost_frame >>
  disch_then (qspecl_then [`typed_val_to_w256 entry.type entry.value`,
                          `LENGTH sb.cs_current_insts`, `PG`] strip_assume_tac) >>
  fs[Abbr `t`, Abbr `u`, Abbr `inst`, update_var_def, arithmeticTheory.ADD1,
     vyperASTTheory.expr_type_def] >>
  drule_all name_word_ghost_inputs >> strip_tac >> gvs[] >>
  simp[ptr_val_ok_def] >>
  conj_tac
  >- (qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
      irule (SRULE [update_var_def] (cj 1 mload_ghost_clean)) >>
      simp[eval_operand_def] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT]
QED

Resume name_word_full_edge[name_load_edge]:
  `allocas_from lo s0` by metis_tac[ghost_inv_at_def] >>
  drule_all name_word_ghost_inputs >> strip_tac >> gvs[Abbr `inst`] >>
  `inst_mem_below_frontier
    (mk_inst sa.cs_next_id MLOAD [Var p] [STRING #"%" (toString sa.cs_next_var)]) s0` by
    metis_tac[body_wordtype_name_MLOAD_frontier] >>
  `ptr_inst_ok (DF H) lo 0 ctx func G0 tn0
    (mk_inst sa.cs_next_id MLOAD [Var p] [STRING #"%" (toString sa.cs_next_var)]) s0` by
    (irule ptr_inst_ok_mload_lo >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def,
       Abbr `t`, Abbr `u`, update_var_def]
QED

Finalise name_word_full_edge

Theorem name_word_full:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  strip_tac >> simp[expr_sim_full_via_bundle] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
                   storage_trace_frame_read_result] >>
  `~s0.vs_halted` by fs[expr_sim_full_hypotheses_def] >>
  simp[] >> strip_tac >> drule_all name_word_full_edge >> strip_tac >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G`,`es`,`INL v`,`t`,`tn`] >> simp[] >>
  gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t,G,tn) [] (OK t,G,tn)` by simp[gas_origin_ptr_path_rules] >>
  drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED
