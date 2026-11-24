(* The linked value post of the single MLOAD emitted for a word local. *)
Theory bodyLocalNameWordReadMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrMakeArrayMloadFrame
  bodyNameWordTypeMemory bodyMemoryDefs stateRelProj exprSimProps
  emitHelperProps exprLoweringProps bodyInvSplit representationCleanPtr
  fragGasSeqPtr fragGasOriginPtr exprPtrCtorImmStore wordLoadStorePtr
  fragExec memSafeRun unitTransformDefs
  ptrDiscipline bodyPtrDefs allocaHistory venomExecSemantics venomInst venomState
  exprSimMemDefs loweringStateRelDefs loweringPosts valueEncodingProps loweringSlice
  vyperState vyperStorageFootprint vyperAST finite_map arithmetic list

Theorem local_name_mload_immutable[local]:
  immutable_frame_mods func ce cx es s /\
  (!id p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  immutable_frame_mods func ce cx (es with gas_obs := [])
    (update_var out word s with vs_inst_idx := k)
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def, update_var_def]) >>
  simp[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`, `es`] >> simp[update_var_def] >>
  reverse conj_tac
  >- (qpat_x_assum `immutable_alloca_sep_mods _ _ _ _ _` mp_tac >>
      simp[immutable_alloca_sep_mods_def]) >>
  simp[local_region_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> qexists_tac `id` >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem local_name_mload_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  let i = mk_inst iid MLOAD [Var p] [out];
      u = update_var out word s;
      G' = step_prov PG G i u;
      tn' = step_taint i s u tn
  in ghost_inv_at_mods D lo d ce cx (es with gas_obs := []) G' tn'
       (u with vs_inst_idx := k) /\
     ghost_kept_at lo ce es sa G tn s G' tn'
Proof
  strip_tac >> `!x. not_fresh_at sa x ==> x <> out` by metis_tac[] >>
  simp[ghost_kept_at_def, mload_ghost_frame] >>
  qmatch_goalsub_abbrev_tac `step_prov PG G i u` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  qabbrev_tac `t = u with vs_inst_idx := k` >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    simp[Abbr `tn'`, Abbr `i`, Abbr `u`, mload_ghost_frame] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `t`, Abbr `G'`, Abbr `tn'`, Abbr `u`, Abbr `i`,
                          mload_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!x sz. not_fresh_at sa x ==> (ptr_covers G' tn' x t sz <=> ptr_covers G tn x s sz)` by
    simp[ptr_covers_def] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by simp[Abbr `t`, Abbr `u`, update_var_def] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> simp[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> rpt strip_tac >>
      `not_fresh_at sa x` by metis_tac[] >> qexistsl_tac [`x`,`slot_size`] >> simp[])
  >- (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_def] >>
      simp[]) >>
  metis_tac[]
QED

Theorem local_name_word_read_mods:
  is_word_type ann /\ lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w /\ ptr_covers G0 tn0 p s0 sz /\
  (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem) /\
  lower_value compile_expr ce ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t,G',tn') /\
    expr_post_mods H ctx func ce cx (Name ann id) es sa sb s0
      (es with gas_obs := []) entry.value op t /\
    expr_store_bound cx (post_value_type ce (Name ann id)) entry.value op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx (post_value_type ce (Name ann id)) entry.value op G' tn' t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >> gvs[] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MLOAD [Var p] [out]` >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by simp[Abbr `out`, not_fresh_at_def] >>
  `!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
        mem_word_at (w2n w) mem = typed_val_to_w256 entry.type entry.value` by
    (rpt strip_tac >> irule val_in_memory_word_type >> simp[] >>
     qexistsl_tac [`ann`,`get_tenv cx`] >> simp[]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `mload (w2n w) s0 = typed_val_to_w256 entry.type entry.value` by
    (first_x_assum (qspec_then `s0.vs_memory` mp_tac) >>
     simp[mem_word_at_eq_mload, mem_agree_outside_def]) >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 entry.type entry.value) s0` >>
  `eval_operand (Var p) s0 = SOME w` by simp[eval_operand_def] >>
  `step_inst_base i s0 = OK u` by
    (drule step_MLOAD >> simp[Abbr `i`, Abbr `u`]) >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G0 i u`,`step_taint i s0 u tn0`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  suspend "landing"
QED

Resume local_name_word_read_mods[landing]:
  drule_all fn_has_code_same_block >> strip_tac >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s0.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s0.vs_inst_idx` by simp[] >>
  `alloca_inv s0 /\ 32 <= sz` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[local_ptrs_rel_def] >>
     strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >>
     drule_all word_tv_memory_size >> simp[]) >>
  conj_tac
  >- (`allocas_from lo s0` by
        (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
         PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
      `ptr_covers G0 tn0 p s0 32` by
        (qpat_assum `ptr_covers _ _ _ _ sz` mp_tac >>
         PURE_REWRITE_TAC[ptr_covers_def] >> strip_tac >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      `ptr_inst_ok (DF H) lo 0 ctx func G0 tn0 i s0` by
        (simp[Abbr `i`] >> irule ptr_inst_ok_mload_lo >> simp[]) >>
      `inst_mem_below_frontier i s0` by
        (`local_region ce es.scopes s0 id (w2n w) sz` by
           (simp[local_region_def] >> goal_assum (drule_at Any) >> simp[]) >>
         `lookup_var p s0 = SOME (n2w (w2n w))` by simp[wordsTheory.n2w_w2n] >>
         drule_all body_local_ptr_MLOAD_frontier >> simp[Abbr `i`]) >>
      drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_origin_ptr_edge >>
      simp[] >>
      (impl_tac >- fs[Abbr `i`, mk_inst_def, is_terminator_def,
                      inst_dload_in_section_def, dalloca_no_wrap_def]) >>
      disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
      simp[Abbr `i`, mk_inst_def] >> strip_tac >>
      once_rewrite_tac[GSYM APPEND_NIL] >>
      irule (cj 2 gas_origin_ptr_path_rules) >>
      pure_rewrite_tac[APPEND_NIL] >>
      goal_assum (drule_at Any) >>
      simp[gas_origin_ptr_path_rules, Abbr `u`, update_var_def]) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[expr_post_mods_def] >> conj_tac
      >- (drule_all body_name_wordtype_post >> disch_then (qspec_then `entry.value` mp_tac) >>
          simp[Abbr `u`, update_var_def]) >>
      simp[Abbr `u`] >> irule local_name_mload_immutable >>
      simp[] >> metis_tac[local_ptrs_reserved_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule_all alloca_history_base_step >> simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `ptr_val_ok cx ann entry.value (Var out) (step_prov PG G0 i u)
     (step_taint i s0 u tn0) (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[ptr_val_ok_def, Abbr `i`, Abbr `u`] >> reverse conj_tac
     >- simp[step_prov_def, op_prov_def, set_prov_def, out_prov_def,
             mk_inst_def, FLOOKUP_DRESTRICT] >>
     drule_all mload_ghost_clean >> simp[]) >>
  simp[expr_store_bound_def, expr_type_def,
       allocas_below_fmp_def, Abbr `u`, update_var_def] >>
  fs[ptr_val_ok_def, update_var_def] >>
  simp[Abbr `i`] >> drule_all local_name_mload_ghost >>
  simp[update_var_def] >> disch_then irule
QED

Finalise local_name_word_read_mods
