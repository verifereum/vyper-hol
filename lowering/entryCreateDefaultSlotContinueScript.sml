(* Prepare an omitted keyword row and transport its slots to the next row. *)
Theory entryCreateDefaultSlotContinue
Ancestors
  groupedDefaultCode groupedKeywordOmitted exprBodyPreProps exprSimSource
  exprSimFullBundleProps fragGasOriginPtrLoop freshWrites valueEncodingTyping
  vyperStorageTrace bodyFullIfExpReach loweringStateRelDefs loweringPosts
  finite_map words list pair bodyPtrDefs exprLoweringProps bodyFullPreds
  vyperStorageFootprint exprSimProps

Theorem grouped_initializer_head_inputs:
  compile_init_kwargs ce ((name,Var p,ty,e)::vars) off 0 hi sa = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ce)
    ((name,Var p,ty,gas_shadow_expr e)::MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
    off 0 hi sha = ((),shb) /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
  (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
    expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
  lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
    lower_value compile_expr ce ty e /\
  lower_value compile_expr (gas_shadow_env T (ce with ce_vars := FEMPTY))
    ty (gas_shadow_expr e) =
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
  ce.ce_return_buf = NONE /\ ce.ce_return_pc = NONE /\ ce.ce_imm_alloca = NONE /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct fn /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
  alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_fmp_headroom inst u) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?op mid last shmid shlast.
    expr_body_pre (ce with ce_vars := FEMPTY) cx env e es /\
    expr_sim_full_hypotheses (DF,0,NONE,ctx,shadow_ctx,PG:(num # num) option list,fn,shfn)
      (ce with ce_vars := FEMPTY) cx ty e es (st0,sa,mid,sha,shmid,op,s,G,tn) /\
    lower_value compile_expr ce ty e sa = (op,mid) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shmid) /\
    (if is_word_type ty then emit_void MSTORE [Var p;op]
     else if is_bytestring_type ty then compile_store_bytestring op (Var p)
     else emit_void MCOPY [Var p;op;Lit (n2w (type_memory_bytes ce ty))]) mid = ((),last) /\
    compile_init_kwargs ce vars off 0 hi last = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(n,p,a,d). (n,p,a,gas_shadow_expr d)) vars)
      off 0 hi shlast = ((),shb) /\
    fn_has_code sa mid fn /\ fn_has_code sha shmid shfn /\
    fn_has_code mid last fn /\ fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\
    gas_shadow_state mid shmid /\ gas_shadow_state last shlast /\
    ci_mono sa last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (drule_all_then
    (qx_choosel_then [`op`,`mid`,`last`,`shmid`,`shlast`] strip_assume_tac))
    grouped_default_initializer_intervals >>
  qexistsl_tac [`op`,`mid`,`last`,`shmid`,`shlast`] >>
  `expr_body_pre (ce with ce_vars := FEMPTY) cx env e es` by metis_tac[] >>
  asm_rewrite_tac[] >>
  simp[expr_sim_full_hypotheses_def, expr_sim_full_code_def, local_ptrs_reserved_def,
       return_buf_frame_def, FLOOKUP_EMPTY] >>
  metis_tac[expr_body_pre_gas_admissible]
QED

val allocated_slot = ``\sa s G tn (aid,p,b0,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ b0 < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (b0,type_memory_size tv) /\
  lookup_var p s = SOME (n2w b0) /\ ptr_covers G tn p s (type_memory_size tv)``;

val initialized_slot = ``\sa s G tn (aid,p,b0,tv,v).
  ^allocated_slot sa s G tn (aid,p,b0,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v b0 mem)``;

Theorem grouped_initializer_allocated_slot_kept:
  ci_mono sa sb /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
     lookup_var p t = SOME w /\ FLOOKUP J p = FLOOKUP G p /\
     op_taint tz (Var p) = op_taint tn (Var p)) /\
  ^allocated_slot sa s G tn slot ==>
  ^allocated_slot sb t J tz slot
Proof
  PairCases_on `slot` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!p w. _` (qspecl_then [`slot1`,`n2w slot2:256 word`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  fs[ci_mono_def, ptr_covers_def] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, not_fresh_at_mono]
QED

Theorem grouped_initializer_tail_inputs:
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    value_has_type tv v /\ val_wf tv v /\
    (!mem. mem_agree_outside tn1.t_mem tail_state.vs_memory mem ==>
      val_in_memory tv v b0 mem) /\
    lookup_var p tail_state = SOME (n2w b0) /\
    FLOOKUP tail_state.vs_allocas aid = SOME (b0,type_memory_size tv) /\
    ptr_covers G1 tn1 p tail_state (type_memory_size tv) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP tail_state.vs_allocas id = SOME entry) /\
    (!q w. not_fresh_at sa q /\ lookup_var q s = SOME w ==>
      lookup_var q tail_state = SOME w /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)) /\
    (!id q old_b0 n otv x. id <> aid /\ id < sa.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (old_b0,n) /\
      not_fresh_at sa q /\ lookup_var q s = SOME (n2w old_b0) /\
      ptr_covers G tn q s n /\ val_wf otv x /\ val_footprint otv x <= n /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory otv x old_b0 mem) ==>
      !mem. mem_agree_outside tn1.t_mem tail_state.vs_memory mem ==>
        val_in_memory otv x old_b0 mem) /\
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee tail_state /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee G1 tn1 tail_state /\
    ee.scopes = es.scopes /\ expr_sim_inv (ce with ce_vars := FEMPTY) cx env ee /\
    alloca_history fn tail_state /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tail_state) /\
    tail_state.vs_current_bb = last.cs_current_bb /\
    tail_state.vs_inst_idx = LENGTH last.cs_current_insts /\ ~tail_state.vs_halted /\
    gas_origin_ptr_path (DF H,0,explicit,ctx,fn,PG) (s,G,tn) marks (OK tail_state,G1,tn1)) /\
  expr_body_pre (ce with ce_vars := FEMPTY) cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ ci_mono sa last /\
  ^allocated_slot sa s G tn (aid,p,b0,tv) /\
  EVERY (^allocated_slot sa s G tn) slots /\
  EVERY (^initialized_slot sa s G tn) kept /\
  ALL_DISTINCT (aid::(MAP FST slots ++ MAP FST kept)) /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_fmp_headroom inst u) ==>
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env ee /\
  EVERY (^allocated_slot last tail_state G1 tn1) slots /\
  EVERY (^initialized_slot last tail_state G1 tn1) ((aid,p,b0,tv,v)::kept) /\
  ALL_DISTINCT (MAP FST slots ++ MAP FST ((aid,p,b0,tv,v)::kept)) /\
  (!f inst u. frag_reachable ctx fn tail_state f inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee tail_state /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee G1 tn1 tail_state) /\
  alloca_history fn tail_state /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tail_state) /\
  ~tail_state.vs_halted /\ tail_state.vs_current_bb = last.cs_current_bb /\
  tail_state.vs_inst_idx = LENGTH last.cs_current_insts /\ ee.scopes = es.scopes
Proof
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (`well_typed_expr env e` by drule_then (ACCEPT_TAC o cj 2) expr_body_pre_static_facts >>
     qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac
         (Q.INST [`mods` |-> `[(NONE,tops)]`, `env` |-> `env`]
           (SPEC_ALL body_const_cells_agree_expr_read)))) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!f inst u. frag_reachable ctx fn tail_state f inst u ==> dalloca_fmp_headroom inst u` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> metis_tac[]) >>
  `EVERY (^allocated_slot last tail_state G1 tn1) slots` by
    (qpat_assum `EVERY _ slots` mp_tac >> simp_tac bool_ss [EVERY_MEM] >>
     strip_tac >> qx_gen_tac `row` >> strip_tac >>
     qpat_assum `!x. MEM x slots ==> _` (qspec_then `row` (drule_then assume_tac)) >>
     mp_tac (SIMP_RULE (srw_ss()) []
       (Q.INST [`sb` |-> `last`, `t` |-> `tail_state`, `J` |-> `G1`,
         `tz` |-> `tn1`, `slot` |-> `row`]
         (SPEC_ALL grouped_initializer_allocated_slot_kept))) >> asm_rewrite_tac[]) >>
  `EVERY (^initialized_slot last tail_state G1 tn1) kept` by
    (qpat_assum `EVERY _ kept` mp_tac >> simp_tac bool_ss [EVERY_MEM] >>
     strip_tac >> qx_gen_tac `row` >> PairCases_on `row` >> strip_tac >>
     qpat_assum `!row. MEM row kept ==> _`
       (qspec_then `(row0,row1,row2,row3,row4)` (drule_then mp_tac)) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     `row0 <> aid` by
       (`MEM row0 (MAP FST kept)` by
          (simp_tac bool_ss [MEM_MAP] >> qexists_tac `(row0,row1,row2,row3,row4)` >> simp[]) >>
        metis_tac[]) >>
     `val_wf row3 row4` by (irule (cj 1 value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
     `val_footprint row3 row4 <= type_memory_size row3` by simp[val_footprint_le] >>
     conj_tac >-
       (mp_tac (Q.INST [`sb` |-> `last`, `t` |-> `tail_state`, `J` |-> `G1`,
         `tz` |-> `tn1`, `slot` |-> `(row0,row1,row2,row3)`]
         (SPEC_ALL grouped_initializer_allocated_slot_kept)) >> simp[]) >>
     simp[] >>
     qpat_assum `!id p old_b0 n otv x. id <> aid /\ _ ==> _`
       (qspecl_then [`row0`,`row1`,`row2`,`type_memory_size row3`,`row3`,`row4`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  qpat_assum `ci_mono sa last` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `aid < last.cs_next_id` by decide_tac >>
  `not_fresh_at last p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `^initialized_slot last tail_state G1 tn1 (aid,p,b0,tv,v)` by simp[] >>
  `ALL_DISTINCT (MAP FST slots ++ MAP FST ((aid,p,b0,tv,v)::kept))` by
    (MAP_EVERY (fn pat => qpat_assum pat mp_tac)
       [`ALL_DISTINCT (MAP FST slots ++ MAP FST kept)`,
        `~MEM aid (MAP FST slots)`,`~MEM aid (MAP FST kept)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  fs[] >> first_assum ACCEPT_TAC
QED
