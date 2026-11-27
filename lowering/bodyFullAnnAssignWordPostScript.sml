(* Joint word-declaration stores and scope installation. *)
Theory bodyFullAnnAssignWordPost
Ancestors
  bodyFullAllocaFresh gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  stmtSimDeclSource stmtSimDeclStore stmtSimDeclCompose stmtSimDeclCopyFrame exprSimStorageCopy
  stateRelProj bodyMemoryDefs logStoreDataOriginPtr bodyBinopFragMemory
  bodyFullMemoryFrames bodyExprPreFacts exprSimHyps exprSimSource
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  supportedStmtTraverse vyperTypeCallGraph supportedExprTraverse stmtSimProps
  loweringSlice exprLoweringProps loweringPosts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

Theorem annassign_word_full_shadow_parts:
  is_word_type typ /\ ~has_length_word typ /\ expr_type e = typ /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_shadow_state r shadow_r /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sf) /\
  emit_inst ALLOCA [Lit (n2w sz)] [p] r = ((),a) /\
  lower_value compile_expr ce typ e a = (op,b) /\
  fn_has_code shadow_r shadow_sf shadow_func ==>
  ?shadow_a shadow_b.
    emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r = ((),shadow_a) /\
    lower_value compile_expr ce typ (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    emit_void MSTORE [Var p;op] shadow_b = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func
Proof
  strip_tac >>
  Cases_on `emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r` >>
  rename1 `emit_inst ALLOCA _ _ shadow_r = (u,shadow_a)` >>
  `u = () /\ gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit (n2w sz)]`,
       `outs` |-> `[p]`] gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`, `shadow_r`] mp_tac) >> gvs[]) >> gvs[] >>
  Cases_on `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_op,shadow_b)` >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
       gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`, `shadow_a`] mp_tac) >> simp[]) >> gvs[] >>
  `cs_extends shadow_a shadow_b` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _`
       (mp_tac o MATCH_MP (CONJUNCT2 compile_expr_grows)) >> simp[]) >>
  qpat_x_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr e)) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >>
  simp[compile_stmt_def, compile_assign_value_def, emit_local_alloca_def,
       lower_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       gas_shadow_expr_type] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  `cs_extends shadow_r shadow_a` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_b shadow_sf` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_a shadow_sf` by metis_tac[cs_extends_trans] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem annassign_word_full_value_type:
  !mods.
  expr_body_pre_mods mods cenv cx env e es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ expr_type e = typ /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es ==>
  value_has_type tyv v
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] exprSimSourceTheory.expr_body_pre_eval) >>
  disch_then (qspecl_then [`cenv`, `env`] mp_tac) >> simp[] >>
  simp[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env mid` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  gvs[]
QED

Theorem annassign_word_full_store_history[local]:
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\
  fn_has_code b sf func /\ alloca_history func u /\
  u.vs_current_bb = b.cs_current_bb /\
  u.vs_inst_idx = LENGTH b.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\
  t.vs_inst_idx = LENGTH b.cs_current_insts + 1 /\
  t.vs_allocas = u.vs_allocas ==>
  alloca_history func t
Proof
  strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `sf.cs_current_bb = b.cs_current_bb` by
    (qpat_x_assum `emit_void MSTORE _ b = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `fn_has_code b sf func` mp_tac >>
  simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
  rename1 `lookup_block b.cs_current_bb func.fn_blocks = SOME bb` >>
  `?restcode. bb.bb_instructions = sf.cs_current_insts ++ restcode` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
  `t with vs_inst_idx := u.vs_inst_idx + 1 = t` by
    simp[venomStateTheory.venom_state_component_equality] >>
  `alloca_history func (t with vs_inst_idx := u.vs_inst_idx + 1)` suffices_by
    asm_rewrite_tac [] >>
  qpat_assum `alloca_history func u`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice)) >>
  disch_then (qspecl_then [`t`, `bb`,
    `[mk_inst b.cs_next_id MSTORE [Var p;op] []]`, `restcode`] mp_tac) >>
  simp[venomInstTheory.mk_inst_def, listTheory.DROP_APPEND,
       arithmeticTheory.SUB_EQ_0] >>
  `t with vs_inst_idx := LENGTH b.cs_current_insts + 1 = t` by
    simp[venomStateTheory.venom_state_component_equality] >>
  `LENGTH b.cs_current_insts - (LENGTH b.cs_current_insts + 1) = 0` by decide_tac >>
  asm_rewrite_tac [listTheory.DROP_0]
QED

(* Install the source declaration after the joint word store. *)
Theorem annassign_word_full_install[local]:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ is_word_type typ /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, mid) /\
  stmt_state_rel H ctx func ce cx mid s /\ fn_inst_ids_distinct func /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,32) /\
  typed_copy_state_frame sb (w2n w) 32 s t /\
  local_ptrs_reserved ce sb /\
  (!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at sb q) /\
  value_has_type tyv v /\ val_in_memory tyv v (w2n w) t.vs_memory ==>
  stmt_state_rel H ctx func ce cx (SND (new_variable id tyv v mid)) t
Proof
  strip_tac >> drule_all annassign_continuation_success >> strip_tac >>
  simp[] >>
  `val_wf tyv v /\ type_memory_size tyv = 32` by
    metis_tac[stmtSimDeclStoreTheory.typed_word_store] >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  irule stmt_state_rel_declare_copy_frame >>
  simp[] >>
  qexistsl_tac [`inst`, `s`, `sb`, `w`] >>
  simp[exprSimStorageCopyTheory.copy_static_def,
       venomStateTheory.venom_state_component_equality] >>
  fs[typedMemoryCopyTheory.typed_copy_frame_def] >>
  metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]
QED

(* Scope installation preserves the complete, arbitrary-lo ghost frame. *)
Theorem annassign_word_full_ghost_install[local]:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, mid) /\
  ghost_inv_at D lo d ce cx mid G tn t /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  ptr_covers G tn p t 32 /\
  (!w mem. lookup_var p t = SOME w /\
    mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tyv v (w2n w) mem) ==>
  ghost_inv_at D lo d ce cx (SND (new_variable id tyv v mid)) G tn t
Proof
  strip_tac >> drule_all annassign_continuation_success >> strip_tac >>
  simp[] >> fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  `lookup_scopes name mid.scopes = SOME entry` by
    gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  gvs[] >> metis_tac[]
QED

Theorem annassign_word_full_ghost_store[local]:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, mid) /\
  stmt_state_rel H ctx func ce cx mid s /\ fn_inst_ids_distinct func /\
  ghost_inv_at D lo d ce cx mid G tn s /\ local_ptrs_reserved ce sb /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sb x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sb x) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,32) /\
  ptr_covers G tn p s 32 /\ typed_copy_state_frame sb (w2n w) 32 s t /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!q. FLOOKUP Gf q = FLOOKUP G q /\ op_taint tf (Var q) = op_taint tn (Var q)) /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n w) mem) ==>
  ghost_inv_at D lo d ce cx (SND (new_variable id tyv v mid)) Gf tf t
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  `lo <= w2n w` by (fs[bodyPtrDefsTheory.ghost_inv_at_def,
    ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `ghost_inv_at D lo d ce cx mid Gf tf t` by
    (irule bodyFullMemoryFramesTheory.body_full_memory_ghost_frame >>
     conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
     conj_tac >- (fs[bodyPtrDefsTheory.ghost_inv_at_def,
       ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
     qexistsl_tac [`G`, `s`, `sb`, `tn`, `{i | w2n w <= i /\ i < w2n w + 32}`] >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `local_ptrs_rel func ce mid.scopes s /\ alloca_inv s` by
           metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
         `local_region ce mid.scopes s name (w2n w') sz` by
           (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
         `regions_disjoint (w2n w) 32 (w2n w') sz` by
           (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
            goal_assum (drule_at Any) >> metis_tac[]) >>
         fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
         first_x_assum drule_all >> strip_tac >> gvs[] >>
         drule exprSimPropsTheory.val_footprint_le >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     conj_tac >- (fs[typedMemoryCopyTheory.typed_copy_frame_def] >>
       rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     conj_tac >- (rpt strip_tac >>
       `~(w2n w <= i /\ i < w2n w + 32)` by decide_tac >> metis_tac[]) >>
     fs[typedMemoryCopyTheory.typed_copy_frame_def]) >>
  irule annassign_word_full_ghost_install >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`e`, `es`, `gs`, `lctx`, `typ`] >> simp[]) >>
  `not_fresh_at sb p` by
    metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  simp[] >> fs[bodyPtrDefsTheory.ptr_covers_def] >> gvs[]
QED

(* A word local. *)
Theorem annassign_word_full_final_frame:
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\ fn_has_code b sf func /\
  expr_post H ctx func ce cx e es a b entry mid v op u /\
  typed_copy_state_frame b (w2n w) 32 u t /\
  alloca_history func u /\ u.vs_current_bb = b.cs_current_bb /\
  u.vs_inst_idx = LENGTH b.cs_current_insts /\
  t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
  return_buf_frame d old sa s0 /\ ce.ce_return_buf = old.ce_return_buf /\
  cs_extends sa a /\ cs_extends a b /\
  sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\
  entry.vs_alloca_next <= u.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0) /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP entry.vs_allocas aid = SOME z) /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  (!x. not_fresh_at sa x ==> FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint tna (Var x) = op_taint tn0 (Var x)) /\
  (!x. FLOOKUP Gf x = FLOOKUP G1 x /\ op_taint tnf (Var x) = op_taint tn1 (Var x)) ==>
  return_buf_frame d ce sf t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tnf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
        venomStateTheory.venom_state_component_equality] >>
  `cs_extends sa b` by metis_tac[cs_extends_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at b x /\ not_fresh_at a x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z` by
    (rpt strip_tac >>
     qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >> strip_tac >>
     fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  qpat_assum `emit_void MSTORE _ b = _`
    (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >> strip_tac >>
  `sf.cs_current_bb = b.cs_current_bb` by
    (qpat_x_assum `emit_void MSTORE _ b = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >> strip_tac >> gvs[]) >>
  conj_tac >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
    qexistsl_tac [`old`, `s0`, `sa`] >> simp[] >> metis_tac[cs_extends_trans]) >>
  conj_tac >- (irule annassign_word_full_store_history >>
    goal_assum (drule_at (Pat `compile_stmt _ _ _ _ _ = _`)) >>
    goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> qexists_tac `u` >> simp[]) >>
  fs[loweringPostsTheory.expr_post_def, bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]
QED

Theorem annassign_word_full_frame_post:
  alloca_frame old es sa s0 ce es entry /\
  alloca_frame ce es a entry ce mid u /\ sa.cs_next_id <= a.cs_next_id /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==>
           FLOOKUP entry.vs_allocas aid = SOME z) /\
  (!aid z. FLOOKUP entry.vs_allocas aid = SOME z ==>
           FLOOKUP u.vs_allocas aid = SOME z) /\
  stmt_state_rel H ctx func ce cx mid u /\
  FLOOKUP u.vs_allocas aid0 = SOME (w2n w,32) /\ sa.cs_next_id <= aid0 /\
  lookup_var p u = SOME w /\ FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  mid.scopes = sc :: rest /\ out.scopes = (sc |+ (id,decl)) :: rest /\
  typed_copy_state_frame b (w2n w) 32 u t /\ local_ptrs_reserved ce b ==>
  alloca_frame old es sa s0 ce out t
Proof
  strip_tac >>
  `allocas_non_overlapping u` by
    (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
     simp[venomMemDefsTheory.alloca_inv_def]) >>
  `alloca_frame ce es sa entry ce out t` by
    (irule stmtSimDeclComposeTheory.alloca_frame_declare_store >>
     goal_assum (drule_at (Pat `alloca_frame ce es a entry ce mid u`)) >>
     goal_assum (drule_at (Pat `FLOOKUP u.vs_allocas aid0 = _`)) >>
     qexistsl_tac [`decl`, `id`, `p`, `rest`, `b`, `sc`] >>
     simp[] >>
     fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
        typedMemoryCopyTheory.typed_copy_frame_def] >>
     rpt strip_tac >>
     `aid <> aid0` by decide_tac >>
     `off + z' <= w2n w \/ w2n w + 32 <= off` by
       (fs[venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]) >>
     metis_tac[]) >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  qexistsl_tac [`ce`, `es`, `entry`, `sa`] >> simp[]
QED

Theorem annassign_word_full_taint_post:
  alloca_frame old es sa s0 ce es entry /\ sa.cs_next_id <= a.cs_next_id /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==>
           FLOOKUP entry.vs_allocas aid = SOME z) /\
  (!aid z. FLOOKUP entry.vs_allocas aid = SOME z ==>
           FLOOKUP u.vs_allocas aid = SOME z) /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  allocas_non_overlapping u /\
  FLOOKUP u.vs_allocas aid0 = SOME (w2n w,32) /\ sa.cs_next_id <= aid0 /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) ==>
  !aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region old es.scopes s0 n b sz' ==>
               off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem
Proof
  strip_tac >>
  `!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region old es.scopes s0 n b sz' ==>
               off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (GEN_ALL bodySimFullTheory.alloca_taint_kept_trans) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`tna`, `a`] >>
     fs[bodyPtrDefsTheory.ghost_kept_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid <> aid0` by decide_tac >>
  `off + sz <= w2n w \/ w2n w + 32 <= off` by
    (fs[venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]) >>
  `i IN tn1.t_mem` by
    (qpat_x_assum `!i. ~_ ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  first_x_assum irule >> simp[] >> qexistsl_tac [`aid`, `off`, `sz`] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem annassign_word_full_installation_post:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ is_word_type typ /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  expr_post (H: (bool # 256 word # type_value) list # num list)
    ctx func ce cx e es a b entry mid v op u /\
  ghost_inv_at D lo d ce cx mid G1 tn1 u /\ fn_inst_ids_distinct func /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\ not_local_ptr ce mid.scopes p /\
  lookup_var p u = SOME w /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32) /\
  ptr_covers G1 tn1 p u 32 /\ local_ptrs_reserved ce b /\
  (!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at b q) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  value_has_type tyv v /\ typed_copy_state_frame b (w2n w) 32 u t /\
  (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n w) mem) /\
  val_in_memory tyv v (w2n w) t.vs_memory /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
  (!q. FLOOKUP Gf q = FLOOKUP G1 q /\ op_taint tnf (Var q) = op_taint tn1 (Var q)) ==>
  cenv_top_ext old ce (SND (new_variable id tyv v mid)).scopes /\
  stmt_state_rel H ctx func ce cx (SND (new_variable id tyv v mid)) t /\
  storage_well_formed_on cx (SND (new_variable id tyv v mid)) (FST H) /\
  ghost_inv_at D lo d ce cx (SND (new_variable id tyv v mid)) Gf tnf t
Proof
  strip_tac >>
  `stmt_state_rel H ctx func ce cx mid u` by fs[loweringPostsTheory.expr_post_def] >>
  `stmt_state_rel H ctx func ce cx (SND (new_variable id tyv v mid)) t` by
    (irule annassign_word_full_install >> simp[] >> conj_tac
     >- metis_tac[] >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >> metis_tac[]) >>
  `ghost_inv_at D lo d ce cx (SND (new_variable id tyv v mid)) Gf tnf t` by
    (irule (INST_TYPE [alpha |-> ``:256``] annassign_word_full_ghost_store) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[]) >>
  drule_all annassign_continuation_success >> strip_tac >> simp[] >>
  conj_tac >- (simp[loweringPostsTheory.cenv_top_ext_def] >>
    rpt strip_tac >> `n = id` by metis_tac[] >> gvs[] >>
    qpat_x_assum `lookup_scopes id _ = NONE` mp_tac >>
    simp[vyperStateTheory.lookup_scopes_def, CaseEq "option"]) >>
  irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
  qexists_tac `mid` >> fs[loweringPostsTheory.expr_post_def]
QED
