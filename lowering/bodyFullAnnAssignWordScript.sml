(* Joint word-declaration execution and source continuation. *)
Theory bodyFullAnnAssignWord
Ancestors
  bodyFullAnnAssignWordPost bodyFullAnnAssignMemoryPost
  bodyFullShared ptrDiscipline bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  bodyExprPreFacts exprSimHyps exprSimSource supportedStmtTraverse vyperTypeCallGraph
  bodySimDeclCases supportedExprTraverse stmtSimProps loweringSlice exprLoweringProps
  bodyFullAllocaFresh gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  bodyFullHashKeccakFixed bodyFullIfExpReach stateRelProj
  stmtSimDeclSource stmtSimDeclStore bodyMemoryDefs logStoreDataOriginPtr bodyBinopFragMemory
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

Theorem annassign_word_full_bind[local]:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
    (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna)
    P (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + exception) r /\
    halt_exit H cx ee (INR exc) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 u.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H res mid G1 tn1 u /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
    (?v. res = INL v /\
      gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
        (new_variable id tyv v) (mid,u,G1,tn1) Q R) \/
    (?exc. res = INR exc /\ !H. valid_horizon cx st0 H mid.storage_trace ==>
      Q H (INR exc) mid G1 tn1 u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Ga`, `entry`, `tna`] >> conj_tac >- simp[] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn u. P H res ee G tn u /\
                    ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res`
  >- fs[exprSimDefsTheory.expr_exit_def] >>
  simp[] >> first_x_assum irule >> fs[exprSimDefsTheory.halt_exit_def]
QED

Theorem annassign_word_full_continuation[local]:
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  value_has_type tyv v /\
  eval_operand op u = SOME (typed_val_to_w256 tyv v) /\ op_taint tn1 op = {} /\
  lookup_var p u = SOME w /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 <= u.vs_alloca_next /\ ptr_covers G1 tn1 p u 32 /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code b sf func /\ ~u.vs_halted /\
  u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!tail. new_variable id tyv v (mid with gas_obs := tail) =
    (INL (),out with gas_obs := tail)) /\
  (!H Gf tnf t'.
    valid_horizon cx st0 H out.storage_trace /\
    val_in_memory tyv v (w2n w) t'.vs_memory /\
    typed_copy_state_frame b (w2n w) 32 u t' /\
    ~t'.vs_halted /\ t'.vs_current_bb = sf.cs_current_bb /\
    t'.vs_inst_idx = LENGTH sf.cs_current_insts /\
    tnf.t_imm = tn1.t_imm /\ tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
    (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t'.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    (!p. FLOOKUP Gf p = FLOOKUP G1 p /\ op_taint tnf (Var p) = op_taint tn1 (Var p)) ==>
    Q H (INL ()) (out with gas_obs := []) Gf tnf t') ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (new_variable id tyv v) (mid,u,G1,tn1) Q R
Proof
  strip_tac >>
  `compile_store_memory ce op (Var p) typ typ b = ((),sf)` by
    simp[contextTheory.compile_store_memory_def] >>
  drule_all compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `out`, `INL ()`, `t`, `tnf`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem annassign_word_full_final_post[local]:
  ghost_inv_at D lo d ce cx mid G1 tn1 u ==>
  return_buf_frame d old sa s0 ==>
  expr_post (H: (bool # 256 word # type_value) list # num list)
    ctx func ce cx e es a b entry mid v op u ==>
  typed_copy_state_frame b (w2n w) 32 u t ==>
  new_variable id tyv v mid = (INL (),out) ==>
  (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n w) mem) ==>
  (!q. FLOOKUP Gf q = FLOOKUP G1 q /\ op_taint tnf (Var q) = op_taint tn1 (Var q)) ==>
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ is_word_type typ /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  fn_inst_ids_distinct func /\
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
  value_has_type tyv v /\ val_in_memory tyv v (w2n w) t.vs_memory /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\ fn_has_code b sf func /\
  alloca_history func u /\ u.vs_current_bb = b.cs_current_bb /\
  u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
  t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ce.ce_return_buf = old.ce_return_buf /\
  cs_extends sa a /\ cs_extends a b /\
  sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\ entry.vs_alloca_next <= u.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0) /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP entry.vs_allocas aid = SOME z) /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  alloca_frame old es sa s0 ce es entry /\
  alloca_frame ce es a entry ce mid u /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
  sa.cs_next_id <= a.cs_next_id /\ sa.cs_next_id <= inst.inst_id /\
  (!x. not_fresh_at sa x ==> FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint tna (Var x) = op_taint tn0 (Var x)) /\
  local_ptrs_reserved old sa /\
  (?J:(bool # 256 word # type_value) list # num list.
     stmt_state_rel J ctx func old cx es s0) /\
  (!ce'. stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
    (~block_is_terminated sf /\ ce' = ce) /\
    cenv_top_ext old ce' out.scopes /\
    stmt_state_rel H ctx func ce' cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce' sf t /\ alloca_history func t /\
    (return_buf_sep d old es s0 /\
       (!bw cap. d = SOME (bw,cap) ==>
         allocas_from (w2n bw + cap) t) ==>
       return_buf_sep d ce' out t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce' cx out Gf tnf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce' out t /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region old es.scopes s0 n b sz' ==>
        off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem) ==> R) ==> R
Proof
  rpt strip_tac >>
  drule_all annassign_word_full_installation_post >> strip_tac >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    annassign_word_full_final_frame) >> strip_tac >>
  `allocas_non_overlapping u` by
    (fs[loweringPostsTheory.expr_post_def] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     simp[venomMemDefsTheory.alloca_inv_def]) >>
  `alloca_frame old es sa s0 ce out t` by
    (drule_all annassign_continuation_success >> strip_tac >> gvs[] >>
     irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
       annassign_word_full_frame_post) >>
     goal_assum (drule_at (Pat `alloca_frame old es sa s0 ce es entry`)) >>
     goal_assum (drule_at (Pat `alloca_frame ce es a entry ce mid u`)) >>
     goal_assum (drule_at (Pat `FLOOKUP u.vs_allocas _ = SOME (_,32)`)) >>
     qexistsl_tac [`H`, `b`, `ctx`, `cx`,
       `<|assignable := T; type := tyv; value := v; popped := []|>`,
       `func`, `id`, `p`] >>
     fs[loweringPostsTheory.expr_post_def]) >>
  `!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region old es.scopes s0 n b sz' ==>
      off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (GEN_ALL (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
       annassign_word_full_taint_post)) >>
     goal_assum (drule_at (Pat `alloca_frame old es sa s0 ce es entry`)) >>
     qexistsl_tac [`w`, `u`, `tna`, `tn1`, `lo`, `inst.inst_id`,
       `a`, `Ga`, `G1`, `G0`] >>
     fs[loweringPostsTheory.expr_post_def] >> first_assum ACCEPT_TAC) >>
  `~block_is_terminated sf` by
    (drule exprOpenPrimitivesTheory.emit_void_terminated >>
     simp[venomInstTheory.is_terminator_def]) >>
  `return_buf_sep d old es s0 /\
   (!bw cap. d = SOME (bw,cap) ==>
     allocas_from (w2n bw + cap) t) ==>
   return_buf_sep d ce out t` by
    (strip_tac >>
     drule_all annassign_continuation_success >> strip_tac >>
     `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
       (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     `lookup_var p t = SOME w /\ t.vs_allocas = u.vs_allocas` by
       (`not_fresh_at b p` by simp[] >>
        fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
           venomStateTheory.venom_state_component_equality]) >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_allocated_local) >>
     qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas inst.inst_id = SOME _` (fn th =>
       qpat_assum `t.vs_allocas = u.vs_allocas` (fn eq =>
         irule_at Any (REWRITE_RULE [GSYM eq] th))) >>
     qexistsl_tac [`sa`,`s0`,`func`,`es`,`cx`,`ctx`,`old`,`J`] >>
     simp[] >> rpt strip_tac >>
     `out = mid with scopes :=
       (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` by
       metis_tac[pairTheory.PAIR_EQ] >>
     `MAP FDOM (sc :: rest) = MAP FDOM es.scopes` by metis_tac[] >>
     fs[] >>
     irule lookup_scopes_declared_other >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!ce'. _ ==> R` (qspec_then `ce` irule) >>
  gvs[loweringPostsTheory.stmt_lands_def] >> first_assum ACCEPT_TAC
QED

Theorem annassign_word_full_success[local]:
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  is_word_type (expr_type e) /\ expr_body_pre ce cx env e es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  expr_post H ctx func ce cx e es a b entry mid v op u /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  ptr_covers Ga tna p entry 32 /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ FLOOKUP entry.vs_allocas aid = SOME (w2n w,32) ==>
  lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,32) /\
  ptr_covers G1 tn1 p u 32 /\
  eval_operand op u = SOME (typed_val_to_w256 tyv v) /\ value_has_type tyv v /\
  ?sc rest. mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    !tail. new_variable id tyv v (mid with gas_obs := tail) =
      (INL (), (mid with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>))::rest)
          with gas_obs := tail)
Proof
  strip_tac >>
  `lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,32)` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 p u 32` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `ptr_covers Ga tna _ entry 32` mp_tac >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def, bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[]) >>
  `eval_operand op u = SOME (typed_val_to_w256 tyv v)` by
    (fs[expr_post_def, expr_val_rel_def, post_value_type_word] >> (gvs[])) >>
  `value_has_type tyv v` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[] >> strip_tac >> irule annassign_word_full_value_type >>
     goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `gas_admissible _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  drule_all annassign_continuation_all_tails >> metis_tac[]
QED

Theorem annassign_word_full_store_freshness[local]:
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  expr_body_pre ce cx env e es /\ is_word_type typ /\ expr_type e = typ /\
  lower_value compile_expr ce typ e a = (op,b) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  lookup_scopes id scopes = NONE /\
  local_ptrs_reserved ce a /\ cs_extends sa a /\
  sa.cs_next_var <= a.cs_next_var /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  not_local_ptr ce scopes p /\ local_ptrs_reserved ce b /\
  (!q. q = p \/ ~not_local_ptr ce scopes q ==> not_fresh_at b q) /\
  sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x)
Proof
  strip_tac >> gvs[] >>
  `not_local_ptr ce scopes p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`, `32`] >> simp[]) >>
     qexists_tac `a` >> simp[]) >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >>
     simp[] >> drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `!q. q = p \/ ~not_local_ptr ce scopes q ==> not_fresh_at b q` by
    (rpt strip_tac >- metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[exprSimOperandsTheory.fresh_not_local_ptr]) >>
  `a.cs_next_var <= b.cs_next_var` by
    (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `sa.cs_next_var <= b.cs_next_var` by decide_tac >>
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem annassign_word_full_rhs[local]:
  is_word_type (expr_type e) /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo old cx) /\ ce.ce_is_ctor = old.ce_is_ctor /\
  ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc /\
  (!x sz. old.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok old sa s0 /\ sa.cs_next_var <= a.cs_next_var /\
  (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  return_buf_frame d old sa s0 /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G,tn)
    (\H res ee Gf tnf u. ?v. res = INL v /\
      expr_post H ctx func ce cx e es a b t ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = b.cs_current_bb /\
      u.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee Gf tnf u /\
      ptr_val_ok cx (post_value_type ce e) v op Gf tnf u /\
      (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op Gf u) /\
      ghost_kept_at lo ce es a G tn t Gf tnf)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `a`, `b`, `shadow_a`, `shadow_b`,
     `op`, `t`, `G`, `tn`] mp_tac) >>
  impl_tac >-
    (asm_rewrite_tac[] >> rpt conj_tac
     >- (qpat_x_assum `!H. dead_lo_ok H _ _ old _` mp_tac >>
         simp[bodyPtrDefsTheory.dead_lo_ok_def])
     >- (rpt strip_tac >> metis_tac[])
     >- (rpt strip_tac >> fs[ret_pc_ok_def] >> metis_tac[])
     >~ [`gas_admissible _ expr_res_ok es`]
     >- (drule annassign_admissible_rhs >> simp[])
     >~ [`return_buf_frame d ce a t`]
     >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qexistsl_tac [`old`, `s0`, `sa`] >> simp[]) >>
     simp[]) >>
  simp[post_value_type_word] >> disch_tac >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >> simp[] >>
  rpt strip_tac >> qexists_tac `v` >> simp[]
QED

Theorem annassign_word_full_declared_layout[local]:
  declare_local old id (expr_type e) sa = (ce,r) /\
  compile_stmt ce lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  old.ce_alloca_locals /\ FLOOKUP old.ce_vars id = NONE /\
  is_word_type (expr_type e) /\ expr_body_pre ce cx env e es /\
  local_ptrs_reserved old sa /\ fn_has_code sa sf func ==>
  ?p a b op.
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
    (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    emit_inst ALLOCA [Lit 32w] [p] r = ((),a) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    emit_void MSTORE [Var p;op] b = ((),sf) /\
    cs_extends r a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code a b func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    local_ptrs_reserved ce a /\ not_fresh_at a p /\
    compile_alloc_buffer 32 sa = (<|buf_operand := Var p; buf_size := 32|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\
    type_memory_bytes old (expr_type e) = 32 /\ ~has_length_word (expr_type e)
Proof
  strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved ce r` by metis_tac[declare_local_reserved] >>
  `fn_has_code r sf func` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `~has_length_word (expr_type e)` by
    metis_tac[stmtSimAssignTheory.is_word_type_no_length_word] >>
  `!sa sb op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) ==>
      cs_extends sa sb` by metis_tac[expr_body_pre_lower_value_word_shape] >>
  drule_all compile_annassign_word_parts >> strip_tac >>
  `compile_alloc_buffer (type_memory_bytes old (expr_type e)) sa =
      (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
         buf_size := type_memory_bytes old (expr_type e)|>,sa')` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     qpat_x_assum `r = _` SUBST1_TAC >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  `cs_extends sa sa'` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sa sa' func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `type_memory_bytes old (expr_type e) = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `sa'`, `sb`, `vop`] >>
  gvs[]
QED

Theorem annassign_word_full_store_ready[local]:
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es ==>
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (res,mid with gas_obs := tail)) ==>
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    (?v. res = INL v /\ expr_post H ctx func ce cx e es a b entry mid v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func u /\ entry.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx mid G1 tn1 u /\
      ptr_val_ok cx (post_value_type ce e) v op G1 tn1 u /\
      (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G1 u) /\
      ghost_kept_at lo ce es a Ga tna entry G1 tn1) /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
  storage_trace_domain cx st0 mid.storage_trace /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  is_word_type (expr_type e) /\ expr_body_pre ce cx env e es /\
  ptr_covers Ga tna p entry 32 /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ FLOOKUP entry.vs_allocas aid = SOME (w2n w,32) /\
  w2n w + 32 <= entry.vs_alloca_next /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\
  cs_extends sa a /\ cs_extends a b /\ cs_extends b sf /\ fn_has_code sa sf func ==>
  ?v sc rest.
    res = INL v /\ mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    (!tail. new_variable id tyv v (mid with gas_obs := tail) =
      (INL (),mid with <|scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>))::rest;
        gas_obs := tail|>)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func ce cx e es a b entry mid v op u /\
      ghost_inv_at (DF H) lo d ce cx mid G1 tn1 u) /\
    lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,32) /\
    ptr_covers G1 tn1 p u 32 /\ eval_operand op u = SOME (typed_val_to_w256 tyv v) /\
    value_has_type tyv v /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    w2n w + 32 <= u.vs_alloca_next /\ op_taint tn1 op = {} /\
    compile_store_memory ce op (Var p) (expr_type e) (expr_type e) b = ((),sf) /\
    cs_extends sa b /\ fn_has_code b sf func /\
    u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
    alloca_history func u /\ entry.vs_alloca_next <= u.vs_alloca_next /\
    ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\ ~u.vs_halted /\ mid.gas_obs = []
Proof
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[post_value_type_word] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func ce cx e es
     a b entry mid v op u` by metis_tac[] >>
  drule_all annassign_word_full_success >> strip_tac >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[] >> strip_tac >> fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `w2n w + 32 <= u.vs_alloca_next` by decide_tac >>
  `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `compile_store_memory ce op (Var p) (expr_type e) (expr_type e) b = ((),sf)` by
    simp[contextTheory.compile_store_memory_def] >>
  `cs_extends sa b` by metis_tac[cs_extends_trans] >>
  `fn_has_code b sf func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  qexistsl_tac [`sc`, `rest`] >> simp[]
QED

Theorem annassign_word_full_runtime_preparation[local]:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\ expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func /\
  (ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  ?p a b op w t Ga tna.
    FLOOKUP cenv'.ce_vars id = SOME (PtrVar (Var p) 32) /\
    (!n. n <> id ==> FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    cenv' with <|ce_vars := cenv.ce_vars; ce_dynarray_capacity := cenv.ce_dynarray_capacity;
                ce_var_type := cenv.ce_var_type|> = cenv /\
    emit_inst ALLOCA [Lit 32w] [p] r = ((),a) /\
    lower_value compile_expr cenv' (expr_type e) e a = (op,b) /\
    emit_void MSTORE [Var p;op] b = ((),sf) /\
    cs_extends sa a /\ cs_extends a b /\ cs_extends b sf /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    local_ptrs_reserved cenv' a /\ not_fresh_at a p /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) [] (OK t,Ga,tna)) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ lookup_var p t = SOME w /\
    ptr_covers Ga tna p t 32 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= t.vs_alloca_next /\
    (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
       FLOOKUP Ga x = FLOOKUP G0 x /\ op_taint tna (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv' es t /\
    (?H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv' cx es t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Ga tna /\
    cenv'.ce_return_buf = cenv.ce_return_buf /\ cenv'.ce_return_pc = cenv.ce_return_pc /\
    sa.cs_next_var <= a.cs_next_var /\
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,Ga,tna)
      (\H res ee Gf tnf u. ?v. res = INL v /\
        expr_post H ctx func cenv' cx e es a b t ee v op u /\
        expr_store_bound cx (expr_type e) v op u /\
        u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv' cx ee Gf tnf u /\
        ptr_val_ok cx (post_value_type cenv' e) v op Gf tnf u /\
        (~is_word_type (post_value_type cenv' e) ==> ptr_buf_ok cenv' e op Gf u) /\
        ghost_kept_at lo cenv' es a Ga tna t Gf tnf)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_all annassign_word_full_declared_layout >>
  disch_then (qx_choosel_then [`p`, `sa'`, `sb`, `vop`] strip_assume_tac) >> gvs[] >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  qpat_x_assum `type_memory_bytes cenv (expr_type e) = 32` (assume_tac o SYM) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     conj_tac >- metis_tac[stmt_state_rel_allocas_below_fmp] >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`, `gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`, `t`, `G'`, `tn'`] strip_assume_tac)) >>
  qpat_x_assum `32 = type_memory_bytes cenv (expr_type e)` (assume_tac o SYM) >>
  `gas_shadow_state r r'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_compiles_env_declare_local) >>
     rewrite_tac[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `r'.cs_blocks = shadow_sa.cs_blocks` by
    (drule_at (Pat `declare_local _ _ _ shadow_sa = _`) declare_local_ptr >>
     simp[] >> strip_tac >> simp[]) >>
  `fn_has_code r' shadow_sf shadow_func` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (irule bodyFullSharedTheory.local_ptrs_reserved_gas_shadow >>
     qexists_tac `sa` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved (gas_shadow_env T cenv') r'` by
    (drule_at (Pat `declare_local _ _ _ shadow_sa = _`) declare_local_reserved >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr _)) _ = _`
    (mp_then (Pos hd) mp_tac compile_annassign_word_parts) >>
  disch_then (qspecl_then [`shadow_func`,`p`,`32`] mp_tac) >>
  simp[gas_shadow_expr_type] >>
  (impl_tac >- metis_tac[compile_expr_grows]) >>
  disch_then (qx_choosel_then [`shadow_a`,`shadow_b`,`shadow_op`] strip_assume_tac) >>
  `gas_shadow_state sa' shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit 32w]`, `outs` |-> `[p]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`,`r'`] mp_tac) >> simp[]) >>
  `shadow_op = vop /\ gas_shadow_state sb shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `cenv'`, `e` |-> `e`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_stmt_lower_value_env) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa'`,`shadow_a`] mp_tac) >> simp[]) >>
  gvs[] >>
  `cenv'.ce_is_ctor = cenv.ce_is_ctor` by
    (qpat_x_assum `cenv' with <|ce_vars := _; ce_dynarray_capacity := _;
                              ce_var_type := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `sa.cs_next_var <= sa'.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sa' x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w` by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv' cx es t` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ ctx func cenv' cx es t`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (qpat_assum `ctx_has_dalloca ctx ==> (!bb. _) /\ (!fn inst s. _)`
           (drule_then strip_assume_tac) >>
         qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G',tn')`
           (qspec_then `ARB` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
           qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
           ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path,phi,safe]))))))) >>
     rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_members >>
     disch_then drule >> strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM,
        unitTransformDefsTheory.dalloca_fmp_headroom_def] >> metis_tac[]) >>
  drule_all annassign_word_full_rhs >> disch_tac >>
  `?H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv' cx es t` by goal_assum (drule_at Any) >>
  qexistsl_tac [`w`, `t`, `G'`, `tn'`] >> fs[post_value_type_word] >> gvs[] >>
  goal_assum (drule_at Any)
QED

Theorem annassign_word_full_source_action[local]:
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es ==>
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) ==>
  storage_trace_domain cx st0 mid.storage_trace ==>
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    (?v. res = INL v /\ expr_post H ctx func cenv' cx e es sa' sb t mid v vop u /\
      expr_store_bound cx (expr_type e) v vop u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx mid G1 tn1 u /\
      ptr_val_ok cx (post_value_type cenv' e) v vop G1 tn1 u /\
      (~is_word_type (post_value_type cenv' e) ==> ptr_buf_ok cenv' e vop G1 u) /\
      ghost_kept_at lo cenv' es sa' Ga tna t G1 tn1) /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  expr_sim_inv cenv cx env es /\ expr_body_pre cenv' cx env e es /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\ ~block_is_terminated sa /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  fn_has_code sa sf func /\
  FLOOKUP cenv'.ce_vars id = SOME (PtrVar (Var p) 32) /\
  (!n. n <> id ==> FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n) /\
  cenv' with <|ce_vars := cenv.ce_vars; ce_dynarray_capacity := cenv.ce_dynarray_capacity;
              ce_var_type := cenv.ce_var_type|> = cenv /\
  emit_inst ALLOCA [Lit 32w] [p] r = ((),sa') /\
  lower_value compile_expr cenv' (expr_type e) e sa' = (vop,sb) /\
  emit_void MSTORE [Var p;vop] sb = ((),sf) /\
  cs_extends sa sa' /\ cs_extends sa' sb /\ cs_extends sb sf /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
  local_ptrs_reserved cenv' sa' /\ not_fresh_at sa' p /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ lookup_var p t = SOME w /\
  ptr_covers Ga tna p t 32 /\ FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  w2n w + 32 < dimword (:256) /\ w2n w + 32 <= t.vs_alloca_next /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
    FLOOKUP Ga x = FLOOKUP G0 x /\ op_taint tna (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv' es t /\
  (?H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv' cx es t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Ga tna /\
  (?J:(bool # 256 word # type_value) list # num list.
    stmt_state_rel J ctx func cenv cx es s0) /\
  cenv'.ce_return_buf = cenv.ce_return_buf /\ cenv'.ce_return_pc = cenv.ce_return_pc /\
  sa.cs_next_var <= sa'.cs_next_var ==>
  (?v. res = INL v /\
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (new_variable id tyv v) (mid,u,G1,tn1)
      (\H res ee G tn t'. ?ce.
        stmt_lands lctx sf res t' /\ ~t'.vs_halted /\
        (res = INL () ==> ~block_is_terminated sf /\ ce = cenv') /\
        cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t' /\
        storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sf t' /\
        alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
        (return_buf_sep d cenv es s0 /\
       (!bw cap. d = SOME (bw,cap) ==>
         allocas_from (w2n bw + cap) t') ==>
       return_buf_sep d ce ee t') /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t' /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t'.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ee t' /\
        (!aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==>
          allocas_below_fmp u)))
Proof
  rpt strip_tac >>
  drule annassign_word_full_store_ready >> disch_then drule >>
  disch_then (fn th => first_assum (mp_then (Pos hd) mp_tac th)) >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
       by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `stmt_state_rel _ ctx func cenv' cx mid u`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  irule annassign_word_full_continuation >> simp[] >>
  goal_assum (drule_at (Pat `compile_stmt _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  goal_assum (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  qexists_tac `mid with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>))::rest` >> simp[] >>
  rename1 `stmt_state_rel Hentry ctx func cenv' cx es t` >>
  qx_genl_tac [`H`, `Gf`, `tnf`, `t'`] >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `stmt_state_rel H ctx func cenv' cx mid u` by fs[loweringPostsTheory.expr_post_def] >>
  `!x cap. cenv'.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `!x cap. cenv'.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x` by fs[] >>
  drule_all (SRULE [] (Q.INST [`typ` |-> `expr_type e`]
    annassign_word_full_store_freshness)) >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `!tail. new_variable _ _ _ _ = _`
    (qspec_then `[]` (fn th => qpat_assum `mid with gas_obs := [] = mid`
      (fn eq => assume_tac (REWRITE_RULE [eq] th)))) >>
  `sa.cs_next_id <= sa'.cs_next_id` by
    (drule_all declare_local_ptr >> strip_tac >>
     drule emitHelperPropsTheory.emit_inst_extends >> simp[] >> strip_tac >> gvs[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv' es sa' t cenv' mid u` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     fs[loweringPostsTheory.expr_post_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Hentry`, `ctx`, `cx`, `func`] >> simp[]) >>
  drule annassign_word_full_final_post >> disch_then drule >>
  disch_then (fn th => qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac th)) >>
  disch_then drule >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then irule >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G0`,`Ga`,`mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]`,
                `lctx`,`r`,`ret_ty`,`tn0`,`tna`,`expr_type e`] >>
  simp[venomInstTheory.mk_inst_def] >>
  qpat_x_assum `mid.scopes = _` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  simp[] >> conj_tac
  >- (strip_tac >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `qq` >>
  qpat_x_assum `!q. q = p \/ _ ==> _` (qspec_then `qq` mp_tac) >> simp[]
QED

Theorem annassign_word_full_execution_sep:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\ expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func /\
  (ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (AnnAssign id (expr_type e) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv') /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sf t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      (return_buf_sep d cenv es s0 /\
       (!bw cap. d = SOME (bw,cap) ==>
         allocas_from (w2n bw + cap) t) ==>
       return_buf_sep d ce ee t) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==>
          allocas_below_fmp u))
Proof
  strip_tac >>
  rename1 `compile_stmt _ _ _ (AnnAssign _ _ e) _ = ((),r'')` >>
  rename1 `gas_shadow_state r'' shadow_sf` >>
  suspend "execution"
QED

Resume annassign_word_full_execution_sep[execution]:
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[] >> conj_tac
  >- metis_tac[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  strip_tac >>
  `?J:(bool # 256 word # type_value) list # num list.
     stmt_state_rel J ctx func cenv cx es s0` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  drule_all annassign_word_full_runtime_preparation >>
  disch_then (qx_choosel_then [`p`, `sa'`, `sb`, `vop`, `w`, `t`, `G'`, `tn'`]
    strip_assume_tac) >> suspend "compose"
QED

Resume annassign_word_full_execution_sep[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule annassign_word_full_bind >> conj_tac
  >- (rpt strip_tac >> simp[bodyPtrDefsTheory.stmt_exit_ptr_def,
        exprSimDefsTheory.halt_exit_def] >>
      fs[exprSimDefsTheory.halt_exit_def] >>
      conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
      strip_tac >> rpt strip_tac >> gvs[] >>
      Cases_on `exc` >> fs[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `e'` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  qunabbrev_tac `childR` >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  qexists_tac `tyv` >> simp[] >> suspend "continuation"
QED

Resume annassign_word_full_execution_sep[continuation]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `u`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  drule (SRULE [] annassign_word_full_source_action) >> disch_then drule >>
  disch_then drule >>
  disch_then (fn th => first_assum (mp_then (Pos hd) mp_tac th)) >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >>
  disch_then (fn th => disj1_tac >> irule th) >> simp[] >> metis_tac[]
QED

Finalise annassign_word_full_execution_sep

Theorem annassign_word_full_execution:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\ expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (AnnAssign id (expr_type e) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv') /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sf t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r)
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)` by simp[] >>
  drule_all annassign_word_full_execution_sep >>
  disch_then (fn th => irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    irule_at Any th) >>
  qexists_tac `RetQ` >> simp[] >> rpt strip_tac >>
  qexists_tac `ce` >> simp[] >> metis_tac[]
QED
