(* Joint local AugAssign scalar-to-store frame interfaces. *)
Theory augAssignFullLocalSuccessFrame
Ancestors
  augAssignFullLocalNumeric augAssignFullStateFrame augAssignFullHistory
  bodyFullUnwrapRun bodyFullMemoryFrames bodySimFull stmtSimAugAssign
  exprSimSource exprSimHypsDefs exprSimProps exprLoweringProps exprBopSimProps
  stmtSimAugAssignAttr exprSimExtract32Post loweringSlice vyperState
  fragExec exprSimDefs bodyFullGhostFrame loweringStateRelDefs stmtSimDeclStore stmtSimDefs
  bodyPtrBopScalarRun exprBopStraight augAssignPtrScalarCertificate augAssignPtrCompiler
  exprLowering stmtLowering compileEnv loweringPosts bodyPtrDefs
  freshWrites varsExt ptrDiscipline venomState finite_map list pred_set

Theorem augassign_local_success_history_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  alloca_history func t /\ alloca_inv t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  run_inst_seq (emitted_insts sb sc) t = OK u ==>
  alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  strip_tac >>
  `bop <> In /\ bop <> NotIn` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    (`straight_fresh (compile_binop bop lhs rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE))` by
       (`well_typed_binop ty bop ty (expr_type e)` by
          gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
        drule_all typed_binop_scalar_member_ptr >>
        metis_tac[compile_binop_straight_fresh_ptr]) >>
     qpat_x_assum `straight_fresh _` (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
     disch_then (drule_then strip_assume_tac) >> simp[] >>
     qpat_x_assum `writes_fresh sb _` mp_tac >>
     pure_rewrite_tac [writes_fresh_def, EVERY_MEM] >>
     metis_tac[fresh_write_op_simple]) >>
  `sb.cs_current_bb = sc.cs_current_bb` by
    (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)
       bodyPtrBopScalarDispatchTheory.bop_scalar_compile_binop_typed >>
     disch_then (qspecl_then [`expr_type e`,`ty`,`ty`,`{}`,`UNIV`] mp_tac) >>
     simp[same_blocks_def] >>
     gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  irule emitted_alloca_history >> metis_tac[]
QED

Theorem augassign_local_success_scalar_frame_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  cs_extends sa se /\ cs_extends se sb /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  emit_op MLOAD [Var p] sa = (lhs,se) /\
  expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
  ghost_kept_at lo cenv es se G tn s G1 tn1 /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!z. not_fresh_at sa z ==> lookup_var z s = lookup_var z s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)) /\
  u = t with vs_vars := u.vs_vars /\
  q = u with vs_inst_idx := LENGTH sc.cs_current_insts /\
  (!z. not_fresh_at sb z ==> lookup_var z u = lookup_var z t) /\
  (!z. not_fresh_at sb z ==> FLOOKUP Gu z = FLOOKUP G1 z /\
    op_taint tu (Var z) = op_taint tn1 (Var z)) /\
  tu.t_mem = tn1.t_mem /\ tu.t_stor = tn1.t_stor /\
  tu.t_trans = tn1.t_trans /\ tu.t_imm = tn1.t_imm ==>
  sb.cs_current_bb = sc.cs_current_bb /\ cs_extends sa sc /\
  stmt_state_rel H ctx func cenv cx mid q /\
  ghost_inv_at (DF H) lo d cenv cx mid Gu tu q /\
  (!z. not_fresh_at sa z ==> lookup_var z q = lookup_var z t /\
    FLOOKUP Gu z = FLOOKUP G1 z /\ op_taint tu (Var z) = op_taint tn1 (Var z)) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G0 x /\
    op_taint tu (Var x) = op_taint tn0 (Var x)) /\
  q.vs_memory = t.vs_memory /\ q.vs_allocas = t.vs_allocas /\
  q.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `cs_extends sb sc` by metis_tac[compile_binop_grows] >>
  `cs_extends sa sb /\ cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `sb.cs_current_bb = sc.cs_current_bb` by
    (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)
       bodyPtrBopScalarDispatchTheory.bop_scalar_compile_binop_typed >>
     disch_then (qspecl_then [`expr_type e`,`ty`,`ty`,`{}`,`UNIV`] mp_tac) >>
     simp[same_blocks_def] >>
     gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  `sa.cs_next_var <= se.cs_next_var /\ se.cs_next_var <= sb.cs_next_var` by
    (qspec_then `MLOAD` (qspec_then `[Var p]` (qspec_then `sa` mp_tac)) ci_mono_emit_op >>
     qspecl_then [`cenv`,`ty`,`e`,`se`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `!z. not_fresh_at sa z ==> lookup_var z q = lookup_var z t /\
    FLOOKUP Gu z = FLOOKUP G1 z /\ op_taint tu (Var z) = op_taint tn1 (Var z)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sb z` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[cs_extends_def]) >>
     qpat_assum `!z. not_fresh_at sb z ==> lookup_var _ _ = _` (drule_then assume_tac) >>
     qpat_assum `!z. not_fresh_at sb z ==> FLOOKUP Gu _ = _ /\ _`
       (drule_then strip_assume_tac) >> fs[lookup_var_def]) >>
  `q.vs_memory = t.vs_memory /\ q.vs_allocas = t.vs_allocas /\
   q.vs_alloca_next = t.vs_alloca_next` by
    (simp[] >> qpat_assum `u = _` SUBST1_TAC >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx mid q` by
    (simp[stmt_state_rel_inst_idx] >>
     qpat_assum `u = _` SUBST1_TAC >> irule stmt_state_rel_vars_frame >>
     fs[expr_post_def] >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_def, not_fresh_at_mono]) >>
  `ghost_inv_at (DF H) lo d cenv cx mid Gu tu q` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G1`,`mid`,`t`,`sa`,`tn1`] >> simp[] >>
     qpat_assum `u = _` SUBST1_TAC >> simp[]) >>
  simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at se x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> fs[cs_extends_def]) >>
  conj_tac >- (rpt strip_tac >> fs[expr_post_def] >> metis_tac[]) >>
  conj_tac >- (fs[expr_post_def] >> metis_tac[]) >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED

Theorem augassign_local_success_exterior_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  expr_post (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es se sb s mid v rhs t /\
  stmt_state_rel H ctx func cenv cx es0 s0 /\
  alloca_frame cenv es0 sa s0 cenv mid t /\ local_ptrs_reserved cenv sa /\
  MAP FDOM mid.scopes = MAP FDOM es0.scopes /\
  return_buf_frame d cenv se s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
  sb.cs_current_bb = sc.cs_current_bb /\
  run_inst_seq (emitted_insts sb sc) t = OK u /\
  eval_operand op u = SOME (val_to_w256 w) /\ u = t with vs_vars := u.vs_vars /\
  q = u with vs_inst_idx := LENGTH sc.cs_current_insts /\
  (!z. not_fresh_at sb z ==> lookup_var z u = lookup_var z t) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
  q.vs_memory = t.vs_memory /\ q.vs_allocas = t.vs_allocas /\
  q.vs_alloca_next = t.vs_alloca_next ==>
  alloca_frame cenv es0 sa s0 cenv mid q /\ return_buf_frame d cenv sc q /\
  alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
  ~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
  q.vs_inst_idx = LENGTH sc.cs_current_insts /\ eval_operand op q = SOME (val_to_w256 w)
Proof
  strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv mid q` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     conj_tac >- simp[] >>
     conj_tac
     >- (simp[] >> rpt strip_tac >>
         qpat_assum `alloca_frame cenv es0 sa s0 cenv mid t`
           (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
         disch_then (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
         disch_then drule >> simp[]) >>
     simp[] >> qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `return_buf_frame d cenv sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`se`] >>
     simp[] >> fs[expr_post_def] >>
     qspecl_then [`cenv`,`ty`,`e`,`se`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `return_buf_frame d cenv sc q` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`cenv`,`t`,`sb`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!z. not_fresh_at sb z ==> lookup_var z u = _`
           (drule_then assume_tac) >> fs[lookup_var_def]) >>
     mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_compile_expr_sa) >>
     disch_then (qspecl_then [`bop`,`lhs`,`rhs`,`ty`,`NONE`,
       `if bop = Exp then expr_int_literal e else NONE`,`sb`] mp_tac) >> simp[ci_mono_def]) >>
  `alloca_inv t` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `alloca_history func q` by (simp[] >> irule augassign_local_success_history_full >> metis_tac[]) >>
  simp[eval_operand_def] >> qpat_assum `u = _` SUBST1_TAC >> simp[]
QED

Theorem augassign_local_success_store_bounds_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  expr_sim_inv cenv cx env mid /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!current. lookup_scopes id mid.scopes = SOME current ==>
    store_lays_out entry.type current.type w) /\
  stmt_state_rel H ctx func cenv cx mid q /\
  ghost_inv_at D lo d cenv cx mid Gu tu q /\ dead_lo_ok H D lo cenv cx ==>
  ?aw. lookup_var p q = SOME aw /\ 32 <= sz /\ lo <= w2n aw /\
    w2n aw + 32 <= q.vs_alloca_next /\ ptr_covers Gu tu p q 32 /\
    allocas_from lo q /\ lo <= q.vs_alloca_next
Proof
  strip_tac >>
  `?current. lookup_scopes id mid.scopes = SOME current` by
    (gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs(),
         vyperTypeSystemTheory.well_typed_target_def,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[expr_sim_inv_local]) >>
  `?aw. lookup_var p q = SOME aw` by (drule_all local_word_pointer_live >> simp[]) >>
  `local_ptrs_rel func cenv mid.scopes q` by fs[stmt_state_rel_def, state_rel_def] >>
  `local_region cenv mid.scopes q id (w2n aw) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size current.type <= sz /\ w2n aw + sz <= q.vs_alloca_next` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >> rewrite_tac[local_ptrs_rel_def] >>
     strip_tac >> first_x_assum (qspecl_then [`id`,`current`,`p`,`sz`] mp_tac) >> simp[]) >>
  `32 <= sz` by
    (qpat_assum `!current. lookup_scopes _ _ = _ ==> _` (qspec_then `current` mp_tac) >>
     simp[] >> fs[store_lays_out_def]) >>
  `lo <= w2n aw` by
    (`0 < sz` by decide_tac >> drule_all body_full_local_region_lower_bound >> simp[]) >>
  `ptr_covers Gu tu p q sz /\ allocas_from lo q /\ lo <= q.vs_alloca_next` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  qexists_tac `aw` >> simp[] >>
  fs[ptr_covers_def] >> qexistsl_tac [`aw`,`b`,`sz'`] >> simp[] >> decide_tac
QED

Theorem augassign_local_success_store_inputs_full:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\ cur = entry.value /\ ptv = entry.type /\
  (!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
    (INL (MemoryPlace id []),es with gas_obs := gs) /\
    read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL cur,es with gas_obs := gs) /\
    place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL ptv,es with gas_obs := gs)) /\
  emit_op MLOAD [Var p] sa = (lhs,se) /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\
  fn_has_code sb sc func /\ fn_has_code sc sf func /\
  cs_extends sa se /\ cs_extends se sb /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!z. not_fresh_at sa z ==> lookup_var z s = lookup_var z s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv es s /\
    MAP FDOM es.scopes = MAP FDOM es0.scopes) /\
  return_buf_frame d cenv se s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  expr_sim_inv cenv cx env mid /\ word_value cur /\
  bop_result cx ty bop [ty;expr_type e] cur v mid = INL w /\ word_value w /\
  value_has_type entry.type w /\ storage_trace_domain cx st0 mid.storage_trace /\
  ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ghost_kept_at lo cenv es se G tn s G1 tn1) /\
  run_inst_seq (emitted_insts sb sc) t = OK u /\
  eval_operand op u = SOME (val_to_w256 w) /\ u = t with vs_vars := u.vs_vars /\
  (!z. not_fresh_at sb z ==> lookup_var z u = lookup_var z t) /\
  (!D lo. allocas_from lo t /\ lo <= t.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts),Gu,tu)) /\
  (!z. not_fresh_at sb z ==> FLOOKUP Gu z = FLOOKUP G1 z /\
    op_taint tu (Var z) = op_taint tn1 (Var z)) /\
  tu.t_mem = tn1.t_mem /\ tu.t_stor = tn1.t_stor /\
  tu.t_trans = tn1.t_trans /\ tu.t_imm = tn1.t_imm /\
  op_prov Gu op = NONE /\ op_taint tu op = {} /\
  evaluate_binop (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur v = INL w /\
  (!wr fin. write_place cx (MemoryPlace id []) w (mid with gas_obs := []) = (wr,fin) ==>
    !m. wr <> INR (Error (TypeError m))) /\
  (!current. lookup_scopes id mid.scopes = SOME current ==>
    store_lays_out entry.type current.type w) /\
  (?current. lookup_scopes id mid.scopes = SOME current) /\
  q = u with vs_inst_idx := LENGTH sc.cs_current_insts ==>
  ?aw. lookup_var p q = SOME aw /\ eval_operand op q = SOME (val_to_w256 w) /\
    ~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
    q.vs_inst_idx = LENGTH sc.cs_current_insts /\ 32 <= sz /\ lo <= w2n aw /\
    w2n aw + 32 <= q.vs_alloca_next /\ ptr_covers Gu tu p q 32 /\
    allocas_from lo q /\ lo <= q.vs_alloca_next /\ return_buf_frame d cenv sc q /\
    alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
    cs_extends sa sc /\ op_taint tu op = {} /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G0 x /\
      op_taint tu (Var x) = op_taint tn0 (Var x)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid q /\
      ghost_inv_at (DF H) lo d cenv cx mid Gu tu q /\
      stmt_state_rel H ctx func cenv cx es0 s0 /\
      alloca_frame cenv es0 sa s0 cenv mid q /\
      MAP FDOM mid.scopes = MAP FDOM es0.scopes /\
      storage_well_formed_on cx mid (FST H))
Proof
  strip_tac >>
  `sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by
    (qspec_then `MLOAD` (qspec_then `[Var p]` (qspec_then `sa` mp_tac)) ci_mono_emit_op >> simp[ci_mono_def]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all, vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac eval_read_preserves_scopes_dom) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\ alloca_frame cenv es0 sa s0 cenv mid t /\
    MAP FDOM mid.scopes = MAP FDOM es0.scopes` by
    (gen_tac >> strip_tac >> `valid_horizon cx st0 H es.storage_trace` by simp[] >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     conj_tac
     >- (rpt strip_tac >> `not_fresh_at se x` by
           (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
         `lookup_var x s = SOME w'` by metis_tac[] >> fs[expr_post_def]) >>
     conj_tac
     >- (rpt strip_tac >> qpat_assum `alloca_frame cenv es0 sa s0 cenv es s` (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
         disch_then (qspecl_then [`aid`,`off`,`sz'`] mp_tac) >> simp[] >> disch_then (drule_then strip_assume_tac) >>
         `FLOOKUP s.vs_allocas aid = SOME (off,sz')` by metis_tac[] >> `aid < se.cs_next_id` by decide_tac >>
         qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_post_def]) >> strip_tac >>
         qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ t.vs_memory = _`
           (qspecl_then [`aid`,`off`,`sz'`] mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
     simp[] >> qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all augassign_local_success_scalar_frame_full >> strip_tac >>
  drule_all augassign_local_success_exterior_full >> strip_tac >>
  qpat_assum `!H. dead_lo_ok H _ _ _ _` (qspec_then `storage_trace_horizon mid.storage_trace` assume_tac) >>
  drule_all augassign_local_success_store_bounds_full >> strip_tac >>
  qexists_tac `aw` >> simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all augassign_local_success_scalar_frame_full >> strip_tac >>
  drule_all augassign_local_success_exterior_full >> strip_tac >> gvs[expr_post_def]
QED
