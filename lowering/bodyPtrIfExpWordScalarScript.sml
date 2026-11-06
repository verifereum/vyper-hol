Theory bodyPtrIfExpWordScalar
Ancestors
  bodyPtrIfExpScalarLoad bodyPtrIfExpWordMemory exprSimUnwrap
  exprSimUnwrapProps exprSimPtrProps appendStorageGhostPtr
  loweringPosts freshWrites finite_map venomExecSemantics
  bodyPtrDefs venomState compileEnv emitHelper exprLoweringProps context
  valueEncoding vyperAST vyperTyping vyperValue exprSimProps
  bodyPtrIfExpWordLocations

Theorem ifexp_scalar_word_suffix[local]:
  MEM opc [SLOAD;TLOAD;DLOAD] /\
  emit_op opc [p.ptr_operand] sm = (op,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw
    (LocatedValue (expr_type e) p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  step_inst_base
    (mk_inst sm.cs_next_id opc [p.ptr_operand]
      [STRING #"%" (toString sm.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        w = typed_val_to_w256 tv v) /\ is_word_type (expr_type e) ==>
  ?u G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_emit_scalar_load_ptr_path >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u)` >>
  qexistsl [`u`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- suspend "post" >>
  conj_tac >- (gvs[] >> simp[ptr_val_ok_def]) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  gvs[Abbr `u`, update_var_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def]
QED

Resume ifexp_scalar_word_suffix[post]:
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `not_local_ptr cenv ee.scopes out` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel ctx fn cenv cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> gvs[vv_post_def]) >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue (expr_type e) p) s` by
    (drule vv_post_read_result >> disch_then (fn th => fs[th])) >>
  irule expr_post_of_vv_post_load >> goal_assum (drule_at Any) >>
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexistsl [`p`,`s`,`sm`,`expr_type e`] >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Resume ifexp_scalar_word_suffix[ghost]:
  irule ghost_inv_fresh_frame >> goal_assum (drule_at Any) >>
  qexistsl [`G`,`ee`,`s`,`sa`] >>
  simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[not_fresh_at_mono]
QED

Resume ifexp_scalar_word_suffix[kept]:
  irule ghost_kept_suffix_compose >> goal_assum (drule_at Any) >>
  qexistsl [`G`,`tn`] >> simp[] >> metis_tac[]
QED

Finalise ifexp_scalar_word_suffix

Theorem ifexp_storage_word_suffix:
  is_word_type (expr_type e) /\
  compile_ptr_load F cenv.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw
    (LocatedValue (expr_type e) p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  ?u G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue (expr_type e) p) s` by
    (drule vv_post_read_result >> disch_then (fn th => fs[th])) >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       storage_holds cx tr (expr_type e) (Value v) a ee s` by
    (Cases_on `tr` >> gvs[vv_post_def, vv_holds_def]) >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) a = {}` by
    metis_tac[ifexp_located_word_storage_key_clean] >>
  `op_taint tn p.ptr_operand = {}` by
    (Cases_on `tr` >> gvs[ptr_vv_ok_def]) >>
  irule ifexp_scalar_word_suffix >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl [`a`,`if tr then TLOAD else SLOAD`] >>
  goal_assum (drule_at Any) >> simp[] >>
  ` (if tr then tload a s else sload a s) = typed_val_to_w256 tvt v` by
    metis_tac[storage_holds_load] >>
  Cases_on `tr` >> gvs[compile_ptr_load_def, step_inst_base_def, exec_read1_def] >>
  metis_tac[]
QED

Theorem ifexp_code_word_suffix:
  is_word_type (expr_type e) /\
  compile_ptr_load F cenv.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw
    (LocatedValue (expr_type e) p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ p.ptr_location = LocCode ==>
  ?u G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue (expr_type e) p) s` by
    (drule vv_post_read_result >> disch_then (fn th => fs[th])) >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx (expr_type e) (Value v) a ee s /\
       stmt_state_rel ctx fn cenv cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  drule_all immutable_holds_dload >> strip_tac >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  irule ifexp_scalar_word_suffix >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl [`a`,`DLOAD`] >>
  simp[] >>
  gvs[ifexp_runtime_code_word_compile] >>
  drule step_DLOAD >> simp[] >> metis_tac[]
QED
