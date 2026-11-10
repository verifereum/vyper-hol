(* Counted declaration updates after the shared widened physical copy. *)
Theory widenedDeclareContinuationMem
Ancestors
  widenedLocalContinuationMem widenedLocalEndpointMem widenedLocalRuntimeMem
  stmtSimDeclSource gasSummary fragGasMode vyperState finite_map
  exprLoweringProps compileEnv venomState widenedInternalCallLayout
  exprSimSource externalNormalizePremises exprSimHyps exprSimDefs
  exprSimMemDefs vyperAST loweringPosts localCopyDestinationMem bodyMemoryDefs
  exprOperandVar exprSimMemoryPath exprSimLayoutTransport
Libs monadsyntax

Theorem typed_copy_declare_marked_mem[local]:
  stmt_state_rel ctx fn ce cx es u /\ fn_inst_ids_distinct fn /\
  es.scopes = sc::rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p u = SOME dw /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u) /\
  (!b n. b+n <= w2n dw \/ w2n dw+type_memory_size dtv <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\ type_memory_size dtv <= sz /\
  val_wf dtv v /\ val_in_memory dtv v (w2n dw) t.vs_memory /\
  gas_path_mem ctx fn s g (OK t) /\
  (!tail. new_variable id dtv v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  let ff = es with scopes :=
    (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest in
  gas_marked_exec T (ctx,fn) (new_variable id dtv v) (es,s)
    (REPLICATE g F) (INL ()) ff (OK t) /\
  stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac
  >- (irule gas_marked_exec_no_source_read >>
      simp[gas_marked_path_def]) >>
  `stmt_state_rel ctx fn ce cx
    (es with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest) t` by
    (irule typed_copy_declare_state >> metis_tac[]) >>
  gvs[stmt_state_rel_def, state_rel_gas_obs] >> gvs[]
QED

Theorem widened_declare_copy_continuation_mem:
  compile_assign_value ce (Var p) LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  inst.inst_id < sa.cs_next_id /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  es.scopes = sc::rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_local_ptr ce es.scopes p /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. new_variable id dtv v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  ?marks ff t.
    gas_marked_exec T (ctx,fn) (new_variable id dtv v) (es,s)
      marks (INL ()) ff (OK t) /\
    ff = es with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest /\
    stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ return_buf_frame d ce sb t /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `(!x. src = Var x \/ Var p = Var x ==> not_fresh_at sa x)` by
    (rpt strip_tac >> gvs[]) >>
  Q.SUBGOAL_THEN
    `(?aid. FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id) \/
      (?name. local_region ce es.scopes s name (w2n dw) sz)` assume_tac
  >- metis_tac[] >>
  drule_all widened_local_copy_endpoint_mem >> strip_tac >>
  `lookup_var p u = SOME dw` by
    (first_x_assum (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     simp[eval_operand_def]) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,sz)` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u` by metis_tac[] >>
  drule_all typed_copy_declare_marked_mem >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qexistsl_tac [`REPLICATE g F`, `es with scopes :=
    (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest`, `t`] >>
  simp[] >> gvs[]
QED

Theorem widened_marked_runtime_types[local]:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  gas_marked_exec T (ctx,fn) (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) ==>
  ?stv dtv.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes ce (post_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  irule widened_local_runtime_types >>
  qexistsl_tac [`ee with gas_obs := []`, `env`,
    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
  gvs[ETA_THM] >> metis_tac[]
QED

Theorem widened_internal_call_retained_layout:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  type_widens_to env.type_defs ann dty /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sa = (vv,sb) /\
  gas_marked_exec T (ctx,fn)
    (vyperState$bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) /\
  vv_post ctx fn ce cx (Call ann (IntCall fid) args drv) es sa sb s0
    (ee with gas_obs := []) raw vv t /\
  vv_store_bound cx ann (lowered_value_type ce (Call ann (IntCall fid) args drv))
    (ee with gas_obs := []) raw vv t /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) ==>
  ?stv dtv p w.
    vv = LocatedValue (lowered_value_type ce (Call ann (IntCall fid) args drv)) p /\
    p.ptr_location = LocMemory /\
    evaluate_type (get_tenv cx) (lowered_value_type ce (Call ann (IntCall fid) args drv)) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    0 < type_memory_size stv /\
    eval_operand p.ptr_operand t = SOME w /\
    val_in_memory stv v (w2n w) t.vs_memory /\
    w2n w + type_memory_size stv <= t.vs_alloca_next
Proof
  strip_tac >>
  `post_value_type ce (Call ann (IntCall fid) args drv) =
     lowered_value_type ce (Call ann (IntCall fid) args drv)` by simp[] >>
  `type_widens_to env.type_defs (expr_type (Call ann (IntCall fid) args drv)) dty` by
    simp[expr_type_def] >>
  drule_all widened_marked_runtime_types >> strip_tac >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule normalize_return_source_positive >> metis_tac[]) >>
  `0 < type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[] >>
  drule_all positive_internal_call_memory_layout >> strip_tac >> gvs[] >>
  `val_wf stv v` by simp[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def, vv_holds_def] >> strip_tac >>
  gvs[vv_store_bound_def] >> metis_tac[]
QED

Theorem retained_declaration_destination[local]:
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv t /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id ee.scopes = NONE /\
  lookup_var p s0 = SOME w /\ FLOOKUP s0.vs_allocas aid = SOME (w2n w,sz) /\
  n <= sz /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  gas_marked_exec T (ctx,fn) action (es,s0) marks (INL (v:value)) marked (OK t) /\
  return_buf_frame d ce sa s0 ==>
  lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  w2n w + n <= t.vs_alloca_next /\ w2n w + n < dimword(:256) /\
  local_ptrs_reserved ce sb /\ not_fresh_at sb p /\
  not_local_ptr ce ee.scopes p /\ return_buf_frame d ce sb t /\
  stmt_state_rel ctx fn ce cx ee t /\ ~t.vs_halted
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee t /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)` by
    fs[vv_post_def] >>
  `lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz)` by metis_tac[] >>
  `w2n w + n <= t.vs_alloca_next /\ w2n w + n < dimword(:256)` by
    (drule_all allocated_copy_destination_extent >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[local_ptrs_reserved_not_live] >>
  conj_tac >- (irule return_buf_frame_frame >> metis_tac[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  strip_tac >> drule fragGasPathMemTheory.gas_path_mem_exec >>
  simp[fragExecTheory.exit_result_def]
QED

Theorem retained_copy_type_metadata[local]:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es ==>
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields)
Proof
  fs[bodySimTheory.body_inv_def, exprSimHypsDefsTheory.expr_body_pre_def,
     exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]
QED

Theorem widened_declare_retained_continuation_mem:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  ~is_word_type ann /\ ~is_bytestring_type ann /\
  lowered_value_type ce (Call ann (IntCall fid) args drv) <> ann /\
  compile_expr ce ann (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ann
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sb = ((),sf) /\
  fn_has_code sb sf fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa p /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME dw /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  inst.inst_id < sa.cs_next_id /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  type_memory_bytes ce ann <= sz /\ return_buf_frame d ce sa s0 /\
  gas_admissible (eval_stmt cx (AnnAssign id ann (Call ann (IntCall fid) args drv)))
    (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) ann = SOME dtv /\
  gas_marked_exec T (ctx,fn)
    (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) /\
  vv_post ctx fn ce cx (Call ann (IntCall fid) args drv) es sa sm s0
    (ee with gas_obs := []) raw vv t /\
  vv_store_bound cx ann (lowered_value_type ce (Call ann (IntCall fid) args drv))
    (ee with gas_obs := []) raw vv t /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?right ff u.
    gas_marked_exec T (ctx,fn) (new_variable id dtv v)
      (ee with gas_obs := [],t) right (INL ()) ff (OK u) /\
    stmt_state_rel ctx fn ce cx (ff with gas_obs := []) u /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\ return_buf_frame d ce sf u /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    ?sc rest. ee.scopes = sc::rest /\ ff.scopes =
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest
Proof
  strip_tac >>
  `type_widens_to env.type_defs ann ann` by simp[vyperTypeSystemTheory.type_widens_to_def] >>
  drule_all widened_internal_call_retained_layout >> strip_tac >> gvs[] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  `~is_word_type (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[vyperTypeSystemTheory.type_widens_to_def, compatible_word_type] >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  `?sc rest. ee.scopes = sc::rest /\ lookup_scopes id ee.scopes = NONE /\
    !tail. new_variable id dtv v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest)
        with gas_obs := tail)` by
    (irule annassign_continuation_all_tails >>
     goal_assum (drule_at (Pat `gas_admissible _ _ _`)) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     fs[gas_marked_exec_def]) >>
  `lookup_var p t = SOME dw /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
   w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
   w2n dw + type_memory_size dtv < dimword(:256) /\
   local_ptrs_reserved ce sb /\ not_fresh_at sb p /\
   not_local_ptr ce (ee with gas_obs := []).scopes p /\ return_buf_frame d ce sb t /\
   stmt_state_rel ctx fn ce cx (ee with gas_obs := []) t /\ ~t.vs_halted` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) retained_declaration_destination >>
     disch_then irule >>
     simp[expr_type_def] >>
     conj_tac >- (qexists_tac `id` >> gvs[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[expr_type_def]) >>
  `!x. p'.ptr_operand = Var x ==> not_fresh_at sb x` by
    (drule (CONJUNCT1 compiler_compile_var) >> simp[contextTheory.vv_operand_def]) >>
  `type_memory_size stv < dimword(:256)` by
    (`t.vs_alloca_next < dimword(:256)` by
       metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac) >>
  drule_all retained_copy_type_metadata >> strip_tac >>
  `inst.inst_id < sb.cs_next_id` by
    (drule (CONJUNCT1 compile_expr_grows) >> strip_tac >> decide_tac) >>
  `compile_assign_value ce (Var p) LocMemory p'.ptr_operand F (SOME LocMemory) ann
     (lowered_value_type ce (Call ann (IntCall fid) args drv)) info bytes sb = ((),sf)` by
    fs[contextTheory.vv_location_def] >>
  `!tail. new_variable id dtv v ((ee with gas_obs := []) with gas_obs := tail) =
    (INL (), ((ee with gas_obs := []) with scopes :=
      (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest)
      with gas_obs := tail)` by simp[] >>
  `((ee with gas_obs := []).scopes = sc::rest) /\
    lookup_scopes id (ee with gas_obs := []).scopes = NONE` by gvs[] >>
  `ann <> lowered_value_type ce (Call ann (IntCall fid) args drv) /\
   w2n w + type_memory_size stv <= t.vs_alloca_next` by simp[] >>
  drule_all widened_declare_copy_continuation_mem >> strip_tac >>
  qexistsl_tac [`marks'`, `ff`, `t'`] >>
  simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  gvs[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
