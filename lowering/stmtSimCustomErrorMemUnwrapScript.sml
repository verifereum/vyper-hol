Theory stmtSimCustomErrorMemUnwrap
Ancestors
  exprSimMemoryRead exprSimMemUnwrap bodyFieldMemoryProps
  exprSimUnwrapProps exprSimProps exprLoweringProps loweringPosts
  exprSimMemDefs gasSummary fragGasMode fragGasPath
  valueEncodingProps venomState compileEnv vyperState valueCopyBytes
  context emitHelperProps venomExecProofs exprSimMemorySource
  exprSimMemoryPath fragGasPathMem vyperValue valueEncoding
  exprSimHyps exprSimHypsDefs aggregateEvaluatedLayout vyperTypeArgFits
  vyperTypeSystem

Theorem unwrap_memory_marked_read_mem:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
    ee tv (LocatedValue t p) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (is_word_type t ==> t = expr_type e /\
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `?w v. eval_operand p.ptr_operand s = SOME w /\
         read_result cx tv ee = (INL v,ee)` by
    gvs[vv_post_def, vv_holds_def] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  `!u. gas_path_mem ctx func s 0 (OK u) ==>
       gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s) [] (INL v) ee (OK u)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[read_result_gas_obs]) >>
  reverse (Cases_on `is_word_type t`)
  >- (gvs[unwrap_memory_compile, comp_return_def] >>
      qexistsl_tac [`v`, `s`] >> simp[] >> conj_tac
      >- (first_x_assum irule >> simp[gas_path_mem_rules]) >>
      irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (gvs[] >>
     `val_store_size tvt v = 32` by
       (drule_all word_tv_memory_size >> strip_tac >>
        Cases_on `expr_type e` >> gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
        Cases_on `v` >> simp[val_store_size_def]) >>
     qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def] >> metis_tac[]) >>
  gvs[unwrap_memory_compile] >>
  drule_all body_word_load_run_post >> strip_tac >>
  `alloca_inv s` by gvs[vv_post_def, stmt_state_rel_def] >>
  drule_all body_word_load_history >> strip_tac >>
  drule_all body_word_load_gas_path >> strip_tac >>
  qexistsl_tac [`v`, `q with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[body_field_expr_post_inst_idx] >>
  drule emit_op_extends >> gvs[same_blocks_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule step_MLOAD >>
  disch_then (qspecl_then [`sm.cs_next_id`, `STRING #"%" (toString sm.cs_next_var)`]
    assume_tac) >>
  gvs[run_inst_seq_def, update_var_def]
QED

Theorem unwrap_memory_marked_read_body_mem:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
    ee tv (LocatedValue t p) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  expr_body_pre cenv cx env e es /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `is_word_type t ==> t = expr_type e /\
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` by
  (strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env e` by
    gvs[expr_body_pre_def] >>
  drule_all post_value_type_widens >>
  simp[type_widens_to_def] >> strip_tac >>
  `t = post_value_type cenv e` by
    (gvs[vv_post_def, vv_holds_def] >>
     Cases_on `t` >> gvs[is_word_type_def, is_bytestring_type_def] >>
     Cases_on `b` >> gvs[is_word_type_def, is_bytestring_type_def] >>
     Cases_on `b'` >> gvs[is_word_type_def, is_bytestring_type_def]) >>
  `is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  simp[] >> metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS]) >>
  irule unwrap_memory_marked_read_mem >> metis_tac[]
QED
