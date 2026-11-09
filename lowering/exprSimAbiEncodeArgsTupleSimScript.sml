Theory exprSimAbiEncodeArgsTupleSim
Ancestors
  exprSimAbiEncodeArgsTuplePost exprSimAbiEncodeArgsTupleContracts
  exprSimAbiEncodeArgsTupleSource exprSimAbiEncodeArgsTupleLayout
  exprSimAbiEncodeArgsTupleTarget exprSimWordArgs
  gasOutcome gasSummary gasCount loweringPosts exprLowering compileEnv
  vyperState context

Theorem tuple_source_zero_outcome:
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk /\
  gas_marked_path F ctx fn s 0 (OK t) /\
  Q (INL (Value (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))))
    (es with gas_obs := []) t ==>
  gas_outcome F tops (ctx,fn) (eval_expr cx tuple_call) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])))`,
                `es`, `OK t`] >>
  simp[gas_marked_exec_def, tuple_call_evaluation]
QED

Theorem tuple_value_zero_outcome:
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk /\
  gas_marked_path F ctx fn s 0 (OK t) /\
  Q (INL (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])))
    (es with gas_obs := []) t ==>
  gas_outcome F tops (ctx,fn)
    (bind (eval_expr cx tuple_call) (read_result cx)) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))`,
                `es`, `OK t`] >>
  simp[gas_marked_exec_def, tuple_call_evaluation, bind_def,
       read_result_def, return_def]
QED

Theorem tuple_posts_clear_gas:
  expr_post ctx fn ce cx tuple_call es sa sb s es v op t /\
  vv_post ctx fn ce cx tuple_call es sa sb s es (Value v) (LocatedValue tuple_narrow (base_ptr buf)) t ==>
  expr_post ctx fn ce cx tuple_call es sa sb s (es with gas_obs := []) v op t /\
  vv_post ctx fn ce cx tuple_call es sa sb s (es with gas_obs := []) (Value v) (LocatedValue tuple_narrow (base_ptr buf)) t
Proof
  simp[expr_post_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
       expr_val_at_def, expr_val_own_def, local_region_def, locals_kept_def,
       popped_kept_def, read_result_def, return_def, base_ptr_def] >>
  strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem tuple_vv_judgment:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk ==>
  !ty es sa sb vv s.
    compile_expr ce ty tuple_call sa = (vv,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel (tuple_target_context name ctx) fn ce cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (tuple_target_context name ctx,fn)
      (eval_expr cx tuple_call) (es,s)
      (\res ee t. ?tv. res = INL tv /\
        vv_post (tuple_target_context name ctx) fn ce cx tuple_call es sa sb s ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> rpt gen_tac >>
  drule tuple_actual_call_compile >>
  disch_then (qspecl_then [`ty`,`sa`] mp_tac) >>
  Cases_on `compile_alloc_buffer 128 sa` >>
  rename1 `compile_alloc_buffer 128 sa = (buf,sm)` >>
  Cases_on `emit_void INVOKE [Label name; buf.buf_operand] sm` >>
  Cases_on `q` >>
  fs[] >> rpt strip_tac >> gvs[] >>
  drule_all tuple_target_allocated_posts >> strip_tac >>
  drule_all tuple_target_post_interfaces >> strip_tac >>
  drule_all tuple_posts_clear_gas >> strip_tac >>
  irule tuple_source_zero_outcome >> simp[] >>
  qexists_tac `t` >> simp[]
QED

Theorem tuple_expr_judgment:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk ==>
  !ty es sa sb op s.
    lower_value compile_expr ce ty tuple_call sa = (op,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel (tuple_target_context name ctx) fn ce cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (tuple_target_context name ctx,fn)
      (bind (eval_expr cx tuple_call) (read_result cx)) (es,s)
      (\res ee t. ?v. res = INL v /\
        expr_post (tuple_target_context name ctx) fn ce cx tuple_call es sa sb s ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> rpt gen_tac >>
  drule tuple_actual_call_compile >>
  disch_then (qspecl_then [`ty`,`sa`] mp_tac) >>
  Cases_on `compile_alloc_buffer 128 sa` >>
  rename1 `compile_alloc_buffer 128 sa = (buf,sm)` >>
  Cases_on `emit_void INVOKE [Label name; buf.buf_operand] sm` >>
  Cases_on `q` >> fs[] >> strip_tac >>
  simp[tuple_actual_unwrap, tuple_target_unwrap_buffer] >>
  rpt strip_tac >> gvs[tuple_target_unwrap_buffer] >>
  drule_all tuple_target_allocated_posts >> strip_tac >>
  drule_all tuple_target_post_interfaces >> strip_tac >>
  drule_all tuple_posts_clear_gas >> strip_tac >>
  irule tuple_value_zero_outcome >> simp[] >>
  qexists_tac `t` >> simp[]
QED

Theorem tuple_universal_cases:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk ==>
  exprs_case F (tuple_target_context name ctx) fn ce cx [tuple_call]
Proof
  strip_tac >> rewrite_tac[tuple_joint_contracts] >> conj_tac
  >- (rpt strip_tac >> drule_all tuple_expr_judgment >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> drule_all tuple_vv_judgment >>
  disch_then irule >> simp[]
QED

Theorem tuple_vv_judgment_in_context:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk /\
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) ==>
  !ty es sa sb vv s.
    compile_expr ce ty tuple_call sa = (vv,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,fn) (eval_expr cx tuple_call) (es,s)
      (\res ee t. ?tv. res = INL tv /\
        vv_post ctx fn ce cx tuple_call es sa sb s ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> rpt gen_tac >>
  drule tuple_actual_call_compile >>
  disch_then (qspecl_then [`ty`,`sa`] mp_tac) >>
  Cases_on `compile_alloc_buffer 128 sa` >>
  rename1 `compile_alloc_buffer 128 sa = (buf,sm)` >>
  Cases_on `emit_void INVOKE [Label name; buf.buf_operand] sm` >>
  Cases_on `q` >> fs[] >> rpt strip_tac >> gvs[] >>
  drule_all tuple_target_allocated_posts_in_context >> strip_tac >>
  drule_all tuple_target_post_interfaces >> strip_tac >>
  drule_all tuple_posts_clear_gas >> strip_tac >>
  irule tuple_source_zero_outcome >> simp[] >>
  qexists_tac `t` >> simp[]
QED

Theorem tuple_expr_judgment_in_context:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk /\
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) ==>
  !ty es sa sb op s.
    lower_value compile_expr ce ty tuple_call sa = (op,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,fn)
      (bind (eval_expr cx tuple_call) (read_result cx)) (es,s)
      (\res ee t. ?v. res = INL v /\
        expr_post ctx fn ce cx tuple_call es sa sb s ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> rpt gen_tac >>
  drule tuple_actual_call_compile >>
  disch_then (qspecl_then [`ty`,`sa`] mp_tac) >>
  Cases_on `compile_alloc_buffer 128 sa` >>
  rename1 `compile_alloc_buffer 128 sa = (buf,sm)` >>
  Cases_on `emit_void INVOKE [Label name; buf.buf_operand] sm` >>
  Cases_on `q` >> fs[] >> strip_tac >>
  simp[tuple_actual_unwrap, tuple_target_unwrap_buffer] >>
  rpt strip_tac >> gvs[tuple_target_unwrap_buffer] >>
  drule_all tuple_target_allocated_posts_in_context >> strip_tac >>
  drule_all tuple_target_post_interfaces >> strip_tac >>
  drule_all tuple_posts_clear_gas >> strip_tac >>
  irule tuple_value_zero_outcome >> simp[] >>
  qexists_tac `t` >> simp[]
QED

Theorem tuple_universal_cases_in_context:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  name = internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
    (nsid_to_string (NONE,"f"))
    (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor /\
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk /\
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) ==>
  exprs_case F ctx fn ce cx [tuple_call]
Proof
  strip_tac >> rewrite_tac[tuple_joint_contracts] >> conj_tac
  >- (rpt strip_tac >> drule_all tuple_expr_judgment_in_context >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> drule_all tuple_vv_judgment_in_context >>
  disch_then irule >> simp[]
QED
