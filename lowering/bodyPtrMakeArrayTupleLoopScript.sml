(* Compilation boundary for the counted literal loop.  Keep the source
   type of each store: the operational cons handles capacity widening. *)
Theory bodyPtrMakeArrayTupleLoop
Ancestors
  bodyPtrMakeArrayConsOutcome exprLowering exprLoweringProps emitHelperProps
  compileEnv context bodyPtrMakeArrayConsBind gasSummaryComposePtr
  fragGasPathPtr gasExemptCert gasSummary vyperState exprSimHyps
  exprSimWordArgs bodyPtrMakeArrayConsInvariant valueEncoding valueEncodingDefs argsTailPtr
  assignTuplePtrBodyReady freshWrites list option fragExec
  bodyPtrMakeArrayChildren
  exprSimAggregateLoops exprSimAggregateEncoding

Theorem literal_tuple_cons_compile:
  compile_make_tuple compile_expr ce (e::args) (Var root) off sa = (out,sb) ==>
  ?vv sm dst sn op su ss.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),ss) /\
    compile_make_tuple compile_expr ce args (Var root)
      (off+type_memory_bytes ce (expr_type e)) ss = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* The cons outcome materialises a value, not an eval_result.  Retain its
   actual marked execution when applying the tail induction hypothesis. *)
Theorem literal_value_bind_outcome_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (a : evaluation_state -> value evaluation_result) (es,s0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\ P v ee G tn t)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!marks v ee G tn t.
    gas_marked_exec_ptr D (ctx,func) PG a (es,s0,G0,tn0)
      marks (INL v) ee G tn (OK t) /\
    ee.gas_obs = [] /\ P v ee G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG
      (k v : evaluation_state -> 'b evaluation_result) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind a k) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[] >>
      first_x_assum (qspecl_then
        [`left`, `v`, `es_end with gas_obs := []`, `G`, `tn`, `t`] mp_tac) >>
      (impl_tac >- fs[literal_marked_exec_end_gas_obs]) >>
      rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_ptr_bind_normal])
      >- (qexists `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_ptr_bind_normal]) >>
      qexists `left ++ right` >> disj2_tac >>
      rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule_at Any gas_exempt_cert_bind_value >>
      simp[GSYM ignore_bind_def] >> metis_tac[gas_marked_exec_ptr_exec])
  >- (gvs[] >> qexists `left` >> disj1_tac >>
      metis_tac[gas_marked_exec_ptr_bind_exception]) >>
  qexists `left` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_error_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem literal_tuple_nil_outcome_ptr:
  ~s.vs_halted /\ Q (INL []) (es with gas_obs := []) G tn s ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_exprs cx []) (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists `[]` >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [`INL []`, `es`, `G`, `tn`, `OK s`] >>
  simp[exprSimWordArgsTheory.eval_exprs_nil] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem literal_loop_frame_gas_obs[simp]:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf (es with gas_obs := gs) cs G tn s cells off <=>
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off
Proof
  simp[literal_loop_frame_def, bodyPtrDefsTheory.ghost_inv_def]
QED

Theorem literal_tuple_eval_cons:
  eval_exprs cx (e::args) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [vyperInterpreterTheory.evaluate_def])) >>
  simp[bind_assoc]
QED

Theorem literal_marked_value_inv:
  expr_body_pre ce cx env e es /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) ee G tn (OK t) /\ ee.gas_obs = [] ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all expr_body_pre_eval_gas_ptr >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem literal_tuple_loop_outcome_ptr:
  !args ce cx env off si out sb es tvs cells G0 tn0 s0.
  compile_make_tuple compile_expr ce args (Var root) off si = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  off + type_memory_size_list tvs <= capacity /\
  fn_has_code si sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s0,G0,tn0)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ added) (off + type_memory_size_list tvs) /\
      literal_prefix_ok (cells ++ added) tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        tuple_in_memory vs tvs (addr+off) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_make_tuple_def, comp_return_def] >>
      irule literal_tuple_nil_outcome_ptr >>
      conj_tac >- metis_tac[literal_loop_frame_runtime] >>
      simp[] >> qexists `[]` >> simp[type_memory_size_def, val_in_memory_def]) >>
  rpt gen_tac >> strip_tac >>
  drule literal_tuple_cons_compile >> strip_tac >>
  suspend "cons"
QED

Resume literal_tuple_loop_outcome_ptr[cons]:
  gvs[AllCaseEqs()] >>
  `ci_mono ss sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono si sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono si ss` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code si ss func /\ fn_has_code ss sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_body_pre ce cx env h es /\
   expr_vv_sim_ptr d ctx PG func ce cx (expr_type h) h es` by
    metis_tac[literal_body_child_vv] >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `type_memory_bytes ce (expr_type h) = type_memory_size h'` by
    metis_tac[expr_sim_inv_memory_size] >>
  `off + type_memory_bytes ce (expr_type h) <= capacity` by
    (fs[type_memory_size_def] >> decide_tac) >>
  qpat_assum `!e. e = h \/ MEM e args ==> _`
    (qspec_then `h` (assume_tac o SRULE [])) >>
  `off + type_memory_size h' <= capacity` by metis_tac[] >>
  drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [] literal_cons_outcome_ptr) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `out = Var root` by metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  simp[] >> rewrite_tac[literal_tuple_eval_cons] >>
  irule literal_value_bind_outcome_ptr >>
  irule_at Any gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  simp[] >>
  qexists `\v ee H tm z. value_has_type h' v /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf ee ss H tm z
      (cells ++ [(h',v,addr+off,type_memory_size h')]) (off+type_memory_size h') /\
    literal_prefix_ok (cells ++ [(h',v,addr+off,type_memory_size h')]) tm z` >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce cx env ee` by metis_tac[literal_marked_value_inv] >>
  `body_exprs_ptr_ok cx args` by metis_tac[literal_marked_children_tail] >>
  suspend "tail"
QED
Resume literal_tuple_loop_outcome_ptr[tail]:
  fs[] >>
  `local_ptrs_reserved ce ss` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at ss p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at ss p)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `off + type_memory_size h' + type_memory_size_list t <= capacity` by
    (fs[type_memory_size_def] >> decide_tac) >>
  qpat_x_assum `!ce' cx' env' off' si' out' sb' es' tvs' cells' G0' tn0' s0'. _`
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qexists `[(h',v,addr+off,type_memory_size h')] ++ added` >>
      simp[APPEND_ASSOC, type_memory_size_def] >>
      rpt strip_tac >> simp[val_in_memory_def] >>
      metis_tac[literal_prefix_cell, arithmeticTheory.ADD_ASSOC]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qexists `[(h',v,addr+off,type_memory_size h')] ++ added` >>
  simp[APPEND_ASSOC, type_memory_size_def] >>
  rpt strip_tac >> simp[val_in_memory_def] >>
  metis_tac[literal_prefix_cell, arithmeticTheory.ADD_ASSOC]
QED
Finalise literal_tuple_loop_outcome_ptr

Theorem literal_array_loop_outcome_ptr:
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var root) idx si = (out,sb) /\
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  off = (if header then 32 else 0) + idx * type_memory_bytes ce elem_ty /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= capacity /\
  fn_has_code si sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s0,G0,tn0)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ added)
          (off + type_memory_size_list (REPLICATE (LENGTH args) tv)) /\
      literal_prefix_ok (cells ++ added) tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        tuple_in_memory vs (REPLICATE (LENGTH args) tv) (addr+off) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  drule compile_make_array_elems_as_tuple >>
  disch_then (qspecl_then [`header`, `compile_expr`, `ce`, `Var root`, `idx`] assume_tac) >>
  irule literal_tuple_loop_outcome_ptr >>
  simp[] >> conj_tac >- metis_tac[OPT_MMAP_uniform_map] >>
  conj_tac >- metis_tac[] >>
  qexists `si` >> gvs[arithmeticTheory.ADD_COMM]
QED
