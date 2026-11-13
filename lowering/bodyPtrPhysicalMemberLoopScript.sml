(* Literal traversal uses physical child-store endpoints. *)
Theory bodyPtrPhysicalMemberLoop
Ancestors
  bodyPtrPhysicalMemberOutcome bodyPtrPhysicalLiteralLoop
  bodyPtrMakeArrayTupleLoop bodyPtrPhysicalChildStore
  bodyPtrMakeArrayConsOutcome exprLowering exprLoweringProps emitHelperProps
  compileEnv context bodyPtrMakeArrayConsBind gasSummaryComposePtr
  fragGasPathPtr gasExemptCert gasSummary vyperState exprSimHyps
  exprSimWordArgs bodyPtrMakeArrayConsInvariant valueEncoding valueEncodingDefs argsTailPtr
  assignTuplePtrBodyReady freshWrites list option fragExec
  bodyPtrMakeArrayChildren
  exprSimAggregateLoops exprSimAggregateEncoding

Theorem literal_tuple_members_outcome_ptr_physical:
  !args tys ce cx env off si out sb es tvs cells G0 tn0 s0.
  compile_make_tuple compile_expr ce args tys (Var root) off si = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
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
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s0,G0,tn0)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
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
  Cases_on `tys` >- fs[] >>
  rename1 `compile_make_tuple compile_expr ce (hd::args) (dty::dtys) _ _ _ = _` >>
  fs[AllCaseEqs()] >>
  rename1 `evaluate_type (get_tenv cx) dty = SOME dtv` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME dtvs` >>
  drule compile_make_tuple_cons >> strip_tac >>
  `?dst_name. dst = Var dst_name` by
    (drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
  fs[] >>
  rename1 `compile_store_memory _ _ _ _ _ su = ((),ss)` >>
  suspend "cons"
QED

Resume literal_tuple_members_outcome_ptr_physical[cons]:
  markerLib.RESUME_TAC >>
  fs[AllCaseEqs()] >>
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
  `expr_body_pre ce cx env hd es /\
   expr_vv_sim_ptr d ctx PG func ce cx (expr_type hd) hd es` by
    metis_tac[literal_body_child_vv] >>
  `gas_admissible (eval_expr cx hd) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `off + type_memory_bytes ce dty <= capacity` by
    (qpat_x_assum `_ = tvs` (assume_tac o SYM) >>
     fs[type_memory_size_def] >> decide_tac) >>
  `off + type_memory_size dtv <= capacity` by metis_tac[] >>
  `(pure ==> ~expr_has_effect hd) /\ (pure ==> ~EXISTS expr_has_effect args)` by
    (rpt strip_tac >> fs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`e` |-> `hd`, `sb` |-> `ss`, `tv` |-> `dtv`,
      `dst` |-> `dst_name`, `k` |-> `type_memory_bytes ce dty`]
    (SPEC_ALL literal_member_outcome_ptr_physical)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `out = Var root` by metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  simp[] >> rewrite_tac[literal_tuple_eval_cons] >>
  irule literal_value_bind_outcome_ptr >>
  irule_at Any gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  simp[] >>
  qexists `\v ee H tm z. value_has_type dtv v /\
    literal_loop_frame pure ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf ee ss H tm z
      (cells ++ [(dtv,v,addr+off,type_memory_size dtv)]) (off+type_memory_size dtv) /\
    literal_prefix_ok (cells ++ [(dtv,v,addr+off,type_memory_size dtv)]) tm z` >>
  (conj_tac >- (simp[] >> metis_tac[])) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce cx env ee` by (drule_all literal_marked_value_inv >> simp[]) >>
  `body_exprs_ptr_ok cx args` by (drule_all literal_marked_children_tail >> simp[]) >>
  suspend "tail"
QED
Resume literal_tuple_members_outcome_ptr_physical[tail]:
  markerLib.RESUME_TAC >>
  fs[] >>
  `local_ptrs_reserved ce ss` by metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at ss p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at ss p)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `off + type_memory_size dtv + type_memory_size_list dtvs <= capacity` by
    (qpat_x_assum `_ = tvs` (assume_tac o SYM) >>
     fs[type_memory_size_def] >> decide_tac) >>
  qpat_x_assum `!tys' ce' cx' env' off' si' out' sb' es' tvs' cells' G0' tn0' s0'. _`
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qexists `[(dtv,v,addr+off,type_memory_size dtv)] ++ added` >>
      simp[APPEND_ASSOC, type_memory_size_def] >>
      rpt strip_tac >> simp[val_in_memory_def] >>
      metis_tac[literal_prefix_cell, arithmeticTheory.ADD_ASSOC]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qexists `[(dtv,v,addr+off,type_memory_size dtv)] ++ added` >>
  simp[APPEND_ASSOC, type_memory_size_def] >>
  rpt strip_tac >> simp[val_in_memory_def] >>
  metis_tac[literal_prefix_cell, arithmeticTheory.ADD_ASSOC]
QED
Finalise literal_tuple_members_outcome_ptr_physical

Theorem literal_array_members_outcome_ptr_physical:
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var root) idx si = (out,sb) /\
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  off = (if header then 32 else 0) + idx * type_memory_bytes ce elem_ty /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
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
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s0,G0,tn0)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ added)
          (off + type_memory_size_list (REPLICATE (LENGTH args) tv)) /\
      literal_prefix_ok (cells ++ added) tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        tuple_in_memory vs (REPLICATE (LENGTH args) tv) (addr+off) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  `LIST_REL (\t e. arg_type_fits (expr_type e) t)
     (REPLICATE (LENGTH args) elem_ty) args` by
    (qpat_x_assum `EVERY (\e. arg_type_fits (expr_type e) elem_ty) args` mp_tac >>
     rpt (pop_assum kall_tac) >> Induct_on `args` >> simp[]) >>
  `!n. OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE n elem_ty) =
     SOME (REPLICATE n tv)` by (Induct >> simp[]) >>
  mp_tac (Q.INST [`tys` |-> `REPLICATE (LENGTH args) elem_ty`,
      `tvs` |-> `REPLICATE (LENGTH args) tv`]
    (SPEC_ALL literal_tuple_members_outcome_ptr_physical)) >>
  (impl_tac >- gvs[compile_make_array_elems_as_tuple]) >> simp[]
QED
