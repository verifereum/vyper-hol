(* Prefix the uniform fields loop with its counted allocation path. *)
Theory bodyPtrStructLitUniformAllocated
Ancestors bodyPtrStructLitUniformFieldsLoop bodyPtrMakeArrayPackage
  bodyPtrMakeArrayConsInvariant exprLoweringProps fragExec freshWrites
  gasSummaryComposePtr

Theorem structlit_uniform_allocated_fields_outcome_ptr:
  compile_alloc_buffer (type_memory_size_list tvs) sa = (buf,sm) /\
  buf.buf_operand = Var root /\
  compile_struct_lit compile_expr ce sty fields (Var root) 0 sm = (out,sb) /\
  EVERY (\(name,e). ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case sty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ type_memory_size_list tvs < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx (MAP SND fields) /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e (MAP SND fields) ==> post_value_type ce e = expr_type e) ==>
  out = Var root /\
  ?addr. addr + type_memory_size_list tvs < dimword(:256) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (MAP SND fields)) (es,s,G,tn)
    (\res ee H tm z. ?vs cells. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
        es sa s G tn ee sb H tm z cells (type_memory_size_list tvs) /\
      literal_prefix_ok cells tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs)) addr m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all literal_allocated_loop_start >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    structlit_uniform_fields_loop_outcome_ptr >> simp[] >>
  disch_then (drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)) >> simp[] >>
  disch_then drule_all >> disch_then (qspec_then `PG` strip_assume_tac) >>
  simp[] >> qexists `addr` >> simp[] >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >> fs[] >>
  qexists `0` >> first_assum ACCEPT_TAC
QED
