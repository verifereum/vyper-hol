Theory bodyPtrBytestringBuiltinsUintResult
Ancestors
  bodyPtrBytestringBuiltinsUintReady bodyPtrBytestringBuiltinsUint2Str
  bodyPtrAttributeFields wordArgsPtr exprSimHash exprSimUint2Str
  bodyPtrDefs loweringPosts venomState venomExecSemantics ptrDiscipline
  compileEnv contextCodegenRel codegenRel words list arithmetic vyperState

Theorem ptr_covers_buffer_post:
  ptr_covers G tn p s sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem u2s_result_ptr_post:
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  type_memory_bytes cenv (lowered_value_type cenv e) =
    type_memory_size (BaseTV (StringT cap)) /\
  type_memory_size (BaseTV (StringT cap)) <= sz /\
  val_wf (BaseTV (StringT cap)) (StringV str) /\
  ptr_covers G tn p s sz /\ lookup_var p s = SOME (n2w addr) /\
  addr < dimword(:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (StringT cap)) (StringV str) addr mem) ==>
  ptr_buf_ok cenv e (Var p) G s /\
  ptr_vv_ok cx (expr_type e) (Value (StringV str))
    (LocatedValue (expr_type e) <|ptr_operand := Var p; ptr_location := LocMemory|>)
    es G tn s
Proof
  strip_tac >>
  `ptr_buf_ok cenv e (Var p) G s` by
    (irule ptr_covers_buffer_post >> goal_assum (drule_at Any) >> simp[]) >>
  simp[ptr_vv_ok_def, read_result_def, vyperStateTheory.return_def] >>
  conj_tac >- gvs[ptr_covers_def] >>
  irule ptr_mem_ok_of_buffer >> simp[eval_operand_def, w2n_n2w] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[eval_operand_def, w2n_n2w] >>
  `addr MOD dimword(:256) = addr` by simp[] >> metis_tac[]
QED

Theorem u2s_alloc_loop_ghost_kept:
  compile_alloc_buffer sz sa = (ba,a) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  wb_frame cenv es sa s ready /\
  ghost_kept cenv es sa G tn s G1 tn1 /\
  ghost_kept cenv es a G1 tn1 ready G2 tn2 ==>
  ghost_kept cenv es sa G tn s G2 tn2
Proof
  strip_tac >> drule u2s_alloc_compiler_control >> strip_tac >>
  `sa.cs_next_id <= a.cs_next_id` by
    (mp_tac (Q.SPECL [`sz`, `sa`]
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  irule ghost_kept_wb_trans >> simp[] >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`G1`, `es`, `ready`, `a`, `tn1`] >> simp[]
QED

Theorem u2s_result_control:
  u2s_layout a op buf n sb /\
  t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 ==>
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[u2s_layout_def, u2s_end_def] >> metis_tac[]
QED

Theorem u2s_result_vv_post:
  compile_alloc_buffer (sz+n) sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ out = Var (u2s_var a 2) /\
  inst.inst_id = sa.cs_next_id /\
  u2s_safe ctx fn cenv cx es a ba.buf_operand b (sz+n) inst sr t /\
  wb_frame cenv es sa s t /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v addr t.vs_memory /\
  lookup_var (u2s_var a 2) t = SOME (n2w addr) /\
  addr < dimword(:256) /\ b <= addr /\
  addr + val_footprint tv v <= b+(sz+n) ==>
  vv_post ctx fn cenv cx e es sa sb s es (Value v)
    (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) t
Proof
  strip_tac >> drule u2s_alloc_compiler_control >> strip_tac >>
  `sa.cs_next_id <= a.cs_next_id` by
    (mp_tac (Q.SPECL [`sz+n`, `sa`]
      exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `sa.cs_next_id < sb.cs_next_id` by
    gvs[u2s_layout_def, u2s_end_def] >>
  irule vv_post_allocated_memory_intro >>
  simp[eval_operand_def, w2n_n2w] >>
  reverse conj_tac >- gvs[u2s_safe_def] >>
  qexistsl_tac [`sa.cs_next_id`, `b`, `sz+n`] >> simp[] >>
  gvs[u2s_safe_def] >> metis_tac[]
QED
