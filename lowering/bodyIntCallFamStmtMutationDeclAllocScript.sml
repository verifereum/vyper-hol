(* The declaration ALLOCA changes only its as-yet inactive pointer. *)
Theory bodyIntCallFamStmtMutationDeclAlloc
Ancestors
  bodyIntCallFamStmtMutationDeclEntry bodyIntCallDeclarationAlloc
  bodyIntCallJointContract compileEnv loweringPosts venomState
  exprLoweringProps stmtSimDefs

Theorem intcall_expr_res_inactive_pointer_frame:
  intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t /\
  not_local_ptr ce es.scopes p /\
  (!op. fp.jc_reserved op ==> op <> Var p) /\
  fp.jc_rpc <> Var p /\
  (!sz. ce.ce_return_pc <> SOME (PtrVar (Var p) sz)) /\
  (!sz. ce.ce_return_buf <> SOME (PtrVar (Var p) sz)) /\
  (!op. op <> Var p ==> eval_operand op t = eval_operand op s) /\
  t.vs_memory = s.vs_memory /\ allocas_above fp.jc_lo t /\
  s.vs_alloca_next <= t.vs_alloca_next /\ local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) ==>
  intcall_expr_res fp ce env es sb t
Proof
  strip_tac >>
  `!q. q <> p ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum (qspec_then `Var q` mp_tac) >>
     simp[eval_operand_def]) >>
  `!n b k. local_region ce es.scopes t n b k ==>
           local_region ce es.scopes s n b k` by
    (fs[not_local_ptr_def, local_region_def] >> metis_tac[]) >>
  fs[intcall_expr_res_def] >> rpt conj_tac >> simp[]
  >- metis_tac[]
  >- metis_tac[]
  >- (fs[ret_pc_ok_def] >> metis_tac[])
  >- (Cases_on `fp.jc_rb` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME rb) ce sb t` >>
      PairCases_on `rb` >> fs[return_buf_frame_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem intcall_declared_alloca_entry:
  emit_inst ALLOCA [Lit bytes] [p] sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit bytes] [p]) (fn_insts fp.jc_func) /\
  intcall_expr_res fp ce env es sa s /\ not_local_ptr ce es.scopes p /\
  (!op. fp.jc_reserved op ==> op <> Var p) /\ fp.jc_rpc <> Var p /\
  (!sz. ce.ce_return_pc <> SOME (PtrVar (Var p) sz)) /\
  (!sz. ce.ce_return_buf <> SOME (PtrVar (Var p) sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_res fp ce env es sb t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,w2n bytes) /\
    fp.jc_lo <= w2n w /\ t.vs_memory = s.vs_memory /\
    (!op. op <> Var p ==> eval_operand op t = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   allocas_above fp.jc_lo s /\ local_ptrs_reserved ce sa` by
    fs[intcall_expr_res_def] >>
  drule_all (SRULE [] (Q.INST [`reserved` |-> `\op. op <> Var p`]
                       (SPEC_ALL declared_alloca_resources))) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (gvs[emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
         compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
         compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def]) >>
  `local_ptrs_reserved ce sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    simp[not_fresh_at_def] >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  irule intcall_expr_res_inactive_pointer_frame >> simp[] >>
  qexistsl_tac [`p`, `s`, `sa`] >> simp[] >> metis_tac[]
QED

Theorem intcall_declare_local_pointer_exclusions:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q k. l = PtrVar q k) ==>
  (!op. fp.jc_reserved op ==> op <> Var p) /\ fp.jc_rpc <> Var p /\
  (!k. c.ce_return_pc <> SOME (PtrVar (Var p) k)) /\
  (!k. c.ce_return_buf <> SOME (PtrVar (Var p) k))
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p` by
    metis_tac[stmtSimDeclTheory.declare_local_old_fresh] >>
  `same_frame ce c` by
    (irule bodySimDeclCasesTheory.declare_local_same_frame >> metis_tac[]) >>
  `c.ce_return_pc = ce.ce_return_pc /\ c.ce_return_buf = ce.ce_return_buf` by
    fs[bodySimTheory.same_frame_def, compile_env_component_equality] >>
  fs[intcall_expr_res_def, intcall_frame_ok_def] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (fs[ret_pc_ok_def] >> metis_tac[]) >>
  Cases_on `fp.jc_rb` >- fs[return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME rb) ce sa s` >>
  PairCases_on `rb` >> fs[return_buf_frame_def] >> metis_tac[]
QED
