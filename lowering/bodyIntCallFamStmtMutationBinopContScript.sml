(* Word-binop normal endpoints retain the internal-call resource boundary.
   The exceptional alternative is exactly the operator interface's exit. *)
Theory bodyIntCallFamStmtMutationBinopCont
Ancestors
  bodyIntCallFamStmtMutationBinop bodyIntCallJointContract exprBopSimDefs
  exprLoweringProps compileEnv exprSimDefs gasSummary venomExecSemantics

Theorem intcall_binop_frag_words_cont:
  binop_frag_words fp.jc_ctx fp.jc_func ce fp.jc_cx
    bop ty ann bl el tys v1 v2 w1 w2 es /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  expr_res_ok (bop_result fp.jc_cx ann bop tys v1 v2 es) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  eval_operand x s = SOME w1 /\ eval_operand y s = SOME w2 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F fp.jc_ctx fp.jc_func s 0 r /\
    ((?u v. r = OK u /\
       bop_result fp.jc_cx ann bop tys v1 v2 es = INL v /\
       word_value v /\
       eval_operand op u = SOME (val_to_w256 v) /\
       u.vs_memory = s.vs_memory /\
       intcall_expr_cont fp ce env es sa s es sb u) \/
     (exit_result r /\
      expr_exit (bop_result fp.jc_cx ann bop tys v1 v2 es) r))
Proof
  strip_tac >>
  `local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  drule compile_binop_grows >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qpat_x_assum `binop_frag_words _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[binop_frag_words_def] >>
  disch_then drule_all >> strip_tac
  >- (gvs[] >> rename1 `gas_marked_path F _ _ _ 0 (OK u)` >>
      qexists `OK u` >> simp[] >>
      irule intcall_expr_cont_readonly_path >>
      metis_tac[]) >>
  qexists `r` >> simp[]
QED
