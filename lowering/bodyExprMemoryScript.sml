(* Actual expression producers for the memory body induction. *)
Theory bodyExprMemory
Ancestors
  bodyMemoryDefs exprSim exprSimHyps bodySim fragExecMem loweringSlice
  exprLowering context compileEnv vyperInterpreter vyperValue vyperState
  vyperValueOperation valueEncoding valueEncodingProofs venomState venomExecSemantics

Theorem body_bool_literal_mem:
  !tops ctx func cenv cx env ty b es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Literal (BaseT BoolT) (BoolL b)) es ==>
    expr_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es /\
    expr_vv_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  rw[expr_sim_mem_def, expr_vv_sim_mem_def] >>
  gvs[Once evaluate_def, bind_def, read_result_def, return_def,
      lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vv_post_def, vv_holds_def, vv_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       locals_kept_mem, is_word_type_def, read_result_def, return_def]
QED

val () =
  let val th = body_bool_literal_mem
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_EXPR_MEMORY_AUDIT OK\n"
     else raise Fail "body expression inherited admission"
  end;
