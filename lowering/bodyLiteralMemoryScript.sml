Theory bodyLiteralMemory
Ancestors
  bodyMemoryDefs exprSimLeaves exprSimHyps exprSimUnwrap
  exprLowering exprLoweringProps fragExecMem
  vyperAST vyperInterpreter vyperTyping valueEncoding
  vyperTypeSystem compileEnv context vyperState exprSim
  vyperValueOperation venomState vyperValue loweringSlice

Theorem body_literal_word_compile[local]:
  expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  ?op. compile_expr cenv ty (Literal ann l) sa = (StackValue ann op,sa)
Proof
  strip_tac >>
  `~(?str. l = StringL str)` by
    (strip_tac >> gvs[expr_sim_pre_def, well_typed_expr_def] >>
     Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  Cases_on `l` >> gvs[]
  >~ [`BytesL bs`]
  >- (`!n. ann <> BaseT (BytesT (Dynamic n))` by
        (rpt strip_tac >> gvs[is_word_type_def]) >>
      simp[compile_expr_def, expr_type_def] >> irule compile_literal_bytes_stack >> simp[]) 
  >~ [`BoolL b`]
  >- (Cases_on `b` >> simp[compile_expr_def, compile_literal_vv_def, expr_type_def, comp_return_def]) >>
  simp[compile_expr_def, compile_literal_vv_def, expr_type_def, comp_return_def]
QED

val literal_word_mem_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def, expr_type_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def, is_word_type_def, evaluate_type_def];

Theorem compile_literal_word_body_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_sim_mem_def] >>
  gvs[Once evaluate_def, bind_def, read_result_def, return_def,
      expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_mem_tac)
  >~ [`IntL i`] >- literal_word_mem_tac
  >~ [`DecimalL i`] >- literal_word_mem_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
      literal_word_mem_tac) >>
  literal_word_mem_tac
QED

val literal_word_vv_mem_tac =
  gvs[compile_expr_def, comp_return_def, compile_literal_vv_def,
      evaluate_literal_def, expr_type_def] >>
  irule frag_exec_mem_refl >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def, vv_operand_def,
       vv_location_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def, is_word_type_def, evaluate_type_def];

Theorem compile_literal_word_body_vv_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_vv_sim_mem ctx func cenv cx ty (Literal ann l) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_vv_sim_mem_def] >>
  gvs[Once evaluate_def, return_def, expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_vv_mem_tac)
  >~ [`IntL i`] >- literal_word_vv_mem_tac
  >~ [`DecimalL i`] >- literal_word_vv_mem_tac >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
      literal_word_vv_mem_tac) >>
  literal_word_vv_mem_tac
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_WORD_LITERAL_MEMORY_AUDIT OK\n"
     else raise Fail "word literal memory inherited admission"
  end) [body_literal_word_compile, compile_literal_word_body_sim_mem,
        compile_literal_word_body_vv_sim_mem];
