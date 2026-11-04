(* Counted forcing of address and fixed-byte literals. *)
Theory exprSimLiteralBytes
Ancestors
  exprSimHypsDefs exprSimProps exprSimDefs loweringPosts
  gasOutcome gasSummary gasNormalPrefix fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState vyperValue vyperValueOperation vyperTypeSystem
  valueEncoding valueEncodingProofs fragExec venomInst venomState

val literal_bytes_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def, bind_def, read_result_def, return_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def];

(* An address or bytesN literal: a Lit of its typed encoding, the 20 bytes
   of an address right-aligned and the bytes of a bytesN left-aligned, as
   expr_val_rel has them.  No code. *)
Theorem compile_literal_bytes_word_sim:
  !ctx func cenv cx env ty ann bs es.
    expr_sim_pre cenv cx env (Literal ann (BytesL bs)) es /\
    is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann (BytesL bs)) es
Proof
  rw[expr_sim_def] >> gvs[Once evaluate_def, return_def, expr_sim_pre_def,
                          well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
                       literal_bytes_word_tac) >>
  literal_bytes_word_tac
QED

