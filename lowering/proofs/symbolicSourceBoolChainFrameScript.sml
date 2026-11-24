Theory symbolicSourceBoolChainFrame
Ancestors
  symbolicSourceCompilerFrame exprLowering compileEnv vyperAST list
Libs
  symbolicSourceCompilerFrameLib

Theorem symbolic_frame_compile_bool_chain_ops:
  (!e. MEM e es ==> symbolic_frame R (lower_value f ce (BaseT BoolT) e)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!opc ops outs. symbolic_frame R (emit_inst opc ops outs)) /\
  (!l. symbolic_frame R (new_block l)) ==>
  symbolic_frame R (compile_bool_chain_ops f ce d r exit_lbl es)
Proof
  Induct_on `es`
  >- simp[compile_bool_chain_ops_def] >>
  qx_gen_tac `head` >> strip_tac >>
  `symbolic_frame R (lower_value f ce (BaseT BoolT) head)`
    by (first_x_assum irule >> simp[]) >>
  `symbolic_frame R (compile_bool_chain_ops f ce d r exit_lbl es)`
    by (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  Cases_on `es`
  >- (simp[compile_bool_chain_ops_def] >> frame_tac) >>
  Cases_on `d` >> simp[Once compile_bool_chain_ops_def] >> frame_tac
QED
