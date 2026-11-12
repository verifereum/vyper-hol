(* Joint Neg simulation: its checked arithmetic suffix. *)
Theory bodyFullBuiltinWordNeg
Ancestors
  bodyFullGhostFrame bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullStmts fragGasSeqPtr fragGasEmitCtrl
  exprSimWordBuiltins exprSimUnopProps exprSimSource
  ptrSafeRun ptrDiscipline exprLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomInst venomState
  list rich_list finite_map

Theorem word_neg_emission:
  !x ty sa op sb.
    compile_neg x ty sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) ASSERT
         [Var (STRING #"%" (toString sa.cs_next_var))] [];
       mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
         [STRING #"%" (toString (sa.cs_next_var+1))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+1)))
Proof
  rpt gen_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, LET_THM, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
    fresh_var_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
    arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED
