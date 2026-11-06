(* Checked reachability probes; not a counterexample to the body theorem. *)
Theory bodyMemTbConvertZeroProbe
Ancestors
  bodyMemTbConvertSourceMemory exprSimHypsDefs allocLimits
  vyperTypeSystem exprLowering

Theorem convert_zero_literal_static_pre:
  well_typed_expr env
    (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
      [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]) /\
  byte_widths_expr
    (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
      [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]) /\
  alloc_limits_expr cenv
    (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
      [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem convert_zero_payload_load_fails:
  s.vs_alloca_next = 32 ==>
  ~inst_mem_below_frontier (mk_inst id MLOAD [Lit 32w] outs) s
Proof
  simp[instMemFrontierTheory.below_frontier_MLOAD,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def]
QED

Theorem convert_zero_two_loads_mem_check:
  s.vs_alloca_next = 32 ==>
  ~run_inst_seq_mem_ok
    [mk_inst i MLOAD [Lit 0w] [x];
     mk_inst j ADD [Lit 0w; Lit 32w] [y];
     mk_inst k MLOAD [Var y] [z]] s
Proof
  strip_tac >>
  `step_inst_base (mk_inst i MLOAD [Lit 0w] [x]) s =
     OK (update_var x (mload 0 s) s)` by
    (simp[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
          venomStateTheory.eval_operand_def, venomStateTheory.eval_operands_def]) >>
  `step_inst_base (mk_inst j ADD [Lit 0w; Lit 32w] [y])
      (update_var x (mload 0 s) s) =
     OK (update_var y 32w (update_var x (mload 0 s) s))` by
    (simp[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
          wordsTheory.WORD_ADD_0,
          venomStateTheory.eval_operand_def, venomStateTheory.eval_operands_def]) >>
  asm_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
  simp[instMemFrontierTheory.below_frontier_MLOAD,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, wordsTheory.dimword_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
