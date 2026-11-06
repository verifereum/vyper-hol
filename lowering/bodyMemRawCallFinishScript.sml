(* Memory checks for raw_call result handling. *)
Theory bodyMemRawCallFinish
Ancestors
  bodyMemRawCallBounds rawCallResultFrame exprSimRawCall builtinSimple emitHelper context
  exprLoweringProps fragExecMem instMemFrontier memSafeRun compileEnv
  venomState venomExecSemantics venomInst finite_map rich_list list
Libs
  monadsyntax

Theorem raw_call_success_mem_ok:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  w2n addr + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
  `code = TAKE 5 code ++ DROP 5 code` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  irule run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (irule raw_call_result_prefix_mem_ok >> simp[Abbr `code`, mk_inst_def]) >>
  rpt strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL] /\
      (!v. ov = Var v ==> ~MEM v i.inst_outputs)) (TAKE 5 code)` by
    (simp[Abbr `code`, mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[not_fresh_at_def] >>
     metis_tac[ASCIInumbersTheory.toString_inj, arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all raw_call_result_prefix_operand >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL])
     (TAKE 5 code)` by fs[EVERY_MEM] >>
  drule_all raw_call_result_prefix_frontier >> strip_tac >>
  simp[Abbr `code`, run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  rpt strip_tac >> gvs[]
QED
