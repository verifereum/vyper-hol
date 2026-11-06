(* Concrete six-instruction decimal rounding sequences. *)
Theory bodyPtrWordBuiltinsRounding
Ancestors bodyPtrWordBuiltinsRoundingSteps bodyPtrWordBuiltinsAbsPost
  bodyPtrWordBuiltinsAbsSequence bodyPtrWordBuiltinsAbsSuffix
  bodyPtrWordBuiltinsScalarSequence bodyPtrWordBuiltinsIntervalGhost
  builtinMisc builtinSimple exprSimWordBuiltins exprLoweringProps compileEnv
  emitHelper venomInst list rich_list pred_set bodyPtrDefs ptrDiscipline ptrSafeRun
  finite_map codegenRel fragGasSeqPtr venomState

Theorem word_round_emitted_insts:
  (if up then compile_ceil else compile_floor) v d sa = (op,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id SLT [v; Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) (if up then ADD else SUB) [v; Lit (n2w (d-1))]
      [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) XOR
      [(if up then v else Var (STRING #"%" (toString (sa.cs_next_var + 1))));
       (if up then Var (STRING #"%" (toString (sa.cs_next_var + 1))) else v)]
      [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) MUL
      [Var (STRING #"%" (toString sa.cs_next_var));
       Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
      [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) XOR
      [(if up then Var (STRING #"%" (toString (sa.cs_next_var + 1))) else v);
       Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
      [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) SDIV
      [Var (STRING #"%" (toString (sa.cs_next_var + 4))); Lit (n2w d)]
      [STRING #"%" (toString (sa.cs_next_var + 5))]] /\
  op = Var (STRING #"%" (toString (sa.cs_next_var + 5)))
Proof
  Cases_on `up` >>
  simp[compile_ceil_def, compile_floor_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_round_emitted_shape:
  (if up then compile_ceil else compile_floor) v d sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 6 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. MEM i.inst_opcode [SUB; SLT; XOR; MUL; ADD; SDIV] /\
    ?x. i.inst_outputs = [x]) (emitted_insts sa sb)
Proof
  strip_tac >> drule word_round_emitted_insts >> strip_tac >>
  Cases_on `up` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem word_round_emitted_dependency:
  (if up then compile_ceil else compile_floor) v d sa = (op,sb) ==>
  !pre i post x. emitted_insts sa sb = pre ++ i::post /\
    MEM (Var x) i.inst_operands ==>
    x IN {z | v = Var z} UNION set (FLAT (MAP (\j. j.inst_outputs) pre))
Proof
  strip_tac >> drule word_round_emitted_insts >> strip_tac >>
  Cases_on `up` >> rpt gen_tac >> strip_tac >> gvs[] >>
  ntac 7
    (qmatch_asmsub_rename_tac `pre ++ [i] ++ post` >>
     Cases_on `pre` >> gvs[mk_inst_def])
QED

Theorem word_round_outputs_fresh:
  (if up then compile_ceil else compile_floor) v d sa = (op,sb) /\
  sc.cs_next_var <= sa.cs_next_var ==>
  !i x p. MEM i (emitted_insts sa sb) /\ MEM x i.inst_outputs /\
    not_fresh_at sc p ==> p <> x
Proof
  strip_tac >> drule word_round_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[MEM, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

