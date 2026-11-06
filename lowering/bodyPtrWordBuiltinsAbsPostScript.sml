(* Concrete dependency facts and the invariant-carrying Abs suffix. *)
Theory bodyPtrWordBuiltinsAbsPost
Ancestors bodyPtrWordBuiltinsAbsSequence bodyPtrWordBuiltinsAbsSuffix
  bodyPtrWordBuiltinsScalarSequence bodyPtrWordBuiltinsIntervalGhost
  exprLoweringProps builtinSimple compileEnv venomInst list pred_set
  bodyPtrDefs ptrDiscipline ptrSafeRun finite_map codegenRel

Theorem word_abs_emitted_shape:
  compile_builtin_abs v sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 9 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. MEM i.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
    (i.inst_opcode = ASSERT ==> ?v. i.inst_operands = [v] /\ i.inst_outputs = []) /\
    (i.inst_opcode <> ASSERT ==> ?x. i.inst_outputs = [x])) (emitted_insts sa sb)
Proof
  strip_tac >> drule word_abs_emitted_insts >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem word_abs_emitted_dependency:
  compile_builtin_abs v sa = (op,sb) ==>
  !pre i post x. emitted_insts sa sb = pre ++ i::post /\
    MEM (Var x) i.inst_operands ==>
    x IN {z | v = Var z} UNION set (FLAT (MAP (\j. j.inst_outputs) pre))
Proof
  strip_tac >> drule word_abs_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  ntac 10
    (qmatch_asmsub_rename_tac `pre ++ [i] ++ post` >>
     Cases_on `pre` >> gvs[mk_inst_def])
QED
