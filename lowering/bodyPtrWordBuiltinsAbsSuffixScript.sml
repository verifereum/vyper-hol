(* Compiler boundary for the branchless, ASSERT-checked Abs suffix. *)
Theory bodyPtrWordBuiltinsAbsSuffix
Ancestors builtinSimple exprLowering exprLoweringProps compileEnv emitHelper
  venomInst list rich_list fragExec bodyPtrWordBuiltinsArithmeticSteps
  bodyPtrWordBuiltinsNegSuffix fragGasSeqPtr finite_map ptrDiscipline
  ptrSafeRun venomExecSemantics venomState venomExecProofs codegenRel contextCodegenRel
  bodyPtrWordBuiltinsScalar pred_set

Theorem word_abs_current_block:
  compile_builtin_abs x sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_abs_emitted_opcodes:
  compile_builtin_abs x sa = (op,sb) ==>
  MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
    [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem word_abs_code_prefix:
  compile_builtin_abs x sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule word_abs_current_block >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem word_abs_emitted_insts:
  compile_builtin_abs x sa = (op,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id SUB [Lit 0w; x]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) SLT [x; Lit 0w]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) EQ
       [x; Var (STRING #"%" (toString sa.cs_next_var))]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) AND
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] [];
     mk_inst (sa.cs_next_id + 6) XOR
       [Var (STRING #"%" (toString sa.cs_next_var)); x]
       [STRING #"%" (toString (sa.cs_next_var + 5))];
     mk_inst (sa.cs_next_id + 7) MUL
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 5)))]
       [STRING #"%" (toString (sa.cs_next_var + 6))];
     mk_inst (sa.cs_next_id + 8) XOR
       [x; Var (STRING #"%" (toString (sa.cs_next_var + 6)))]
       [STRING #"%" (toString (sa.cs_next_var + 7))]] /\
  op = Var (STRING #"%" (toString (sa.cs_next_var + 7)))
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_abs_scalar_inst_ok:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  (!arg. MEM arg inst.inst_operands ==>
    op_taint tn arg = {} /\ op_prov G arg = NONE) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s
Proof
  strip_tac >>
  `!arg. MEM arg inst.inst_operands ==> op_taint tn arg = {}` by metis_tac[] >>
  `!u v. inst.inst_operands = [Var u; Var v] ==>
     u NOTIN FDOM G /\ v NOTIN FDOM G` by
    (rpt strip_tac >>
     qpat_assum `!arg. _ ==> _ /\ _` (qspec_then `Var u` mp_tac) >>
     qpat_assum `!arg. _ ==> _ /\ _` (qspec_then `Var v` mp_tac) >>
     gvs[op_prov_def, FLOOKUP_DEF]) >>
  gvs[MEM, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_abs_out_taint:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] ==>
  out_taint tn inst s = {}
Proof
  simp[MEM] >> strip_tac >>
  (namedCases_on `inst.inst_operands` ["", "a rest"]
  >- simp[out_taint_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  Cases_on `tail` >> simp[out_taint_def])
QED

Theorem word_abs_scalar_transfer:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  (!x. x IN scalars ==> FLOOKUP G x = NONE /\
                            op_taint tn (Var x) = {}) /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN scalars) ==>
  !x. x IN scalars UNION set inst.inst_outputs ==>
    FLOOKUP (step_prov PG G inst t) x = NONE /\
    op_taint (step_taint inst s t tn) (Var x) = {}
Proof
  strip_tac >>
  `!x. x IN scalars UNION set inst.inst_outputs ==>
       FLOOKUP (step_prov PG G inst t) x = NONE` by
    (rpt strip_tac >> irule step_prov_scalar_set >> gvs[MEM] >>
     qexists_tac `scalars` >> simp[] >> metis_tac[]) >>
  drule word_abs_out_taint >> strip_tac >>
  rpt strip_tac >- metis_tac[] >>
  namedCases_on `inst.inst_outputs` ["", "out rest"]
  >- (gvs[step_taint_def, op_taint_def, set_var_taint_def,
          FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  namedCases_on `rest` ["", "out2 tail"]
  >- (Cases_on `out = x` >>
      gvs[step_taint_def, op_taint_def, set_var_taint_def,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  gvs[step_taint_def, op_taint_def, set_var_taint_def,
      FLOOKUP_DRESTRICT] >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED
