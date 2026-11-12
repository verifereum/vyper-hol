(* Backward progress for kept instructions other than PARAM. *)
Theory fmpStageCoverBackKeptOps
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  passSimulationDefs venomExecSemantics venomState venomInst venomWf
  unitShapeDefs stackPlanTypes finite_map words list

Theorem kept_operand_defined[local]:
  (!v. MEM (Var v) ops ==> IS_SOME (lookup_var v s)) /\
  s.vs_labels = t.vs_labels ==>
  !op. MEM op ops /\ IS_SOME (eval_operand op t) ==>
       IS_SOME (eval_operand op s)
Proof
  strip_tac >> Cases >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem kept_pure1[local]:
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ terminates (exec_pure1 f inst t) ==>
  terminates (exec_pure1 g inst s)
Proof
  strip_tac >> Cases_on `exec_pure1 f inst t` >>
  gvs[terminates_def, exec_pure1_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a]` >>
  Cases_on `eval_operand a s` >> gvs[]
QED

Theorem kept_pure2[local]:
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ terminates (exec_pure2 f inst t) ==>
  terminates (exec_pure2 g inst s)
Proof
  strip_tac >> Cases_on `exec_pure2 f inst t` >>
  gvs[terminates_def, exec_pure2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a;b]` >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand b s` >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem kept_pure3[local]:
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ terminates (exec_pure3 f inst t) ==>
  terminates (exec_pure3 g inst s)
Proof
  strip_tac >> Cases_on `exec_pure3 f inst t` >>
  gvs[terminates_def, exec_pure3_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a;b;c]` >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand b s` >> gvs[] >>
  Cases_on `eval_operand c s` >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem kept_read1[local]:
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ terminates (exec_read1 f inst t) ==>
  terminates (exec_read1 g inst s)
Proof
  strip_tac >> Cases_on `exec_read1 f inst t` >>
  gvs[terminates_def, exec_read1_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a]` >>
  Cases_on `eval_operand a s` >> gvs[]
QED

Theorem kept_write2[local]:
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ terminates (exec_write2 f inst t) ==>
  terminates (exec_write2 g inst s)
Proof
  strip_tac >> Cases_on `exec_write2 f inst t` >>
  gvs[terminates_def, exec_write2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a;b]` >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand b s` >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem kept_read0[local]:
  terminates (exec_read0 f inst t) ==> terminates (exec_read0 g inst s)
Proof
  Cases_on `exec_read0 f inst t` >>
  gvs[terminates_def, exec_read0_def, AllCaseEqs()]
QED

Theorem kept_gas[local]:
  terminates (exec_gas inst t) ==> terminates (exec_gas inst s)
Proof
  Cases_on `exec_gas inst t` >>
  gvs[terminates_def, exec_gas_def, AllCaseEqs()] >>
  Cases_on `s.vs_gas_readings` >> simp[terminates_def]
QED

Theorem kept_operands[local]:
  (!op. MEM op ops /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\ IS_SOME (eval_operands ops t) ==>
  IS_SOME (eval_operands ops s)
Proof
  simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]
QED

Theorem kept_write2_defined[local]:
  LENGTH inst.inst_operands = 2 /\ IS_SOME (eval_operands inst.inst_operands s) ==>
  terminates (exec_write2 f inst s)
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[eval_operands_IS_SOME_EVERY] >>
  rename1 `inst.inst_operands = [a;b]` >>
  Cases_on `eval_operand a s` >> gvs[exec_write2_def, terminates_def] >>
  Cases_on `eval_operand b s` >> gvs[exec_write2_def, terminates_def]
QED

Theorem kept_base_terminates[local]:
  inst_wf inst /\ inst_shape_ok inst /\ pre_fmp_opcode inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM] /\
  (!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op t) ==>
        IS_SOME (eval_operand op s)) /\
  terminates (step_inst k' C' inst t) ==>
  terminates (step_inst k C inst s)
Proof
  strip_tac >> Cases_on `inst.inst_opcode`
  >~ [`inst.inst_opcode = ADD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SUB`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = MUL`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = Div`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = Mod`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SDIV`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SMOD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = Exp`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = ADDMOD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure3])
  >~ [`inst.inst_opcode = MULMOD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure3])
  >~ [`inst.inst_opcode = EQ`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = LT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = GT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SLT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SGT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = ISZERO`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure1])
  >~ [`inst.inst_opcode = AND`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = OR`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = XOR`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = NOT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure1])
  >~ [`inst.inst_opcode = SHL`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SHR`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SAR`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = SIGNEXTEND`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = BYTE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_pure2])
  >~ [`inst.inst_opcode = MLOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = MSTORE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_write2])
  >~ [`inst.inst_opcode = MSTORE8`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_write2])
  >~ [`inst.inst_opcode = SLOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = TLOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = CALLER`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = ADDRESS`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = CALLVALUE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = GAS`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_gas])
  >~ [`inst.inst_opcode = ORIGIN`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = GASPRICE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = CHAINID`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = COINBASE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = TIMESTAMP`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = NUMBER`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = PREVRANDAO`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = GASLIMIT`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = BASEFEE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = BLOBBASEFEE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = BLOCKHASH`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = BLOBHASH`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = BALANCE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = SELFBALANCE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = CALLDATASIZE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = CALLDATALOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = RETURNDATASIZE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = MEMTOP`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = CODESIZE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read0])
  >~ [`inst.inst_opcode = EXTCODESIZE`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = EXTCODEHASH`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = ILOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = DLOAD`] >-
    (fs[step_inst_non_invoke, step_inst_base_def] >> metis_tac[kept_read1])
  >~ [`inst.inst_opcode = INVOKE`] >- gvs[]
  >~ [`inst.inst_opcode = DALLOCA`] >- gvs[]
  >~ [`inst.inst_opcode = RETPC_PARAM`] >- gvs[]
  >~ [`inst.inst_opcode = PHI`] >- gvs[]
  >~ [`inst.inst_opcode = PARAM`] >- gvs[]
  >~ [`inst.inst_opcode = DRET`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = GETFMP`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = SETFMP`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = RETFMP`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = INITIAL_FMP`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = BUMP`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = FMP_PARAM`] >- gvs[pre_fmp_opcode_def]
  >~ [`inst.inst_opcode = DELEGATECALL`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, exec_delegatecall_def,
         AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c;d;e;f]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_assum (qspec_then `c` assume_tac) >>
     first_assum (qspec_then `d` assume_tac) >>
     first_assum (qspec_then `e` assume_tac) >>
     first_x_assum (qspec_then `f` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >>
     Cases_on `eval_operand d s` >> gvs[] >>
     Cases_on `eval_operand e s` >> gvs[] >>
     Cases_on `eval_operand f s` >> gvs[] >>
     fs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[] >>
     simp[exec_delegatecall_def] >> pairarg_tac >> simp[])
  >~ [`inst.inst_opcode = CREATE`] >-
    (`LENGTH inst.inst_operands = 3` by gvs[inst_wf_def] >>
     gvs[LENGTH_EQ_NUM_compute] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     `IS_SOME (eval_operand a t) /\
      IS_SOME (eval_operand b t) /\
      IS_SOME (eval_operand c t)` by
       (CCONTR_TAC >> qpat_x_assum `terminates _` mp_tac >>
        Cases_on `eval_operand a t` >>
        Cases_on `eval_operand b t` >>
        Cases_on `eval_operand c t` >>
        gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
            eval_operands_def, terminates_def]) >>
     `?v0 v1 v2.
        eval_operand a s = SOME v0 /\
        eval_operand b s = SOME v1 /\
        eval_operand c s = SOME v2` by
       (gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
         eval_operands_def, terminates_def, exec_create_def] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]))
  >~ [`inst.inst_opcode = CREATE2`] >-
    (`LENGTH inst.inst_operands = 4` by gvs[inst_wf_def] >>
     gvs[LENGTH_EQ_NUM_compute] >>
     rename1 `inst.inst_operands = [a;b;c;d]` >>
     `IS_SOME (eval_operand a t) /\
      IS_SOME (eval_operand b t) /\
      IS_SOME (eval_operand c t) /\
      IS_SOME (eval_operand d t)` by
       (CCONTR_TAC >> qpat_x_assum `terminates _` mp_tac >>
        Cases_on `eval_operand a t` >>
        Cases_on `eval_operand b t` >>
        Cases_on `eval_operand c t` >>
        Cases_on `eval_operand d t` >>
        gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
            eval_operands_def, terminates_def]) >>
     `?v0 v1 v2 v3.
        eval_operand a s = SOME v0 /\
        eval_operand b s = SOME v1 /\
        eval_operand c s = SOME v2 /\
        eval_operand d s = SOME v3` by
       (gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
         eval_operands_def, terminates_def, exec_create_def] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]))
  >~ [`inst.inst_opcode = SELFDESTRUCT`] >-
    (`LENGTH inst.inst_operands = 1` by gvs[inst_wf_def] >>
     gvs[LENGTH_EQ_NUM_compute] >>
     rename1 `inst.inst_operands = [a]` >>
     `IS_SOME (eval_operand a t)` by
       (CCONTR_TAC >> qpat_x_assum `terminates _` mp_tac >>
        Cases_on `eval_operand a t` >>
        gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
            eval_operands_def, terminates_def]) >>
     `?v0.
        eval_operand a s = SOME v0` by
       (gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
         eval_operands_def, terminates_def] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]))
  >~ [`inst.inst_opcode = DJMP`] >- gvs[inst_shape_ok_def]
  >~ [`inst.inst_opcode = OFFSET`] >- gvs[inst_shape_ok_def]
  >~ [`inst.inst_opcode = NOP`] >-
    simp[step_inst_non_invoke, step_inst_base_def, terminates_def]
  >~ [`inst.inst_opcode = STOP`] >-
    simp[step_inst_non_invoke, step_inst_base_def, terminates_def]
  >~ [`inst.inst_opcode = SINK`] >-
    simp[step_inst_non_invoke, step_inst_base_def, terminates_def]
  >~ [`inst.inst_opcode = INVALID`] >-
    simp[step_inst_non_invoke, step_inst_base_def, terminates_def]
  >~ [`inst.inst_opcode = MCOPY`] >-
    (fs[step_inst_non_invoke] >>
     Cases_on `step_inst_base inst t` >> gvs[terminates_def] >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     `IS_SOME (eval_operand a s) /\ IS_SOME (eval_operand b s) /\
      IS_SOME (eval_operand c s)` by metis_tac[MEM, optionTheory.IS_SOME_DEF] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF])
  >~ [`inst.inst_opcode = SSTORE`] >-
    (fs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     Cases_on `s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)` >>
     simp[terminates_def] >>
     Cases_on `t.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands t)`
     >- (rewrite_tac[GSYM terminates_def] >> irule kept_write2_defined >>
         fs[inst_wf_def, eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
     gvs[] >> rewrite_tac[GSYM terminates_def] >> metis_tac[kept_write2])
  >~ [`inst.inst_opcode = TSTORE`] >-
    (fs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     Cases_on `s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)` >>
     simp[terminates_def] >>
     Cases_on `t.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands t)`
     >- (rewrite_tac[GSYM terminates_def] >> irule kept_write2_defined >>
         fs[inst_wf_def, eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
     gvs[] >> rewrite_tac[GSYM terminates_def] >> metis_tac[kept_write2])
  >~ [`inst.inst_opcode = ISTORE`] >-
    (fs[step_inst_non_invoke] >>
     Cases_on `step_inst_base inst t` >> gvs[terminates_def] >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b]` >>
     `IS_SOME (eval_operand a s) /\ IS_SOME (eval_operand b s)` by
       metis_tac[MEM, optionTheory.IS_SOME_DEF] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF])
  >~ [`inst.inst_opcode = JMP`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()])
  >~ [`inst.inst_opcode = JNZ`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;Label l;Label r]` >>
     first_x_assum (qspec_then `a` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >> IF_CASES_TAC >> simp[])
  >~ [`inst.inst_opcode = ASSERT`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a]` >>
     Cases_on `eval_operand a s` >> gvs[] >> IF_CASES_TAC >> simp[])
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a]` >>
     Cases_on `eval_operand a s` >> gvs[] >> IF_CASES_TAC >> simp[])
  >~ [`inst.inst_opcode = ASSIGN`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a]` >>
     Cases_on `eval_operand a s` >> gvs[])
  >~ [`inst.inst_opcode = RET`] >-
    (fs[step_inst_non_invoke] >>
     `IS_SOME (eval_operands inst.inst_operands t)` by
       (Cases_on `eval_operands inst.inst_operands t` >>
        gvs[step_inst_base_opcode_eqs, terminates_def]) >>
     `IS_SOME (eval_operands inst.inst_operands s)` by
       (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
     Cases_on `inst.inst_operands` >-
       gvs[step_inst_base_opcode_eqs, eval_operands_def, terminates_def] >>
     rename1 `inst.inst_operands = h::rest` >>
     Cases_on `eval_operand h s` >> gvs[eval_operands_def] >>
     Cases_on `eval_operands rest s` >>
     gvs[step_inst_base_opcode_eqs, eval_operands_def, terminates_def])
  >~ [`inst.inst_opcode = RETURN`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_x_assum (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[])
  >~ [`inst.inst_opcode = REVERT`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_x_assum (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[])
  >~ [`inst.inst_opcode = ALLOCA`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[] >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME p` >> Cases_on `p` >> simp[])
  >~ [`inst.inst_opcode = CALLDATACOPY`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_x_assum (qspec_then `c` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[])
  >~ [`inst.inst_opcode = DLOADBYTES`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_x_assum (qspec_then `c` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[])
  >~ [`inst.inst_opcode = CODECOPY`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_x_assum (qspec_then `c` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[])
  >~ [`inst.inst_opcode = EXTCODECOPY`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c;d]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_assum (qspec_then `c` assume_tac) >>
     first_x_assum (qspec_then `d` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >>
     Cases_on `eval_operand d s` >> gvs[])
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_x_assum (qspec_then `c` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >> IF_CASES_TAC >> simp[])
  >~ [`inst.inst_opcode = SHA3`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_x_assum (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[])
  >~ [`inst.inst_opcode = CALL`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, exec_ext_call_def, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c;d;e;f;g]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_assum (qspec_then `c` assume_tac) >>
     first_assum (qspec_then `d` assume_tac) >>
     first_assum (qspec_then `e` assume_tac) >>
     first_assum (qspec_then `f` assume_tac) >>
     first_x_assum (qspec_then `g` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >>
     Cases_on `eval_operand d s` >> gvs[] >>
     Cases_on `eval_operand e s` >> gvs[] >>
     Cases_on `eval_operand f s` >> gvs[] >>
     Cases_on `eval_operand g s` >> gvs[] >>
     IF_CASES_TAC >> simp[] >>
     fs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[] >>
     simp[exec_ext_call_def] >> pairarg_tac >> simp[])
  >~ [`inst.inst_opcode = STATICCALL`] >-
    (fs[step_inst_non_invoke] >> Cases_on `step_inst_base inst t` >>
     gvs[terminates_def, step_inst_base_opcode_eqs, exec_ext_call_def, AllCaseEqs()] >>
     rename1 `inst.inst_operands = [a;b;c;d;e;f]` >>
     first_assum (qspec_then `a` assume_tac) >>
     first_assum (qspec_then `b` assume_tac) >>
     first_assum (qspec_then `c` assume_tac) >>
     first_assum (qspec_then `d` assume_tac) >>
     first_assum (qspec_then `e` assume_tac) >>
     first_x_assum (qspec_then `f` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operand c s` >> gvs[] >>
     Cases_on `eval_operand d s` >> gvs[] >>
     Cases_on `eval_operand e s` >> gvs[] >>
     Cases_on `eval_operand f s` >> gvs[] >>
     fs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[] >>
     simp[exec_ext_call_def] >> pairarg_tac >> simp[])
  >~ [`inst.inst_opcode = LOG`] >-
    (fs[step_inst_non_invoke, inst_wf_def] >>
     rename1 `inst.inst_operands = Lit tc :: rest` >>
     `?a b ops. REVERSE rest = a::b::ops` by
       (`LENGTH (REVERSE rest) = w2n tc + 2` by simp[] >>
        Cases_on `REVERSE rest` >> fs[] >>
        rename1 `REVERSE rest = a::tail` >> Cases_on `tail` >> fs[]) >>
     `rest = REVERSE (a::b::ops)` by metis_tac[REVERSE_REVERSE] >>
     gvs[] >>
     `IS_SOME (eval_operand a t) /\ IS_SOME (eval_operand b t) /\
      IS_SOME (eval_operands ops t)` by
       (Cases_on `step_inst_base inst t` >>
        gvs[step_inst_base_opcode_eqs, terminates_def, AllCaseEqs(),
            eval_operands_IS_SOME_EVERY, EVERY_MEM, REVERSE_APPEND, REVERSE_REVERSE] >>
        `IS_SOME (eval_operands ops t)` by simp[] >>
        fs[eval_operands_IS_SOME_EVERY, EVERY_MEM]) >>
     `IS_SOME (eval_operand a s) /\ IS_SOME (eval_operand b s) /\
      IS_SOME (eval_operands ops s)` by
       (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand b s` >> gvs[] >>
     Cases_on `eval_operands ops s` >> gvs[] >>
     simp[step_inst_base_opcode_eqs, REVERSE_APPEND, REVERSE_REVERSE] >>
     IF_CASES_TAC >> simp[terminates_def] >>
     first_assum (qspec_then `b` mp_tac) >> simp[])
QED

Theorem fmp_stage_back_kept_nonparam:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  terminates (step_inst k' C' inst t) /\ inst.inst_opcode <> PARAM /\
  (!v. MEM (Var v) inst.inst_operands ==> IS_SOME (lookup_var v s)) ==>
  terminates (step_inst k C inst s)
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `inst_wf inst /\ inst_shape_ok inst /\ pre_fmp_opcode inst.inst_opcode` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_shape_ok_def,
        pre_fmp_ops_def, EVERY_MEM] >> metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff]) >>
  irule kept_base_terminates >> simp[] >>
  reverse conj_tac >- gvs[] >>
  qexistsl_tac [`C'`, `k'`, `t`] >> simp[] >>
  ho_match_mp_tac kept_operand_defined >> simp[] >>
  fs[fmp_stage_rel_def, fmp_frame_rel_def]
QED
