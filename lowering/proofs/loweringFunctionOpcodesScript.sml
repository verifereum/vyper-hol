Theory loweringFunctionOpcodes
Ancestors
  moduleLowering compileEnv context emitHelper loweringShapeDefs venomInst
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABIDecode list pair

Theorem outcomes_free_nonreentrant:
  ((!opc. MEM opc [TLOAD; SLOAD; TSTORE; SSTORE; EQ; ISZERO; ASSERT] ==> P opc) /\
   EVERY (\i. P i.inst_opcode) (state_insts s) ==>
   EVERY (\i. P i.inst_opcode)
     (state_insts (SND (compile_nonreentrant_lock key trans view s)))) /\
  (P TSTORE /\ P SSTORE /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
   EVERY (\i. P i.inst_opcode)
     (state_insts (SND (compile_nonreentrant_unlock key trans view s))))
Proof
  rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_fixed_region:
  P ASSIGN ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  strip_tac >>
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    state_insts_def, all_blocks_def, mk_inst_def]
QED

Theorem outcomes_free_constructor_epilogue:
  P ALLOCA /\ P ADD /\ P MCOPY /\ P CODECOPY /\ P RETURN ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_constructor_epilogue sz cap imm st)))
Proof
  strip_tac >> simp[compile_constructor_epilogue_def] >>
  rpt (FIRST [IF_CASES_TAC,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, outcomes_free_alloc_buffer,
      every_state_insts_return])])
QED

Theorem opcode_every_fixed_region:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_fixed_region_with_id sz st)))
Proof
  strip_tac >> match_mp_tac outcomes_free_fixed_region >> simp[]
QED

Theorem opcode_every_nonreentrant_lock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_lock key trans view st)))
Proof
  rpt strip_tac >> irule (cj 1 outcomes_free_nonreentrant) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_abi_arg_ptr_guard:
  P LT /\ P ISZERO /\ P ASSERT /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_arg_ptr_guard opc src parent st)))
Proof
  strip_tac >> simp[compile_abi_arg_ptr_guard_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void]),
    gen_tac, strip_tac, irule every_state_insts_bind])
QED

Theorem opcode_every_abi_arg_ptr_guard:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_arg_ptr_guard opc src parent st)))
Proof
  rpt strip_tac >> irule outcomes_free_abi_arg_ptr_guard >> simp[]
QED

Theorem outcomes_free_decode_args:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; ALLOCA; JMP; JNZ] ==> P opc) ==>
  !args ce off opc hi base.
  P opc /\ (opc = CALLDATALOAD ==> P CALLDATACOPY) /\
  (opc = DLOAD ==> P DLOADBYTES) ==> !st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_decode_args ce args off opc hi base st)))
Proof
  strip_tac >> mp_tac outcomes_free_abi_decode >>
  impl_tac >- simp[DISJ_IMP_THM] >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Induct >> simp[compile_decode_args_def, every_state_insts_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >> strip_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      outcomes_free_abi_clamp, every_state_insts_return])]) >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[every_state_insts_return, opcode_every_emit_void] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op,
      outcomes_free_abi_arg_ptr_guard, every_state_insts_return])])
QED

Theorem opcode_every_decode_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !args ce off opc hi base. P opc ==> !st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_decode_args ce args off opc hi base st)))
Proof
  strip_tac >> mp_tac outcomes_free_decode_args >>
  impl_tac >- simp[DISJ_IMP_THM] >> simp[]
QED

Theorem outcomes_free_register_constructor_args:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; ALLOCA; JMP; JNZ] ==> P opc) /\
  P DLOAD /\ P DLOADBYTES ==>
  !args ce off sz st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_register_constructor_args ce args off sz st)))
Proof
  strip_tac >> drule outcomes_free_decode_args >> strip_tac >>
  `P ALLOCA` by fs[] >>
  Induct >- simp[compile_register_constructor_args_def, every_state_insts_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `compile_register_constructor_args _ ((nm,_)::_)` >>
  Cases_on `FLOOKUP ce.ce_vars nm` >>
  simp[compile_register_constructor_args_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (gvs[outcomes_free_alloc_buffer, every_state_insts_return]),
    irule every_state_insts_bind, irule every_state_insts_ignore_bind, conj_tac,
    IF_CASES_TAC,
    (qmatch_goalsub_rename_tac `var_location_memory_size loc` >>
      Cases_on `var_location_memory_size loc`)]) >>
  qpat_x_assum `!ce off sz st. _` irule >> simp[]
QED

Theorem register_constructor_args_defaults[local]:
  !args cenv off sz st.
    (FST (compile_register_constructor_args cenv args off sz st)).ce_func_defaults =
    cenv.ce_func_defaults
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once compile_register_constructor_args_def] >>
  qmatch_goalsub_rename_tac `var_location_memory_size loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem every_state_insts_constructor_args_bind[local]:
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts
      (SND (compile_register_constructor_args ce args off sz st)))) /\
  (!env. env.ce_func_defaults = ce.ce_func_defaults ==>
    !st. EVERY P (state_insts st) ==> EVERY P (state_insts (SND (f env st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts
      (SND (comp_bind (compile_register_constructor_args ce args off sz) f st)))
Proof
  rpt strip_tac >>
  qspecl_then [`args`, `ce`, `off`, `sz`, `st`] mp_tac
    register_constructor_args_defaults >>
  Cases_on `compile_register_constructor_args ce args off sz st` >>
  gvs[comp_bind_def] >> metis_tac[pairTheory.SND]
QED

Theorem constructor_prefix_opcode_every:
  (!opc. MEM opc [CALLVALUE; ASSIGN; TLOAD; SLOAD; TSTORE; SSTORE; CODECOPY;
     RETURN; DLOAD; ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; DLOADBYTES; ALLOCA; JMP; JNZ]
     ==> P opc) /\
  (!ce st. ce.ce_func_defaults = cenv.ce_func_defaults /\
     EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_stmts ce NoLoop NoneT fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) args 0 sz;
          (if nr then compile_nonreentrant_lock key trans view else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans view else return ());
          compile_constructor_epilogue runtime_size cap imm od st)))
Proof
  strip_tac >>
  `!args ce off sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_register_constructor_args ce args off sz st)))` by
    (rpt strip_tac >> irule outcomes_free_register_constructor_args >>
     fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
  `!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_nonreentrant_lock key trans view st))) /\
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_nonreentrant_unlock key trans view st)))` by
    (gen_tac >> strip_tac >> conj_tac >|
       [irule (cj 1 outcomes_free_nonreentrant),
        irule (cj 2 outcomes_free_nonreentrant)] >>
     fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (FIRST [IF_CASES_TAC,
    (ho_match_mp_tac every_state_insts_constructor_args_bind >> conj_tac
      >- simp[] >> gen_tac >> disch_tac),
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (fs[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return, every_state_insts_get,
      every_state_insts_new_block, every_state_insts_fresh_label,
      outcomes_free_fixed_region, outcomes_free_constructor_epilogue])]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_constructor_prefix:
  (!opc. MEM opc [CALLVALUE; ASSIGN; TLOAD; SLOAD; TSTORE; SSTORE; CODECOPY;
     RETURN; DLOAD; ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; DLOADBYTES; ALLOCA; JMP; JNZ]
     ==> P opc) /\
  (!ce st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_stmts ce NoLoop NoneT fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE)) args 0 sz;
          (if nr then compile_nonreentrant_lock key trans view else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT fbody;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans view else return ());
          compile_constructor_epilogue runtime_size cap imm od st)))
Proof
  rpt strip_tac >> irule constructor_prefix_opcode_every >> simp[]
QED
