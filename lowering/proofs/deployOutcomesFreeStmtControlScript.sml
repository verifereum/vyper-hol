Theory deployOutcomesFreeStmtControl
Ancestors
  deployOutcomesFreeLowering stmtLowering compileEnv emitHelper venomInst
  loweringShapeDefs

Theorem outcomes_free_range_bound_checks:
  P SGT /\ P GT /\ P ISZERO /\ P ASSERT ==>
  !a b c n signed s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_range_bound_checks a b c n signed s)))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, comp_ignore_bind_def, comp_bind_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
       comp_return_def, emit_def, outcomes_free_state_insts, mk_inst_def]
QED

Theorem outcomes_free_declare_local:
  !cenv id ty s.
    EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (declare_local cenv id ty s)))
Proof
  rpt gen_tac >> simp[declare_local_def] >>
  Cases_on `cenv.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       outcomes_free_state_insts]
QED

Theorem outcomes_free_emit_local_alloca:
  P ALLOCA ==>
  !cenv id s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (emit_local_alloca cenv id s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[emit_local_alloca_def, outcomes_free_return] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[outcomes_free_return] >> rename1 `PtrVar op n` >> Cases_on `op` >>
  simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_declare_stmt_local:
  !cenv stmt s.
    EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (declare_stmt_local cenv stmt s)))
Proof
  rpt gen_tac >> Cases_on `stmt` >>
  simp[declare_stmt_local_def, outcomes_free_return, outcomes_free_declare_local]
QED

Theorem outcomes_free_return_unlock:
  (!key transient view s.
     EVERY P (state_insts s) ==>
     EVERY P (state_insts
       (SND (compile_nonreentrant_unlock key transient view s)))) ==>
  !cenv s. EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (compile_return_unlock cenv s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `cenv.ce_nonreentrant` >>
  rename1 `cenv.ce_nonreentrant = (nr, rest)` >>
  PairCases_on `rest` >>
  simp[compile_return_unlock_def] >>
  Cases_on `nr` >> simp[outcomes_free_return]
QED

Theorem outcomes_free_iter_elem_copy:
  P MSTORE /\ P MLOAD /\ P CALLDATACOPY /\
  (!a b n loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_slot_to_memory a b n loc s)))) /\
  (!ctor alloc loc ptr s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ptr_load ctor alloc loc ptr s)))) /\
  (!ctor alloc src dst n k s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_imm_copy_to_memory ctor alloc src dst n k s)))) /\
  (!dst src n s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_memory dst src n s)))) /\
  (!env src dst ty sty s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory env src dst ty sty s)))) ==>
  !env src dst n loc slots ty sty s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_iter_elem_copy env src dst n loc slots ty sty s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `slots` >> simp[compile_iter_elem_copy_def] >>
  Cases_on `loc` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_internal_return_from_env:
  P MLOAD /\
  (!env s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_return_unlock env s)))) /\
  (!env value rpc count ty sty elems buf s.
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_internal_return env value rpc count ty sty elems buf s)))) ==>
  !env ty sty value rpc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_internal_return_from_env env ty sty value rpc s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `env.ce_return_buf` >>
  simp[compile_internal_return_from_env_def] >-
   (rpt (FIRST [irule outcomes_free_ignore_bind >> conj_tac,
                irule outcomes_free_bind >> conj_tac,
                gen_tac, disch_tac]) >>
    simp[outcomes_free_return, comp_bind_def, comp_return_def]) >>
  rename1 `env.ce_return_buf = SOME loc` >> Cases_on `loc` >>
  simp[] >>
  rpt (FIRST [irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[outcomes_free_emit_ops, outcomes_free_return, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[outcomes_free_state_insts, mk_inst_def]
QED
