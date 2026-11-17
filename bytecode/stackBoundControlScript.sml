(* Exact stack and control-flow refinement for the operand-stack checker. *)
Theory stackBoundControl
Ancestors
  stackBoundInterface stackBoundDefs vfmExecution vfmExecutionProp
  vfmContext vfmOperation vfmState vfmConstants
  list rich_list pair option finite_map words byte

Theorem sb_jump_target:
  (case a of NONE => T | SOME n => n = w2n w) /\
  FLOOKUP (parse_code 0 FEMPTY code) (w2n w) = SOME JumpDest ==>
  MEM (w2n w)
    (bytecode_jump_targets (parse_code 0 FEMPTY code)
      (FILTER (\pc. FLOOKUP (parse_code 0 FEMPTY code) pc = SOME JumpDest)
        (GENLIST I (LENGTH code))) a)
Proof
  strip_tac >>
  `w2n w < LENGTH code` by
    (drule FLOOKUP_parse_code_SOME_less_LENGTH >> simp[]) >>
  Cases_on `a` >> gvs[bytecode_jump_targets_def, MEM_FILTER, MEM_GENLIST]
QED

Theorem sb_push_contract[local]:
  sb_opcode_contract (Push n ws)
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  simp[sb_successors_def, bytecode_stack_successors_def] >>
  conj_tac
  >- (strip_tac >>
      drule bytecode_stack_describes_length >> strip_tac >>
      simp[step_inst_def, step_push_def, consume_gas_def, push_stack_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, step_push_def, consume_gas_def,
       push_stack_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def,
              bytecode_stack_describes_def, word_of_bytes_le_def]
QED

Theorem sb_dup_contract[local]:
  sb_opcode_contract (Dup n)
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  drule bytecode_stack_describes_length >> strip_tac >>
  simp[sb_successors_def, bytecode_stack_successors_def] >>
  Cases_on `n < LENGTH a` >> gvs[]
  >- (conj_tac
      >- (strip_tac >>
          simp[step_inst_def, step_dup_def, consume_gas_def, push_stack_def,
               bind_def, ignore_bind_def, get_current_context_def,
               set_current_context_def, assert_def, return_def, fail_def] >>
          rw[] >> gvs[return_def, fail_def]) >>
      simp[sb_inner_def, step_inst_def, step_dup_def, consume_gas_def,
           push_stack_def, inc_pc_or_jump_def, is_call_def, bind_def,
           ignore_bind_def, get_current_context_def, set_current_context_def,
           assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def, sb_at_def] >>
      irule bytecode_stack_describes_dup >> simp[]) >>
  simp[sb_inner_def, step_inst_def, step_dup_def, consume_gas_def,
       push_stack_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def]
QED

Theorem sb_swap_contract[local]:
  sb_opcode_contract (Swap n)
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  drule bytecode_stack_describes_length >> strip_tac >>
  simp[sb_successors_def, bytecode_stack_successors_def] >>
  conj_tac
  >- (simp[step_inst_def, step_swap_def, consume_gas_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, step_swap_def, consume_gas_def,
       inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def] >>
  `SUC n < LENGTH a` by simp[] >>
  drule_all bytecode_stack_describes_swap >>
  Cases_on `h0.stack` >> gvs[EL, arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1]
QED

Theorem sb_pop_contract[local]:
  sb_opcode_contract Pop
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  drule bytecode_stack_describes_length >> strip_tac >>
  simp[sb_successors_def, bytecode_stack_successors_def, bytecode_stack_io_def] >>
  conj_tac
  >- (simp[step_inst_def, step_pop_def, consume_gas_def, pop_stack_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, step_pop_def, consume_gas_def,
       pop_stack_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def] >>
  irule bytecode_stack_describes_drop >> simp[]
QED

Theorem sb_jumpdest_contract[local]:
  sb_opcode_contract JumpDest
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  simp[sb_successors_def, bytecode_stack_successors_def, bytecode_stack_io_def] >>
  conj_tac
  >- (simp[step_inst_def, consume_gas_def,
           bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, consume_gas_def,
       inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def]
QED

Theorem sb_jump_contract[local]:
  sb_opcode_contract Jump
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  drule bytecode_stack_describes_length >> strip_tac >>
  simp[sb_successors_def, bytecode_stack_successors_def] >>
  conj_tac
  >- (simp[step_inst_def, step_jump_def, consume_gas_def, pop_stack_def,
           set_jump_dest_def, bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, step_jump_def, consume_gas_def,
       pop_stack_def, set_jump_dest_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def] >>
  gvs[NULL_EQ] >>
  namedCases_on `a` ["", "av ats"] >>
  namedCases_on `h0.stack` ["", "w wts"] >>
  gvs[bytecode_stack_describes_def, MEM_MAP, sb_at_def] >>
  qexists_tac `(w2n w,ats)` >>
  simp[sb_at_def, bytecode_stack_describes_def] >>
  irule sb_jump_target >> simp[]
QED

Theorem sb_jumpi_contract[local]:
  sb_opcode_contract JumpI
Proof
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `wf_context h0` by gvs[wf_state_def] >>
  gvs[wf_context_def, sb_decoded_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code) h0.pc` >>
  gvs[] >>
  drule bytecode_stack_describes_length >> strip_tac >>
  simp[sb_successors_def, bytecode_stack_successors_def] >>
  conj_tac
  >- (simp[step_inst_def, step_jumpi_def, consume_gas_def, pop_stack_def,
           set_jump_dest_def, bind_def, ignore_bind_def, get_current_context_def,
           set_current_context_def, assert_def, return_def, fail_def] >>
      rw[] >> gvs[return_def, fail_def]) >>
  simp[sb_inner_def, step_inst_def, step_jumpi_def, consume_gas_def,
       pop_stack_def, set_jump_dest_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, get_current_context_def, set_current_context_def,
       assert_def, return_def, fail_def] >>
  rw[] >> gvs[return_def, fail_def, sb_at_def] >>
  gvs[set_current_context_def, return_def, bind_def, assert_def, fail_def]
  >- (qexists_tac `(h0.pc + LENGTH (opcode JumpI),DROP 2 a)` >>
      simp[sb_at_def] >>
      irule bytecode_stack_describes_drop >> simp[]) >>
  Cases_on `w2n (HD (TAKE 2 h0.stack)) < LENGTH h0.msgParams.code /\
    FLOOKUP (parse_code 0 FEMPTY h0.msgParams.code)
      (w2n (HD (TAKE 2 h0.stack))) = SOME JumpDest` >> gvs[] >>
  namedCases_on `a` ["", "av ats"] >>
  namedCases_on `h0.stack` ["", "w wts"] >>
  gvs[bytecode_stack_describes_def, MEM_MAP] >>
  qexists_tac `(w2n w,DROP 2 (av::ats))` >>
  simp[sb_at_def, bytecode_stack_describes_def] >>
  conj_tac
  >- (disj2_tac >> irule sb_jump_target >> simp[]) >>
  simp[LIST_REL_DROP]
QED

(* Published family interface used by the all-opcode refinement theorem. *)
Theorem sb_stack_control_contracts:
  (!n ws. sb_opcode_contract (Push n ws)) /\
  (!n. sb_opcode_contract (Dup n)) /\
  (!n. sb_opcode_contract (Swap n)) /\
  sb_opcode_contract Pop /\ sb_opcode_contract Jump /\
  sb_opcode_contract JumpI /\ sb_opcode_contract JumpDest
Proof
  simp[sb_push_contract, sb_dup_contract, sb_swap_contract,
       sb_pop_contract, sb_jump_contract, sb_jumpi_contract, sb_jumpdest_contract]
QED
