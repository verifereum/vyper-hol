(* Shared effects are independent of the relocated local values.  Operand
   equalities below are explicit: normalized locals are NOT executable locals. *)
Theory readonlyInvokeCopyFwdEffects
Ancestors
  readonlyInvokeCopyFwdRel taintAgree venomExecSemantics venomState
  finite_map words list pred_set o1LowerDloadShared codegenRel ptrDiscipline

Definition ricf_effect_agree_def:
  ricf_effect_agree D X tn s t <=>
    taint_agree D X tn s
      (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>)
End

Definition ricf_effect_result_def:
  ricf_effect_result D X tn r q <=>
    case (r,q) of
      (OK s, OK t) => ricf_effect_agree D X tn s t
    | (Halt s, Halt t) => ricf_effect_agree D X tn s t
    | (Abort a s, Abort b t) => a = b
    | (Error e, Error f) => e = f
    | (IntRet v s, IntRet w t) => v = w /\ ricf_effect_agree D X tn s t
    | _ => F
End

Theorem ricf_frame_effect:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_effect_agree D X tn s t
Proof
  simp[ricf_frame_agree_def, ricf_effect_agree_def]
QED

(* The output values may differ; Values owns their provenance relation. *)
Theorem ricf_effect_update_var:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_agree D X tn (update_var out x s) (update_var out y t)
Proof
  simp[ricf_effect_agree_def, taint_agree_def, update_var_def,
       ld_shared_agree_def, word_agree_except_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality]
QED

Theorem ricf_effect_pure1:
  ricf_effect_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_effect_result D X tn (exec_pure1 f inst s) (exec_pure1 f inst t)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[exec_pure1_def, ricf_effect_result_def] >>
  namedCases_on `ops` ["", "b rest"] >>
  gvs[exec_pure1_def, ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >>
  gvs[exec_pure1_def, ricf_effect_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  gvs[exec_pure1_def, ricf_effect_result_def] >>
  Cases_on `outs` >>
  gvs[exec_pure1_def, ricf_effect_result_def, ricf_effect_update_var]
QED

Theorem ricf_effect_pure2:
  ricf_effect_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_effect_result D X tn (exec_pure2 f inst s) (exec_pure2 f inst t)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[exec_pure2_def, ricf_effect_result_def] >>
  namedCases_on `ops` ["", "b rest"] >>
  gvs[exec_pure2_def, ricf_effect_result_def] >>
  Cases_on `rest` >> gvs[exec_pure2_def, ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >>
  gvs[exec_pure2_def, ricf_effect_result_def] >>
  Cases_on `eval_operand b t` >>
  gvs[exec_pure2_def, ricf_effect_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  gvs[exec_pure2_def, ricf_effect_result_def] >>
  Cases_on `outs` >>
  gvs[exec_pure2_def, ricf_effect_result_def, ricf_effect_update_var]
QED

Theorem ricf_effect_pure3:
  ricf_effect_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_effect_result D X tn (exec_pure3 f inst s) (exec_pure3 f inst t)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  namedCases_on `ops` ["", "b rest"] >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  namedCases_on `rest` ["", "c tail"] >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  Cases_on `tail` >> gvs[exec_pure3_def, ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  Cases_on `eval_operand b t` >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  Cases_on `eval_operand c t` >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  gvs[exec_pure3_def, ricf_effect_result_def] >>
  Cases_on `outs` >>
  gvs[exec_pure3_def, ricf_effect_result_def, ricf_effect_update_var]
QED

Theorem ricf_effect_jump_to:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_agree D X tn (jump_to lbl s) (jump_to lbl t)
Proof
  simp[ricf_effect_agree_def, taint_agree_def, jump_to_def,
       ld_shared_agree_def] >> rpt strip_tac >>
  gvs[venom_state_component_equality]
QED

(* Abort transport intentionally makes no claim about the reverted state. *)
Theorem ricf_effect_assert:
  ricf_effect_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE; INVALID; PHI] ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> fs[MEM] >> simp[step_inst_base_opcode_eqs, ricf_effect_result_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_effect_result_def] >> Cases_on `ops` >>
  gvs[ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_effect_result_def] >>
  IF_CASES_TAC >> simp[ricf_effect_result_def]
QED

Theorem ricf_effect_jmp:
  ricf_effect_agree D X tn s t /\ inst.inst_opcode = JMP ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_effect_result_def] >> Cases_on `a` >>
  gvs[ricf_effect_result_def] >> Cases_on `ops` >>
  simp[ricf_effect_result_def, ricf_effect_jump_to]
QED

Theorem ricf_effect_djmp:
  ricf_effect_agree D X tn s t /\ inst.inst_opcode = DJMP /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_effect_result_def] >>
  Cases_on `extract_labels ops` >> gvs[ricf_effect_result_def] >>
  IF_CASES_TAC >> simp[ricf_effect_result_def, ricf_effect_jump_to]
QED

Theorem ricf_effect_jnz:
  ricf_effect_agree D X tn s t /\ inst.inst_opcode = JNZ /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_effect_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> gvs[ricf_effect_result_def] >>
  Cases_on `b` >> gvs[ricf_effect_result_def] >>
  namedCases_on `rest` ["", "c tail"] >> gvs[ricf_effect_result_def] >>
  Cases_on `c` >> gvs[ricf_effect_result_def] >>
  Cases_on `tail` >> gvs[ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a t` >> gvs[ricf_effect_result_def] >>
  IF_CASES_TAC >> simp[ricf_effect_result_def, ricf_effect_jump_to]
QED

Theorem ricf_effect_read0:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_result D X tn (exec_read0 f inst s) (exec_read0 g inst t)
Proof
  strip_tac >> namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_read0_def, ricf_effect_result_def] >> Cases_on `outs` >>
  simp[exec_read0_def, ricf_effect_result_def, ricf_effect_update_var]
QED

Theorem ricf_effect_read1:
  ricf_effect_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
  ricf_effect_result D X tn (exec_read1 f inst s) (exec_read1 g inst t)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[exec_read1_def, ricf_effect_result_def] >>
  Cases_on `ops` >> gvs[exec_read1_def, ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand a t` >>
  gvs[exec_read1_def, ricf_effect_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  gvs[exec_read1_def, ricf_effect_result_def] >> Cases_on `outs` >>
  simp[exec_read1_def, ricf_effect_result_def, ricf_effect_update_var]
QED

Theorem ricf_effect_ret:
  ricf_effect_agree D X tn s t /\ inst.inst_opcode = RET /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  Cases_on `eval_operands inst.inst_operands t` >>
  gvs[ricf_effect_result_def] >> Cases_on `x` >>
  simp[ricf_effect_result_def]
QED

Theorem ricf_effect_revert:
  inst.inst_opcode = REVERT /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >>
  gvs[ricf_effect_result_def] >>
  namedCases_on `ops` ["", "b tail"] >> gvs[ricf_effect_result_def] >>
  Cases_on `tail` >> gvs[ricf_effect_result_def, MEM] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand a t` >>
  gvs[ricf_effect_result_def] >>
  Cases_on `eval_operand b s` >> Cases_on `eval_operand b t` >>
  gvs[ricf_effect_result_def] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_effect_sstore:
  ricf_effect_agree D X tn s t /\ word_agree_except m v w ==>
  ricf_effect_agree D X (tn with t_stor := key_update tn.t_stor key m)
    (sstore key v s) (sstore key w t)
Proof
  simp[ricf_effect_agree_def] >> strip_tac >>
  drule_all taint_agree_sstore >> simp[sstore_def]
QED

Theorem ricf_effect_tstore:
  ricf_effect_agree D X tn s t /\ word_agree_except m v w ==>
  ricf_effect_agree D X (tn with t_trans := key_update tn.t_trans key m)
    (tstore key v s) (tstore key w t)
Proof
  simp[ricf_effect_agree_def] >> strip_tac >>
  drule_all taint_agree_tstore >> simp[tstore_def]
QED

Theorem ricf_effect_halt_state:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_agree D X tn (halt_state s) (halt_state t)
Proof
  simp[ricf_effect_agree_def, taint_agree_def, halt_state_def,
       ld_shared_agree_def] >> rpt strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem ricf_effect_returndata:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_agree D X tn (set_returndata rd s) (set_returndata rd t)
Proof
  simp[ricf_effect_agree_def, taint_agree_def, set_returndata_def,
       ld_shared_agree_def] >> rpt strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem ricf_effect_simple_halt:
  ricf_effect_agree D X tn s t /\ MEM inst.inst_opcode [STOP; SINK] ==>
  ricf_effect_result D X tn (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> fs[MEM] >>
  simp[step_inst_base_opcode_eqs, ricf_effect_result_def, ricf_effect_halt_state] >>
  irule ricf_effect_halt_state >>
  drule ricf_effect_returndata >> simp[set_returndata_def]
QED

Theorem ricf_effect_gas_readings:
  ricf_effect_agree D X tn s t ==>
  s.vs_gas_readings = t.vs_gas_readings
Proof
  simp[ricf_effect_agree_def] >> strip_tac >>
  drule taint_agree_frame >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_gas_readings`) >> simp[]
QED

Theorem ricf_effect_gas_tail:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_agree D X tn
    (s with vs_gas_readings := rest) (t with vs_gas_readings := rest)
Proof
  simp[ricf_effect_agree_def, taint_agree_def, ld_shared_agree_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality]
QED

Theorem ricf_effect_gas:
  ricf_effect_agree D X tn s t ==>
  ricf_effect_result D X tn (exec_gas inst s) (exec_gas inst t)
Proof
  strip_tac >> drule ricf_effect_gas_readings >> strip_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_gas_def, ricf_effect_result_def] >>
  Cases_on `outs` >> simp[exec_gas_def, ricf_effect_result_def] >>
  Cases_on `t.vs_gas_readings` >>
  simp[ricf_effect_result_def, ricf_effect_update_var, ricf_effect_gas_tail]
QED
