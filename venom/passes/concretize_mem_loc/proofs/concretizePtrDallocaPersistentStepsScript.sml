Theory concretizePtrDallocaPersistentSteps
Ancestors
  ptrDiscipline lowerDloadMaskedStorage lowerDloadPtrCreateInterfaces
  venomExecSemantics venomCallOracleDefs extCallOracle venomState venomInst
  finite_map pred_set list

(* Persistent masks need only the demanded store selector, not equality of
   states.  These boundaries apply to actual step_taint results, including
   halting results.  The chronology join must supply selector evaluation,
   operand-mask inclusion, and the oracle adoption decision separately. *)
Theorem ptr_dalloca_store_mask_mono[local]:
  Y SUBSET X /\
  (!a v. inst.inst_opcode = opc /\ inst.inst_operands = [a;v] ==>
     eval_operand a t = eval_operand a s /\
     op_taint un v SUBSET op_taint tn v) ==>
  store_taint opc un inst t Y SUBSET store_taint opc tn inst s X
Proof
  strip_tac >> simp[store_taint_def] >>
  Cases_on `inst.inst_opcode = opc` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::v::rest` >> Cases_on `rest` >> simp[] >>
  first_x_assum (qspecl_then [`h`,`v`] strip_assume_tac) >>
  gvs[] >> Cases_on `eval_operand h s` >> simp[ld_key_update_mono]
QED

Theorem ptr_dalloca_imm_mask_mono[local]:
  un.t_imm SUBSET tn.t_imm /\
  (!a v. inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] ==>
     eval_operand a t = eval_operand a s /\
     op_taint un v SUBSET op_taint tn v) ==>
  imm_taint un inst t SUBSET imm_taint tn inst s
Proof
  strip_tac >> simp[imm_taint_def] >>
  Cases_on `inst.inst_opcode = ISTORE` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::v::rest` >> Cases_on `rest` >> simp[] >>
  first_x_assum (qspecl_then [`h`,`v`] strip_assume_tac) >>
  gvs[] >> Cases_on `eval_operand h s` >> simp[ld_key_update_mono]
QED

Theorem ptr_dalloca_adopt_mask_mono[local]:
  Y SUBSET X /\ instT.inst_opcode = inst.inst_opcode /\
  (MEM inst.inst_opcode [CALL;DELEGATECALL;CREATE;CREATE2] ==>
   adoptedT = adopted) ==>
  adopt_reset instT adoptedT Y SUBSET adopt_reset inst adopted X
Proof
  rw[adopt_reset_def] >> gvs[]
QED

Theorem ptr_dalloca_persistent_next:
  un.t_stor SUBSET tn.t_stor /\
  un.t_trans SUBSET tn.t_trans /\ un.t_imm SUBSET tn.t_imm /\
  (instT = inst \/
   (inst.inst_opcode = ALLOCA /\ instT.inst_opcode = ASSIGN)) /\
  (!a v. (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE \/
          inst.inst_opcode = ISTORE) /\ inst.inst_operands = [a;v] ==>
     eval_operand a t = eval_operand a s /\
     op_taint un v SUBSET op_taint tn v) /\
  (MEM inst.inst_opcode [CALL;DELEGATECALL;CREATE;CREATE2] ==>
    ((adopt_guard t.vs_call_ctx.cc_static t postT ((HD t.vs_outcomes).co_success \/ MEM inst.inst_opcode [CREATE;CREATE2])) =
     (adopt_guard s.vs_call_ctx.cc_static s post ((HD s.vs_outcomes).co_success \/ MEM inst.inst_opcode [CREATE;CREATE2])))) ==>
  (step_taint instT t postT un).t_stor SUBSET
    (step_taint inst s post tn).t_stor /\
  (step_taint instT t postT un).t_trans SUBSET
    (step_taint inst s post tn).t_trans /\
  (step_taint instT t postT un).t_imm SUBSET
    (step_taint inst s post tn).t_imm
Proof
  strip_tac >>
  Cases_on `instT = inst`
  >- (gvs[step_taint_def] >> rpt conj_tac
      >- (irule ptr_dalloca_adopt_mask_mono >> simp[] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          irule ptr_dalloca_store_mask_mono >> simp[])
      >- (irule ptr_dalloca_adopt_mask_mono >> simp[] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          irule ptr_dalloca_store_mask_mono >> simp[])
      >> irule ptr_dalloca_imm_mask_mono >> simp[]) >>
  gvs[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]
QED

(* The non-CALL opcodes cannot select a computed precompile. An actual
   successful dispatch has a nonempty queue and consumes its head. *)
Theorem ptr_dalloca_noncall_reset_step:
  MEM inst.inst_opcode [DELEGATECALL;CREATE;CREATE2] /\
  step_inst fuel C inst s = OK post ==>
  ((adopt_guard s.vs_call_ctx.cc_static s post ((HD s.vs_outcomes).co_success \/ MEM inst.inst_opcode [CREATE;CREATE2])) <=>
   (~s.vs_call_ctx.cc_static /\
    ((HD s.vs_outcomes).co_success \/ MEM inst.inst_opcode [CREATE;CREATE2])))
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac
  >>~- ([`exec_delegatecall _ _ _ _ _ _ _ _ = _`],
    qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
    simp[exec_delegatecall_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
    pairarg_tac >> simp[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
    strip_tac >> gvs[Excl "consume_call_outcome_eq"] >>
    Cases_on `s.vs_outcomes` >>
    gvs[consume_call_outcome_eq, venom_call_request_def, take_outcome_def,
        computed_precompile_def, record_request_def, update_var_def]) >>
  gvs[dload_exec_create_success_iff, Excl "consume_create_outcome_eq"] >>
  Cases_on `s.vs_outcomes` >>
  gvs[consume_create_outcome_eq, venom_create_request_def, take_outcome_def,
      computed_precompile_def, record_request_def, update_var_def]
QED

(* Block entry changes only t_var.  INVOKE entry clears it, and return
   restores a restricted saved map; arbitrary maps below cover both forms. *)
Theorem ptr_dalloca_persistent_control:
  un.t_stor SUBSET tn.t_stor /\
  un.t_trans SUBSET tn.t_trans /\ un.t_imm SUBSET tn.t_imm ==>
  ((un with t_var := tvT).t_stor SUBSET (tn with t_var := tv).t_stor /\
   (un with t_var := tvT).t_trans SUBSET (tn with t_var := tv).t_trans /\
   (un with t_var := tvT).t_imm SUBSET (tn with t_var := tv).t_imm) /\
  ((entry_taint_vars fnT t un).t_stor SUBSET
      (entry_taint_vars fn s tn).t_stor /\
   (entry_taint_vars fnT t un).t_trans SUBSET
      (entry_taint_vars fn s tn).t_trans /\
   (entry_taint_vars fnT t un).t_imm SUBSET
      (entry_taint_vars fn s tn).t_imm)
Proof
  simp[entry_taint_vars_def] >> strip_tac >>
  Cases_on `lookup_block t.vs_current_bb fnT.fn_blocks` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED
