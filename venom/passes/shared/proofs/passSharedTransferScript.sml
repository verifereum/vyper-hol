(*
 * Pass Shared Transfer Properties
 *
 * Transfer lemma: if step_inst_base returns OK on state s1, and state s2
 * agrees on operand values, key context fields, and tracked state fields,
 * then step_inst_base also returns OK on s2 AND the results agree on
 * output variables and all written state fields.
 *
 * Isolated in its own file because expanding step_inst_base_def over
 * all ~90 opcodes is expensive (~25s).
 *
 * TOP-LEVEL EXPORTS:
 *   step_inst_base_ok_transfer — OK transfers across agreeing states
 *   step_inst_base_output_determined_fields — per-field output determinism
 *)

Theory passSharedTransfer
Ancestors
  passSharedDefs venomExecSemantics venomEffects

open venomStateTheory venomInstTheory venomExecSemanticsTheory
     venomEffectsTheory venomInstPropsTheory;

(* Helper: eval_operands agreement from pointwise eval_operand agreement *)
Theorem eval_operands_agree_lem[local]:
  !ops s s'.
    (!op. MEM op ops ==> eval_operand op s = eval_operand op s') ==>
    eval_operands ops s = eval_operands ops s'
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operand h s = eval_operand h s'` by gvs[] >>
  `eval_operands ops s = eval_operands ops s'` by
    (first_x_assum irule >> rw[]) >>
  simp[]
QED

(* Helper: resolve_phi result is a member of the operand list *)
Theorem resolve_phi_mem[local]:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >>
  rw[resolve_phi_def, AllCaseEqs()] >> gvs[] >>
  res_tac >> gvs[]
QED

Theorem mem_drop_subset[local]:
  !n l x. MEM x (DROP n l) ==> MEM x l
Proof
  Induct >> rw[] >> Cases_on `l` >> gvs[] >> res_tac >> gvs[]
QED

(* State-accessing function defs used by step_inst_base helpers.
   Needed so gvs can rewrite through field equalities (e.g.
   s1.vs_memory = s2.vs_memory ==> mload x s1 = mload x s2). *)
val state_fn_defs = [mload_def, mstore_def, sload_def, sstore_def,
  tload_def, tstore_def, contract_storage_def, contract_transient_def,
  write_memory_with_expansion_def, write_memory_def, expand_memory_def,
  read_memory_def, mcopy_def];

(* Shared tactic for output_determined: close goals after opcode case split.
   After Cases_on opcode and gvs, handles:
   - PHI (resolve_phi_mem + operand agreement)
   - LOG (eval_operands_agree_lem on sublists)
   - General cases (res_tac + update_var/lookup_var + state fn expansion) *)
val transfer_close_tac =
  TRY (imp_res_tac resolve_phi_mem >> res_tac >> gvs[] >>
       gvs[update_var_def, lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY (gvs (update_var_def :: lookup_var_def ::
            finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs) >>
       res_tac >> gvs[] >> NO_TAC) >>
  TRY (
    `eval_operands (DROP 2 rest) s1 = eval_operands (DROP 2 rest) s2` by (
      irule eval_operands_agree_lem >> rpt strip_tac >>
      first_x_assum irule >>
      imp_res_tac mem_drop_subset >> gvs[]) >>
    `eval_operand (HD rest) s1 = eval_operand (HD rest) s2` by (
      first_x_assum irule >> Cases_on `rest` >> gvs[]) >>
    `eval_operand (EL 1 rest) s1 = eval_operand (EL 1 rest) s2` by (
      first_x_assum irule >>
      Cases_on `rest` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    gvs[] >> NO_TAC) >>
  res_tac >> gvs (update_var_def :: lookup_var_def ::
                  finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs);

(* OK transfer: if step_inst_base returns OK on s, it also returns OK on s'
   when operands and relevant context fields agree. *)
Theorem step_inst_base_ok_transfer:
  !inst s v s'.
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s = eval_operand op s') /\
    (inst.inst_opcode = PHI ==> s.vs_prev_bb = s'.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s.vs_params = s'.vs_params) /\
    (inst.inst_opcode = OFFSET ==> s.vs_label_offsets = s'.vs_label_offsets) /\
    (inst.inst_opcode = RETURNDATACOPY ==>
       s.vs_returndata = s'.vs_returndata) ==>
    ?v'. step_inst_base inst s' = OK v'
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s' = eval_operand op s` by
    (rpt strip_tac >> res_tac >> gvs[]) >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, exec_pure1_def, exec_pure2_def,
       exec_pure3_def, exec_read0_def, exec_read1_def,
       exec_write2_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  TRY (imp_res_tac resolve_phi_mem >> res_tac >> gvs[] >> NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* LOG case *)
  `eval_operands (DROP 2 rest) s' = eval_operands (DROP 2 rest) s` by (
    irule eval_operands_agree_lem >> rpt strip_tac >>
    first_x_assum irule >>
    imp_res_tac mem_drop_subset >> gvs[]) >>
  `eval_operand (HD rest) s' = eval_operand (HD rest) s` by (
    first_x_assum irule >> Cases_on `rest` >> gvs[]) >>
  `eval_operand (EL 1 rest) s' = eval_operand (EL 1 rest) s` by (
    first_x_assum irule >>
    Cases_on `rest` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  gvs[]
QED

(* Per-field output determinism: each field conclusion has only the
   preconditions it needs. The accounts field uses individual effect
   conditions rather than a 3-way disjunction, making it easier to
   apply when effects_independent only gives per-effect disjointness. *)
Theorem step_inst_base_output_determined_fields:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = OFFSET ==> s1.vs_label_offsets = s2.vs_label_offsets) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (* Read-field agreements: individual effect conditions (not grouped) *)
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
       s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
       s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
       s1.vs_immutables = s2.vs_immutables) /\
    (Eff_RETURNDATA IN read_effects inst.inst_opcode ==>
       s1.vs_returndata = s2.vs_returndata) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
       s1.vs_logs = s2.vs_logs) ==>
    (* Memory *)
    ((Eff_MEMORY IN write_effects inst.inst_opcode \/
      Eff_MSIZE IN write_effects inst.inst_opcode) /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_memory = v2.vs_memory) /\
    (* Transient *)
    (Eff_TRANSIENT IN write_effects inst.inst_opcode /\
     s1.vs_transient = s2.vs_transient ==>
       v1.vs_transient = v2.vs_transient) /\
    (* Accounts *)
    ((Eff_STORAGE IN write_effects inst.inst_opcode \/
      Eff_BALANCE IN write_effects inst.inst_opcode) /\
     s1.vs_accounts = s2.vs_accounts ==>
       v1.vs_accounts = v2.vs_accounts) /\
    (* Immutables *)
    (Eff_IMMUTABLES IN write_effects inst.inst_opcode /\
     s1.vs_immutables = s2.vs_immutables /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_immutables = v2.vs_immutables) /\
    (* Returndata *)
    (Eff_RETURNDATA IN write_effects inst.inst_opcode /\
     s1.vs_returndata = s2.vs_returndata /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_returndata = v2.vs_returndata) /\
    (* Logs *)
    (Eff_LOG IN write_effects inst.inst_opcode /\
     s1.vs_logs = s2.vs_logs /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_logs = v2.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
  qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
  simp[step_inst_base_def, exec_pure1_def, exec_pure2_def,
       exec_pure3_def, exec_read0_def, exec_read1_def,
       exec_write2_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  transfer_close_tac
QED

val _ = export_theory();
