(*
 * Pass Shared Variable Frame Properties
 *
 * Variable-frame theorems for instruction execution: unreferenced variable
 * updates pass through step_inst_base and step_inst.
 *
 * TOP-LEVEL EXPORTS:
 *   step_inst_base_var_frame_full — var update passes through step_inst_base
 *   step_inst_var_frame_full — var update passes through step_inst
 *)

Theory passSharedVarFrame
Ancestors
  passSharedProps

open venomStateTheory venomInstTheory venomExecSemanticsTheory
     venomEffectsTheory venomInstPropsTheory;

(* ===================================================================== *)
(* ===== Variable/State Helpers ======================================== *)
(* ===================================================================== *)

Theorem update_var_commutes[local]:
  !x y vx vy s. x <> y ==>
    update_var x vx (update_var y vy s) =
    update_var y vy (update_var x vx s)
Proof
  simp[update_var_def, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem eval_operand_update_other[local]:
  !op y v s.
    ~MEM y (operand_vars [op]) ==>
    eval_operand op (update_var y v s) = eval_operand op s
Proof
  Cases >> rw[eval_operand_def, operand_vars_def, operand_var_def,
              lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem eval_operand_update_other_list[local]:
  !ops x v s.
    ~MEM x (operand_vars ops) ==>
    !op. MEM op ops ==>
    eval_operand op (update_var x v s) = eval_operand op s
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def] >>
  Cases_on `op = h` >> gvs[] >>
  TRY (Cases_on `h` >> gvs[operand_var_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  metis_tac[]
QED

Theorem eval_operands_update_var[local]:
  !ops x v s.
    ~MEM x (operand_vars ops) ==>
    eval_operands ops (update_var x v s) = eval_operands ops s
Proof
  Induct >> rw[eval_operands_def, operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def] >>
  `~MEM x (operand_vars [h])` by
    (rw[operand_vars_def] >> Cases_on `operand_var h` >> gvs[]) >>
  imp_res_tac eval_operand_update_other >> gvs[]
QED

Theorem resolve_phi_mem[local]:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def] >> gvs[AllCaseEqs()]
QED

val operand_vars_drop = prove(
  ``!ops x n. ~MEM x (operand_vars ops) ==>
              ~MEM x (operand_vars (DROP n ops))``,
  Induct >> rw[operand_vars_def] >>
  Cases_on `n` >> gvs[] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def]);

(* ===================================================================== *)
(* ===== Non-terminator result type elimination ======================== *)
(* ===================================================================== *)

val step_base_result_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])));

Theorem step_inst_base_no_halt[local]:
  !inst s s'.
    step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  step_base_result_tac
QED

Theorem step_inst_base_no_intret[local]:
  !inst s vs s'.
    step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  step_base_result_tac
QED

(* Only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY can abort
   among non-terminators *)
Theorem step_inst_base_abort_opcodes[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  step_base_result_tac
QED

(* ===================================================================== *)
(* ===== External call update_var lemmas =============================== *)
(* ===================================================================== *)

val exec_ext_call_update_var = prove(
  ``!inst x w s g a v ao as_ ro rs is_s.
    ~MEM x inst.inst_outputs ==>
    exec_ext_call inst (update_var x w s) g a v ao as_ ro rs is_s =
    case exec_ext_call inst s g a v ao as_ ro rs is_s of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_ext_call_def, read_memory_def, update_var_def,
     make_venom_call_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val exec_delegatecall_update_var = prove(
  ``!inst x w s g a ao as_ ro rs.
    ~MEM x inst.inst_outputs ==>
    exec_delegatecall inst (update_var x w s) g a ao as_ ro rs =
    case exec_delegatecall inst s g a ao as_ ro rs of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_delegatecall_def, read_memory_def, update_var_def,
     make_venom_delegatecall_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val exec_create_update_var = prove(
  ``!inst x w s v off sz salt.
    ~MEM x inst.inst_outputs ==>
    exec_create inst (update_var x w s) v off sz salt =
    case exec_create inst s v off sz salt of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_create_def, update_var_def,
     make_venom_create_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def,
     read_memory_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val wmwe_update_var = prove(
  ``!x w off dat s.
    write_memory_with_expansion off dat (update_var x w s) =
    update_var x w (write_memory_with_expansion off dat s)``,
  rw[write_memory_with_expansion_def, update_var_def]);

val exec_call_var_thms =
  [exec_ext_call_update_var, exec_delegatecall_update_var,
   exec_create_update_var, wmwe_update_var];

(* ===================================================================== *)
(* ===== step_inst_base_var_frame_full ================================= *)
(* ===================================================================== *)

(* Full var-frame for step_inst_base: all result types.
   Directly proved without intermediate OK-only lemma.
   Strategy: case split on result type, then handle each. *)
Theorem step_inst_base_var_frame_full:
  !inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs /\
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (update_var x w st) =
    case step_inst_base inst st of
      OK st' => OK (update_var x w st')
    | Abort a st' => Abort a (update_var x w st')
    | Error e => Error e
    | other => other
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  `eval_operands inst.inst_operands (update_var x w st) =
   eval_operands inst.inst_operands st`
    by (irule eval_operands_update_var >> gvs[]) >>
  (* Shared tactic for OK and Error bulk case split *)
  let val bulk_tac =
    Cases_on `inst.inst_opcode = PHI`
    >- (gvs[step_inst_base_def] >>
        Cases_on `inst.inst_outputs` >> gvs[] >>
        Cases_on `t` >> gvs[] >>
        Cases_on `st.vs_prev_bb` >> gvs[update_var_def] >>
        Cases_on `resolve_phi x' inst.inst_operands` >> gvs[] >>
        imp_res_tac resolve_phi_mem >> res_tac >>
        Cases_on `eval_operand x'' st` >> gvs[] >>
        gvs[update_var_def, finite_mapTheory.FUPDATE_COMMUTES]) >>
    Cases_on `inst.inst_opcode = LOG`
    >- (gvs[step_inst_base_def] >>
        Cases_on `inst.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[] >>
        rename1 `Lit tc :: rest` >>
        `~MEM x (operand_vars rest)` by
          gvs[operand_vars_def, operand_var_def] >>
        `!op. MEM op rest ==>
              eval_operand op (update_var x w st) = eval_operand op st` by
          metis_tac[eval_operand_update_other_list] >>
        `eval_operands (DROP 2 rest) (update_var x w st) =
         eval_operands (DROP 2 rest) st` by (
          irule eval_operands_update_var >>
          metis_tac[operand_vars_drop]) >>
        Cases_on `rest` >> gvs[] >>
        Cases_on `t` >> gvs[] >> simp[] >>
        Cases_on `eval_operand h st` >> gvs[] >>
        Cases_on `eval_operand h' st` >> gvs[] >>
        Cases_on `eval_operands t' st` >> gvs[] >>
        gvs[update_var_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
    fs[step_inst_base_def,
       exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, next_alloca_offset_def, eval_operands_def] >>
    RULE_ASSUM_TAC (SIMP_RULE list_ss []) >>
    gvs[AllCaseEqs()] >>
    rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
    gvs(update_var_def :: finite_mapTheory.FUPDATE_COMMUTES ::
        mload_def :: mstore_def :: sload_def :: sstore_def ::
        tload_def :: tstore_def :: mcopy_def :: read_memory_def ::
        contract_storage_def :: contract_transient_def ::
        revert_state_def :: halt_state_def :: set_returndata_def ::
        exec_call_var_thms) >>
    gvs[AllCaseEqs()]
  in
  Cases_on `step_inst_base inst st` >> gvs[]
  (* OK *)
  >- bulk_tac
  (* Halt: impossible for non-terminators *)
  >- (metis_tac[step_inst_base_no_halt])
  (* Abort: only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY *)
  >- (imp_res_tac step_inst_base_abort_opcodes >>
      gvs[step_inst_base_def, AllCaseEqs(),
        update_var_def, finite_mapTheory.FUPDATE_COMMUTES,
        revert_state_def, halt_state_def, set_returndata_def,
        write_memory_with_expansion_def, read_memory_def])
  (* IntRet: impossible for non-terminators *)
  >- (metis_tac[step_inst_base_no_intret])
  (* Error *)
  >> bulk_tac
  end
QED

(* ===================================================================== *)
(* ===== INVOKE helpers ================================================ *)
(* ===================================================================== *)

Theorem setup_callee_update_var[local]:
  !fn args x w s.
    setup_callee fn args (update_var x w s) = setup_callee fn args s
Proof
  rw[setup_callee_def, update_var_def]
QED

Theorem merge_callee_update_var[local]:
  !x w caller callee.
    merge_callee_state (update_var x w caller) callee =
    update_var x w (merge_callee_state caller callee)
Proof
  rw[merge_callee_state_def, update_var_def]
QED

Theorem foldl_update_var_comm[local]:
  !pairs x w s.
    ~MEM x (MAP FST pairs) ==>
    FOLDL (\s' (out,val). update_var out val s') (update_var x w s) pairs =
    update_var x w (FOLDL (\s' (out,val). update_var out val s') s pairs)
Proof
  Induct >> rw[] >>
  Cases_on `h` >> gvs[] >>
  first_x_assum (qspecl_then [`x`, `w`, `update_var q r s`] mp_tac) >>
  rw[update_var_commutes]
QED

Theorem bind_outputs_update_var[local]:
  !outs vals x w s.
    ~MEM x outs /\ LENGTH outs = LENGTH vals ==>
    bind_outputs outs vals (update_var x w s) =
    OPTION_MAP (update_var x w) (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >>
  irule foldl_update_var_comm >>
  `MAP FST (ZIP (outs,vals)) = outs` suffices_by gvs[] >>
  irule (cj 1 listTheory.MAP_ZIP) >> gvs[]
QED

(* ===================================================================== *)
(* ===== step_inst_var_frame_full ====================================== *)
(* ===================================================================== *)

Theorem step_inst_var_frame_full:
  !fuel ctx inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs /\
    ~is_terminator inst.inst_opcode ==>
    step_inst fuel ctx inst (update_var x w st) =
    case step_inst fuel ctx inst st of
      OK st' => OK (update_var x w st')
    | Abort a st' =>
        if inst.inst_opcode = INVOKE then Abort a st'
        else Abort a (update_var x w st')
    | other => other
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  (* INVOKE *)
  >- (simp[step_inst_def] >>
      `!op. MEM op inst.inst_operands ==>
            eval_operand op (update_var x w st) = eval_operand op st`
        by metis_tac[eval_operand_update_other_list] >>
      Cases_on `decode_invoke inst` >> gvs[] >>
      Cases_on `x'` >> gvs[] >>
      rename1 `SOME (callee_name, arg_ops)` >>
      `inst.inst_operands = Label callee_name :: arg_ops`
        by gvs[decode_invoke_def, AllCaseEqs()] >>
      `~MEM x (operand_vars arg_ops)` by
        gvs[operand_vars_def, operand_var_def] >>
      `eval_operands arg_ops (update_var x w st) =
       eval_operands arg_ops st`
        by (irule eval_operands_update_var >> gvs[]) >>
      Cases_on `lookup_function callee_name ctx.ctx_functions` >> gvs[] >>
      rename1 `SOME callee_fn` >>
      Cases_on `eval_operands arg_ops st` >> gvs[] >>
      rename1 `SOME args` >>
      gvs[setup_callee_update_var] >>
      Cases_on `setup_callee callee_fn args st` >> gvs[] >>
      rename1 `SOME callee_s` >>
      Cases_on `run_function fuel ctx callee_fn callee_s` >> gvs[] >>
      rename1 `IntRet vals callee_s'` >>
      gvs[merge_callee_update_var] >>
      Cases_on `LENGTH inst.inst_outputs = LENGTH vals`
      >- (`bind_outputs inst.inst_outputs vals
             (update_var x w (merge_callee_state st callee_s')) =
           OPTION_MAP (update_var x w)
             (bind_outputs inst.inst_outputs vals
                (merge_callee_state st callee_s'))`
            by (irule bind_outputs_update_var >> gvs[]) >>
          Cases_on `bind_outputs inst.inst_outputs vals
                      (merge_callee_state st callee_s')` >> gvs[])
      >> gvs[bind_outputs_def])
  (* Non-INVOKE: step_inst = step_inst_base *)
  >> (drule_all step_inst_base_var_frame_full >>
      simp[step_inst_non_invoke])
QED

val _ = export_theory();
