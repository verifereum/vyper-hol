(* Shared instruction boundaries for changes of control coordinates. *)
Theory simplifyCfgControlExec
Ancestors
  simplifyCfgControl simplifyCfgControlState instIdxIndep venomExecSemantics venomState list
Libs
  BasicProvers

Theorem scfg_ctrl_operand[simp]:
  eval_operand op (scfg_ctrl c p n s) = eval_operand op s
Proof
  metis_tac[scfg_payload_ctrl, scfg_payload_operand]
QED

Theorem scfg_ctrl_operands[simp]:
  eval_operands ops (scfg_ctrl c p n s) = eval_operands ops s
Proof
  metis_tac[scfg_payload_ctrl, scfg_payload_operands]
QED

Theorem scfg_ctrl_exec_pure1:
  exec_pure1 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_pure1 f i s)
Proof
  simp[exec_pure1_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_pure2:
  exec_pure2 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_pure2 f i s)
Proof
  simp[exec_pure2_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_pure3:
  exec_pure3 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_pure3 f i s)
Proof
  simp[exec_pure3_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_read0:
  (!s. f (scfg_ctrl c p n s) = f s) ==>
  exec_read0 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_read0 f i s)
Proof
  strip_tac >> simp[exec_read0_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_read1:
  (!v s. f v (scfg_ctrl c p n s) = f v s) ==>
  exec_read1 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_read1 f i s)
Proof
  strip_tac >> simp[exec_read1_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_write2:
  (!v w s. f v w (scfg_ctrl c p n s) = scfg_ctrl c p n (f v w s)) ==>
  exec_write2 f i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_write2 f i s)
Proof
  strip_tac >> simp[exec_write2_def] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_exec_gas:
  exec_gas i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (exec_gas i s)
Proof
  simp[exec_gas_def] >>
  rpt (TOP_CASE_TAC >> gvs[exec_result_map_def, update_var_def, scfg_ctrl_def])
QED

Definition scfg_result_def:
  scfg_result (OK s) (OK t) = scfg_payload s t /\
  scfg_result (Halt s) (Halt t) = scfg_payload s t /\
  scfg_result (Abort a s) (Abort b t) = (a = b /\ scfg_payload s t) /\
  scfg_result (IntRet a s) (IntRet b t) = (a = b /\ scfg_payload s t) /\
  scfg_result (Error e) (Error e') = (e = e') /\
  scfg_result _ _ = F
End

Theorem scfg_result_refl[simp]:
  scfg_result r r
Proof
  Cases_on `r` >> simp[scfg_result_def]
QED

Theorem scfg_ctrl_setup_callee[simp]:
  setup_callee fn args (scfg_ctrl c p n s) = setup_callee fn args s
Proof
  simp[setup_callee_def, scfg_ctrl_def]
QED

Theorem scfg_ctrl_merge_callee[simp]:
  merge_callee_state (scfg_ctrl c p n s) t =
  scfg_ctrl c p n (merge_callee_state s t)
Proof
  simp[merge_callee_state_def, scfg_ctrl_def]
QED

Theorem scfg_ctrl_adopt_return[simp]:
  adopt_return_fmp r (scfg_ctrl c p n s) =
  scfg_ctrl c p n (adopt_return_fmp r s)
Proof
  Cases_on `r.iret_adopt_fmp` >> simp[adopt_return_fmp_def, scfg_ctrl_def]
QED

Theorem scfg_ctrl_fold_update:
  !xs s. FOLDL (\s (x,v). update_var x v s) (scfg_ctrl c p n s) xs =
    scfg_ctrl c p n (FOLDL (\s (x,v). update_var x v s) s xs)
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

Theorem scfg_ctrl_bind_outputs[simp]:
  bind_outputs outs vals (scfg_ctrl c p n s) =
  OPTION_MAP (scfg_ctrl c p n) (bind_outputs outs vals s)
Proof
  Cases_on `LENGTH outs = LENGTH vals` >>
  simp[bind_outputs_def, scfg_ctrl_fold_update]
QED

Theorem scfg_ctrl_invoke_result:
  i.inst_opcode = INVOKE ==>
  scfg_result (step_inst k C i s) (step_inst k C i (scfg_ctrl c p n s))
Proof
  strip_tac >> simp[cj 1 run_defs] >>
  rpt (TOP_CASE_TAC >>
    asm_simp_tac (srw_ss())
      [scfg_result_def, scfg_ctrl_setup_callee, scfg_ctrl_operands,
       scfg_ctrl_merge_callee, scfg_ctrl_adopt_return,
       scfg_ctrl_bind_outputs, scfg_payload_ctrl])
QED

Theorem scfg_ctrl_invoke_OK:
  i.inst_opcode = INVOKE /\ step_inst k C i s = OK u ==>
  step_inst k C i (scfg_ctrl c p n s) = OK (scfg_ctrl c p n u)
Proof
  strip_tac >>
  gvs[cj 1 run_defs, AllCaseEqs()] >>
  simp[AllCaseEqs()] >>
  metis_tac[optionTheory.OPTION_MAP_DEF]
QED

Theorem scfg_ctrl_jump:
  jump_to l (scfg_ctrl c p n s) =
  scfg_ctrl l (SOME c) 0 s
Proof
  simp[jump_to_def, scfg_ctrl_def]
QED

Theorem scfg_payload_jump:
  scfg_payload s t ==> scfg_payload (jump_to l s) (jump_to l t)
Proof
  pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  simp[jump_to_def, scfg_ctrl_def]
QED


Theorem scfg_ctrl_jump_result:
  jump_to l (scfg_ctrl c p n s) =
  scfg_ctrl (jump_to l s).vs_current_bb (SOME c) 0 (jump_to l s)
Proof
  simp[jump_to_def, scfg_ctrl_def]
QED

Theorem scfg_ctrl_branch:
  MEM i.inst_opcode [JMP; JNZ; DJMP] ==>
  step_inst k C i (scfg_ctrl c p n s) =
  exec_result_map
    (\u. scfg_ctrl u.vs_current_bb (SOME c) 0 (scfg_ctrl c p n u))
    (step_inst k C i s)
Proof
  simp[] >> strip_tac >>
  asm_simp_tac (srw_ss()) [cj 1 run_defs] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  rpt (PURE_TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [LET_THM, list_case_def, pairTheory.pair_case_thm, optionTheory.option_case_def,
       operand_case_def, exec_result_map_def, scfg_ctrl_operand,
       scfg_ctrl_jump_result])
QED

Theorem scfg_ctrl_call_request[simp]:
  venom_call_request (scfg_ctrl c p n s) addr value ao az static =
  venom_call_request s addr value ao az static
Proof
  simp[venomCallOracleDefsTheory.venom_call_request_def, scfg_ctrl_def,
       read_memory_def]
QED

Theorem scfg_ctrl_consume_outcome:
  consume_call_outcome rq ro rs s = (w,t) ==>
  consume_call_outcome rq ro rs (scfg_ctrl c p n s) =
    (w,scfg_ctrl c p n t)
Proof
  simp[venomCallOracleDefsTheory.consume_call_outcome_eq,
       scfg_ctrl_def, write_memory_with_expansion_def] >>
  strip_tac >> gvs[]
QED

Theorem scfg_ctrl_tx_params[simp]:
  venom_to_tx_params (scfg_ctrl c p n s) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def, scfg_ctrl_def]
QED

Theorem scfg_ctrl_delegate_state[simp]:
  make_venom_delegatecall_state (scfg_ctrl c p n s) a gas data code static =
  make_venom_delegatecall_state s a gas data code static
Proof
  simp[make_venom_delegatecall_state_def, scfg_ctrl_tx_params, scfg_ctrl_def,
       venom_to_tx_params_def]
QED

Theorem scfg_ctrl_create_state[simp]:
  make_venom_create_state (scfg_ctrl c p n s) a gas v code =
  make_venom_create_state s a gas v code
Proof
  simp[make_venom_create_state_def, scfg_ctrl_tx_params, scfg_ctrl_def,
       venom_to_tx_params_def]
QED

Theorem scfg_ctrl_extract_result:
  extract_venom_result (scfg_ctrl c p n s) out ro rs r =
  OPTION_MAP (\q. (FST q, scfg_ctrl c p n (SND q)))
    (extract_venom_result s out ro rs r)
Proof
  simp[extract_venom_result_def] >>
  rpt (PURE_TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [LET_THM, list_case_def, pairTheory.pair_case_thm,
       pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND,
       optionTheory.option_case_def, optionTheory.OPTION_MAP_DEF,
       sumTheory.sum_case_def, scfg_ctrl_def,
       write_memory_with_expansion_def, venom_state_accfupds,
       venom_state_fupdcanon, venom_state_fupdfupds, combinTheory.K_THM])
QED

Theorem scfg_ctrl_ext_call:
  exec_ext_call i (scfg_ctrl c p n s) gas addr v ao az ro rz static =
  exec_result_map (scfg_ctrl c p n)
    (exec_ext_call i s gas addr v ao az ro rz static)
Proof
  Cases_on `consume_call_outcome
    (venom_call_request s addr v ao az static) (w2n ro) (w2n rz) s` >>
  drule scfg_ctrl_consume_outcome >> strip_tac >>
  simp[exec_ext_call_def, scfg_ctrl_call_request] >>
  rpt (PURE_TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [list_case_def, exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_call_fields[local,simp]:
  (scfg_ctrl c p n s).vs_accounts = s.vs_accounts /\
  (scfg_ctrl c p n s).vs_call_ctx = s.vs_call_ctx
Proof
  simp[scfg_ctrl_def]
QED

Theorem scfg_ctrl_delegatecall:
  exec_delegatecall i (scfg_ctrl c p n s) gas addr ao az ro rz =
  exec_result_map (scfg_ctrl c p n)
    (exec_delegatecall i s gas addr ao az ro rz)
Proof
  Cases_on `consume_call_outcome
    (venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall)
    (w2n ro) (w2n rz) s` >>
  drule scfg_ctrl_consume_outcome >> strip_tac >>
  simp[exec_delegatecall_def, scfg_ctrl_call_request] >>
  rpt (PURE_TOP_CASE_TAC >>
    asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
      [list_case_def, exec_result_map_def, scfg_ctrl_update_var])
QED

Theorem scfg_ctrl_create_request[simp]:
  venom_create_request (scfg_ctrl c p n s) v off sz salt =
  venom_create_request s v off sz salt
Proof
  simp[venomCallOracleDefsTheory.venom_create_request_def, scfg_ctrl_def,
       read_memory_def]
QED

Theorem scfg_ctrl_consume_create:
  consume_create_outcome rq (scfg_ctrl c p n s) =
  (FST (consume_create_outcome rq s),
   scfg_ctrl c p n (SND (consume_create_outcome rq s)))
Proof
  simp[venomCallOracleDefsTheory.consume_create_outcome_eq, scfg_ctrl_def,
       venom_state_component_equality]
QED

Theorem scfg_ctrl_create:
  exec_create i (scfg_ctrl c p n s) v off sz salt =
  exec_result_map (scfg_ctrl c p n) (exec_create i s v off sz salt)
Proof
  simp[exec_create_def, scfg_ctrl_create_request,
       Excl "consume_create_outcome_eq", scfg_ctrl_consume_create] >>
  Cases_on `consume_create_outcome (venom_create_request s v off sz salt) s` >>
  simp[] >> Cases_on `i.inst_outputs` >> simp[exec_result_map_def] >>
  rename1 `i.inst_outputs = out :: rest` >> Cases_on `rest` >>
  simp[exec_result_map_def, scfg_ctrl_update_var] >>
  rw[exec_result_map_def]
QED

(* Select only the equation guarded by the live opcode assumption. *)
val ctrl_opcode_eqs = map (fn th =>
  (rhs (#1 (dest_imp (#2 (strip_forall (concl th))))), th))
  (CONJUNCTS step_inst_base_opcode_eqs);

fun ctrl_opcode_rewrite eq =
  PURE_ONCE_REWRITE_TAC [MATCH_MP
    (#2 (valOf (List.find (fn (key, _) => aconv key (rhs (concl eq)))
      ctrl_opcode_eqs))) eq];

Theorem scfg_ctrl_raw_fields[local]:
  (scfg_ctrl c p n s).vs_fmp = s.vs_fmp /\
  (scfg_ctrl c p n s).vs_call_entry_fmp = s.vs_call_entry_fmp /\
  ((scfg_ctrl c p n s) with vs_fmp := v) =
    scfg_ctrl c p n (s with vs_fmp := v) /\
  ((scfg_ctrl c p n s) with vs_accounts := accts) =
    scfg_ctrl c p n (s with vs_accounts := accts) /\
  ((scfg_ctrl c p n s) with vs_returndata := data) =
    scfg_ctrl c p n (s with vs_returndata := data)
Proof
  simp[scfg_ctrl_def]
QED

Theorem scfg_ctrl_pack_dret_eq[local]:
  pack_dret_dynamic cursor pairs (scfg_ctrl c p n s) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     scfg_ctrl c p n (SND (SND (pack_dret_dynamic cursor pairs s))))
Proof
  Cases_on `pack_dret_dynamic cursor pairs s` >>
  rename1 `pack_dret_dynamic cursor pairs s = (ptrs, rest)` >>
  Cases_on `rest` >> drule scfg_ctrl_pack_dret >> simp[]
QED

val ctrl_opcode_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [LET_THM, list_case_def, pairTheory.pair_case_thm, pairTheory.UNCURRY,
   pairTheory.FST, pairTheory.SND, optionTheory.option_case_def,
   operand_case_def, exec_result_map_def, scfg_ctrl_operand, scfg_ctrl_operands,
   scfg_ctrl_update_var, scfg_ctrl_exec_pure1, scfg_ctrl_exec_pure2,
   scfg_ctrl_exec_pure3, scfg_ctrl_alloca, scfg_ctrl_ext_call,
   scfg_ctrl_delegatecall, scfg_ctrl_create, scfg_ctrl_mcopy,
   scfg_ctrl_istore, scfg_ctrl_write_memory, scfg_ctrl_halt,
   scfg_ctrl_revert, scfg_ctrl_set_returndata, scfg_ctrl_pack_dret_eq,
   scfg_ctrl_raw_fields, scfg_ctrl_call_fields];

val ctrl_envelope_tac =
  asm_simp_tac ctrl_opcode_ss [] >>
  rpt (PURE_TOP_CASE_TAC >> asm_simp_tac ctrl_opcode_ss []) >>
  gvs[scfg_ctrl_def, halt_state_def, set_returndata_def];

Theorem scfg_ctrl_nonbranch:
  ~MEM i.inst_opcode [JMP; JNZ; DJMP; INVOKE] ==>
  step_inst k C i (scfg_ctrl c p n s) =
  exec_result_map (scfg_ctrl c p n) (step_inst k C i s)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE` by gvs[] >>
  simp[cj 1 run_defs] >>
  Cases_on `i.inst_opcode` >> gvs[] >>
  qpat_assum `i.inst_opcode = _` ctrl_opcode_rewrite >>
  FIRST [
    (irule scfg_ctrl_exec_read0 >> simp[] >> simp[scfg_ctrl_def] >> NO_TAC),
    (irule scfg_ctrl_exec_read1 >> simp[] >> simp[scfg_ctrl_def] >> NO_TAC),
    (irule scfg_ctrl_exec_write2 >> simp[] >> NO_TAC),
    (MATCH_ACCEPT_TAC scfg_ctrl_exec_gas),
    ctrl_envelope_tac >>
    irule (SRULE [scfg_ctrl_def] scfg_ctrl_exec_write2) >>
    simp[sstore_def, tstore_def]]
QED

Theorem scfg_result_map_payload:
  (!u. scfg_payload u (f u)) ==>
  scfg_result r (exec_result_map f r)
Proof
  strip_tac >> Cases_on `r` >> simp[exec_result_map_def, scfg_result_def]
QED

Theorem scfg_ctrl_step_result:
  scfg_result (step_inst k C i s) (step_inst k C i (scfg_ctrl c p n s))
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (irule scfg_ctrl_invoke_result >> simp[]) >>
  Cases_on `MEM i.inst_opcode [JMP; JNZ; DJMP]`
  >- (drule scfg_ctrl_branch >> disch_then (fn th => rewrite_tac[th]) >>
      irule scfg_result_map_payload >> simp[]) >>
  `~MEM i.inst_opcode [JMP; JNZ; DJMP; INVOKE]` by gvs[] >>
  drule scfg_ctrl_nonbranch >> disch_then (fn th => rewrite_tac[th]) >>
  irule scfg_result_map_payload >> simp[]
QED

Theorem scfg_payload_step:
  scfg_payload s t ==>
  scfg_result (step_inst k C i s) (step_inst k C i t)
Proof
  pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  irule scfg_ctrl_step_result
QED

Theorem scfg_ctrl_step_OK:
  ~MEM i.inst_opcode [JMP; JNZ; DJMP] /\ step_inst k C i s = OK u ==>
  step_inst k C i (scfg_ctrl c p n s) = OK (scfg_ctrl c p n u)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (irule scfg_ctrl_invoke_OK >> simp[]) >>
  `~MEM i.inst_opcode [JMP; JNZ; DJMP; INVOKE]` by gvs[] >>
  drule scfg_ctrl_nonbranch >> simp[exec_result_map_def]
QED
