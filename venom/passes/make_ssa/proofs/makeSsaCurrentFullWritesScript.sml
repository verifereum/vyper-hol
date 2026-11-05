Theory makeSsaCurrentFullWrites
Ancestors makeSsaCurrentPairedWrites makeSsaCurrentOrdinary makeSsaCurrentDefs
  venomWf venomExecSemantics venomState stateFrame list rich_list pair

(* Only successful base steps require full declared-output enumeration. *)
Definition current_full_write_result_def:
  current_full_write_result outs outs' st st' result result' <=>
    !after. result = OK after ==> ?after' events.
      result' = OK after' /\
      current_indexed_writes outs events st after /\
      current_indexed_writes outs' events st' after' /\
      MAP FST events = GENLIST I (LENGTH outs)
End

Theorem current_full_write_error[simp]:
  current_full_write_result outs outs' st st' (Error e) result'
Proof
  simp[current_full_write_result_def]
QED

Theorem current_full_write_single:
  LENGTH outs = LENGTH outs' ==>
  current_full_write_result outs outs' st st'
    (case outs of [x] => OK (update_var x w st) | _ => Error e)
    (case outs' of [y] => OK (update_var y w st') | _ => Error e)
Proof
  strip_tac >> Cases_on `outs` >> Cases_on `outs'` >> gvs[current_full_write_result_def] >>
  rename1 `LENGTH xs = LENGTH ys` >>
  Cases_on `xs` >> Cases_on `ys` >> gvs[] >>
  qexists_tac `[(0,w)]` >> simp[current_indexed_writes_def, update_var_def, GENLIST]
QED

Theorem current_full_write_update:
  current_full_write_result [x] [y] st st'
    (OK (update_var x value st)) (OK (update_var y value st'))
Proof
  simp[current_full_write_result_def] >> qexists_tac `[(0,value)]` >>
  simp[current_indexed_writes_def, update_var_def, GENLIST]
QED

Theorem current_full_exec_read0:
  f st = f st' /\ LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_read0 f inst st) (exec_read0 f inst' st')
Proof
  strip_tac >> simp[exec_read0_def] >> irule current_full_write_single >> simp[]
QED

Theorem current_full_exec_pure1:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_pure1 f inst st) (exec_pure1 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_pure1_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_pure1_def] >>
  rename1 `eval_operand op st = eval_operand op' st'` >>
  Cases_on `eval_operand op' st'` >> gvs[] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_exec_pure2:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_pure2 f inst st) (exec_pure2 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_pure2_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_pure2_def] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[exec_pure2_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  irule current_full_write_update
QED

Theorem current_full_exec_pure3:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_pure3 f inst st) (exec_pure3 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_pure3_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_pure3_def] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[exec_pure3_def] >>
  rename1 `LIST_REL _ last last'` >>
  Cases_on `last` >> Cases_on `last'` >> gvs[exec_pure3_def] >>
  rename1 `inst'.inst_operands = [a;b;c]` >>
  Cases_on `eval_operand a st'` >> gvs[] >>
  Cases_on `eval_operand b st'` >> gvs[] >>
  Cases_on `eval_operand c st'` >> gvs[] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_exec_read1:
  (!w. f w st = f w st') /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_read1 f inst st) (exec_read1 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_read1_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_read1_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  irule current_full_write_update
QED

Theorem current_full_write_two:
  current_full_write_result [x;y] [x';y'] st st'
    (OK (update_var y b (update_var x a st)))
    (OK (update_var y' b (update_var x' a st')))
Proof
  simp[current_full_write_result_def] >> qexists_tac `[(0,a);(1,b)]` >>
  simp[current_indexed_writes_def, update_var_def, GENLIST]
QED

Theorem current_full_bump:
  inst.inst_opcode = BUMP /\ inst'.inst_opcode = BUMP /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[step_inst_base_opcode_eqs] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[step_inst_base_opcode_eqs] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[step_inst_base_opcode_eqs] >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH tail = LENGTH tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[] >>
  rename1 `LENGTH rest = LENGTH rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[] >>
  rename1 `inst'.inst_operands = [a;b]` >>
  Cases_on `eval_operand a st'` >> gvs[] >>
  Cases_on `eval_operand b st'` >> gvs[] >>
  irule current_full_write_two
QED

Theorem current_full_write_zero:
  after.vs_vars = st.vs_vars /\ after'.vs_vars = st'.vs_vars ==>
  current_full_write_result [] [] st st' (OK after) (OK after')
Proof
  simp[current_full_write_result_def] >> strip_tac >> qexists_tac `[]` >> simp[]
QED

Theorem current_full_write_result_no_ok:
  (!after. result <> OK after) ==>
  current_full_write_result outs outs' st st' result result'
Proof
  simp[current_full_write_result_def]
QED

Theorem current_full_write_result_rebase:
  current_full_write_result outs outs' middle middle' result result' /\
  middle.vs_vars = before.vs_vars /\ middle'.vs_vars = before'.vs_vars ==>
  current_full_write_result outs outs' before before' result result'
Proof
  simp[current_full_write_result_def, current_indexed_writes_def] >> metis_tac[]
QED

Theorem current_full_write_non_ok[simp]:
  current_full_write_result outs outs' st st' (Halt after) result' /\
  current_full_write_result outs outs' st st' (Abort reason after) result' /\
  current_full_write_result outs outs' st st' (IntRet ret after) result'
Proof
  simp[current_full_write_result_def]
QED

Theorem current_full_write_empty_paired:
  current_paired_result_writes [] [] st st' result result' ==>
  current_full_write_result [] [] st st' result result'
Proof
  simp[current_full_write_result_def] >> rpt strip_tac >>
  Cases_on `result'` >>
  gvs[current_paired_result_writes_def, current_paired_after_def, current_indexed_writes_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem current_full_assign:
  inst.inst_opcode = ASSIGN /\ inst'.inst_opcode = ASSIGN /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[step_inst_base_opcode_eqs] >> rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[step_inst_base_opcode_eqs] >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH tail = LENGTH tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[] >>
  rename1 `inst'.inst_operands = [a]` >>
  Cases_on `eval_operand a st'` >> gvs[] >>
  irule current_full_write_update
QED

Theorem current_full_special_read0:
  (inst.inst_opcode = GETFMP \/ inst.inst_opcode = INITIAL_FMP) /\
  inst'.inst_opcode = inst.inst_opcode /\
  LENGTH inst.inst_operands = LENGTH inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_fmp = st'.vs_fmp /\ st.vs_initial_fmp = st'.vs_initial_fmp`
    by (conj_tac >> qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. (s.vs_fmp,s.vs_initial_fmp)``) >>
      simp[execution_frame_def]) >>
  Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[step_inst_base_opcode_eqs] >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH tail = LENGTH tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[] >>
  irule current_full_write_update
QED

Theorem current_full_exec_alloca:
  inst'.inst_id = inst.inst_id /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_alloca inst st sz) (exec_alloca inst' st' sz)
Proof
  strip_tac >>
  `st.vs_allocas = st'.vs_allocas /\ st.vs_alloca_next = st'.vs_alloca_next`
    by (conj_tac >> qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. (s.vs_allocas,s.vs_alloca_next)``) >>
      simp[execution_frame_def]) >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[exec_alloca_def] >>
  rename1 `LENGTH tail = LENGTH tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_alloca_def] >>
  Cases_on `FLOOKUP st'.vs_allocas inst.inst_id`
  >- (simp[current_full_write_result_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `[(0,n2w st'.vs_alloca_next)]` >>
      simp[current_indexed_writes_def, update_var_def, GENLIST]) >>
  PairCases_on `x` >> simp[] >> irule current_full_write_update
QED

Theorem current_full_exec_ext_call:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_ext_call inst st gas addr value ao az ro rz static)
    (exec_ext_call inst' st' gas addr value ao az ro rz static)
Proof
  strip_tac >>
  `venom_call_request st addr value ao az static =
   venom_call_request st' addr value ao az static`
    by metis_tac[venomCallOraclePropsTheory.venom_call_request_frame] >>
  qabbrev_tac `rq = venom_call_request st addr value ao az static` >>
  `FST (consume_call_outcome rq (w2n ro) (w2n rz) st) =
   FST (consume_call_outcome rq (w2n ro) (w2n rz) st')`
    by metis_tac[venomCallOraclePropsTheory.consume_call_outcome_frame, PAIR_EQ] >>
  simp[Abbr `rq`, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  rename1 `consume_call_outcome _ _ _ st' = (ret,after')` >>
  rename1 `consume_call_outcome _ _ _ st = (ret,after)` >>
  irule current_full_write_result_rebase >> qexistsl_tac [`after`,`after'`] >>
  conj_tac >- gvs[venomCallOracleDefsTheory.consume_call_outcome_eq] >>
  conj_tac >- gvs[venomCallOracleDefsTheory.consume_call_outcome_eq] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_exec_delegatecall:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_delegatecall inst st gas addr ao az ro rz)
    (exec_delegatecall inst' st' gas addr ao az ro rz)
Proof
  strip_tac >> drule current_concrete_call_inputs_agree >> strip_tac >>
  asm_simp_tac (srw_ss()) [exec_delegatecall_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result st 1w _ _ result` >>
  `extract_venom_result st 1w (w2n ro) (w2n rz) result = NONE <=>
   extract_venom_result st' 1w (w2n ro) (w2n rz) result = NONE`
    by metis_tac[current_extract_result_agree] >>
  Cases_on `extract_venom_result st 1w (w2n ro) (w2n rz) result`
  >- gvs[] >>
  PairCases_on `x` >>
  drule_all (cj 2 current_extract_result_agree) >> strip_tac >> simp[] >>
  rename1 `execution_frame x1 = execution_frame after'` >>
  irule current_full_write_result_rebase >> qexistsl_tac [`x1`,`after'`] >> simp[] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_exec_create:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (exec_create inst st value off sz salt) (exec_create inst' st' value off sz salt)
Proof
  strip_tac >> drule current_create_request_agree >> strip_tac >>
  Cases_on `w2n sz > 2 * max_code_size`
  >- (Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >>
      gvs[exec_create_def] >> rename1 `LENGTH xs = LENGTH ys` >>
      Cases_on `xs` >> Cases_on `ys` >> gvs[exec_create_def]) >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st` >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st'` >>
  drule_all current_consume_create_agree >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  rename1 `execution_frame after = execution_frame after'` >>
  irule current_full_write_result_rebase >> qexistsl_tac [`after`,`after'`] >> simp[] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_param:
  (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/
   inst.inst_opcode = RETPC_PARAM) /\
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_params = st'.vs_params /\ st.vs_return_pc_token = st'.vs_return_pc_token`
    by (conj_tac >> qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. (s.vs_params,s.vs_return_pc_token)``) >>
      simp[execution_frame_def]) >>
  Cases_on `inst.inst_operands` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = op::tail` >>
  Cases_on `tail` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  Cases_on `op` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH xs = LENGTH ys` >>
  Cases_on `xs` >> Cases_on `ys` >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  irule current_full_write_update
QED

Theorem current_full_dalloca:
  inst.inst_opcode = DALLOCA /\ inst'.inst_opcode = DALLOCA /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_fmp = st'.vs_fmp` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >> simp[execution_frame_def]) >>
  Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[step_inst_base_opcode_eqs] >> rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[step_inst_base_opcode_eqs] >>
  Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH tail = LENGTH tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[] >>
  rename1 `inst'.inst_operands = [a]` >>
  Cases_on `eval_operand a st'` >> gvs[] >>
  simp[current_full_write_result_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `[(0,st'.vs_fmp)]` >>
  simp[current_indexed_writes_def, update_var_def, GENLIST]
QED

Theorem current_full_sha3:
  inst.inst_opcode = SHA3 /\ inst'.inst_opcode = SHA3 /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_memory = st'.vs_memory` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >> simp[execution_frame_def]) >>
  Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[step_inst_base_opcode_eqs] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[step_inst_base_opcode_eqs] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[step_inst_base_opcode_eqs] >>
  rename1 `inst'.inst_operands = [a;b]` >>
  Cases_on `eval_operand a st'` >> gvs[] >>
  Cases_on `eval_operand b st'` >> gvs[] >>
  irule current_full_write_single >> simp[]
QED

Theorem current_full_create:
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >>
  asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       pure_asm_rewrite_tac[optionTheory.option_case_def, current_full_write_error]) >>
  qpat_assum `inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `inst'.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule current_full_exec_create >> simp[]
QED

Theorem current_full_external_call:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_call_ctx = st'.vs_call_ctx`
    by (qpat_x_assum `execution_frame _ = _`
          (mp_tac o AP_TERM ``\s:venom_state. s.vs_call_ctx``) >>
        simp[execution_frame_def]) >>
  drule_all current_rename_operands_pointwise >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >>
  rpt (qpat_x_assum `eval_operand _ st = eval_operand _ st'` (assume_tac o SYM)) >>
  asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  qpat_x_assum `inst'.inst_operands = _` kall_tac >>
  rpt (qpat_x_assum `eval_operand _ st' = _` kall_tac) >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       pure_asm_rewrite_tac[optionTheory.option_case_def, current_full_write_error]) >>
  qpat_assum `inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `inst'.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  FIRST [irule current_full_exec_ext_call, irule current_full_exec_delegatecall] >> simp[]
QED

(* Full events are constructed at the semantic-family boundary. Frame/control
   agreement is deliberately reused from current_step_inst_base_paired. *)
val current_full_dispatch : tactic =
  (fn g as (asms,_) =>
    let
      val eq = valOf (List.find (fn t => is_eq t andalso
        is_const (rhs t) andalso type_of (rhs t) = ``:opcode``) asms)
      val opc = fst (dest_const (rhs eq))
      val pure2 = ["ADD","SUB","MUL","Div","Mod","SDIV","SMOD","Exp",
                   "EQ","LT","GT","SLT","SGT","AND","OR","XOR",
                   "SHL","SHR","SAR","SIGNEXTEND","BYTE","OFFSET"]
      fun pure th = simp[step_inst_base_opcode_eqs] >> irule th >> simp[]
      fun direct th = irule th >> simp[] >> rpt conj_tac >>
        (fn g => (if is_exists (snd g) then
           qexists_tac `rs` >> simp[] >> gvs[inst_wf_def]
         else gvs[inst_wf_def, current_rename_operands_map]) g)
      val tac =
        if mem opc pure2 then pure current_full_exec_pure2
        else if mem opc ["ADDMOD","MULMOD"] then pure current_full_exec_pure3
        else if mem opc ["ISZERO","NOT"] then pure current_full_exec_pure1
        else if mem opc ["MLOAD","SLOAD","TLOAD","DLOAD","ILOAD","BLOCKHASH","BLOBHASH","BALANCE","CALLDATALOAD","EXTCODESIZE","EXTCODEHASH"] then
          simp[step_inst_base_opcode_eqs] >> irule current_full_exec_read1 >>
          simp[] >> qpat_x_assum `execution_frame _ = _` mp_tac >>
          simp[execution_frame_def, venom_state_component_equality,
               mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
        else if mem opc ["ADDRESS","CALLER","CALLVALUE","GAS","ORIGIN","GASPRICE","CHAINID","COINBASE","TIMESTAMP","NUMBER","PREVRANDAO","GASLIMIT","BASEFEE","BLOBBASEFEE","SELFBALANCE","CALLDATASIZE","RETURNDATASIZE","MEMTOP","CODESIZE"] then
          simp[step_inst_base_opcode_eqs] >> irule current_full_exec_read0 >>
          simp[] >> qpat_x_assum `execution_frame _ = _` mp_tac >>
          simp[execution_frame_def, venom_state_component_equality]
        else if opc = "ASSIGN" then direct current_full_assign
        else if opc = "DALLOCA" then direct current_full_dalloca
        else if opc = "BUMP" then direct current_full_bump
        else if mem opc ["GETFMP","INITIAL_FMP"] then direct current_full_special_read0
        else if mem opc ["CREATE","CREATE2"] then direct current_full_create
        else if mem opc ["CALL","STATICCALL","DELEGATECALL"] then direct current_full_external_call
        else if opc = "SHA3" then direct current_full_sha3
        else if mem opc ["PARAM","FMP_PARAM","RETPC_PARAM"] then direct current_full_param
        else if opc = "ALLOCA" then
          fs[inst_wf_def] >>
          simp[step_inst_base_opcode_eqs, current_rename_operands_map] >>
          irule current_full_exec_alloca >> simp[]
        else if opc = "INVOKE" then simp[step_inst_base_opcode_eqs]
        else gvs[inst_wf_def]
    in tac g end)

Theorem current_full_family_pure[local]:
  MEM inst.inst_opcode [ADD;SUB;MUL;Div;Mod;SDIV;SMOD;Exp;EQ;LT;GT;SLT;SGT;
    AND;OR;XOR;SHL;SHR;SAR;SIGNEXTEND;BYTE;OFFSET;ADDMOD;MULMOD;ISZERO;NOT] /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_full_dispatch
QED

Theorem current_full_family_read1[local]:
  MEM inst.inst_opcode [MLOAD;SLOAD;TLOAD;DLOAD;ILOAD;BLOCKHASH;BLOBHASH;
    BALANCE;CALLDATALOAD;EXTCODESIZE;EXTCODEHASH] /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_full_dispatch
QED

Theorem current_full_family_read0[local]:
  MEM inst.inst_opcode [ADDRESS;CALLER;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;
    COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
    SELFBALANCE;CALLDATASIZE;RETURNDATASIZE;MEMTOP;CODESIZE] /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_full_dispatch
QED

Theorem current_full_family_special[local]:
  MEM inst.inst_opcode [ASSIGN;DALLOCA;BUMP;GETFMP;INITIAL_FMP;CREATE;
    CREATE2;CALL;STATICCALL;DELEGATECALL;SHA3;PARAM;FMP_PARAM;RETPC_PARAM;ALLOCA] /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_full_dispatch
QED

Theorem current_step_inst_base_full_result:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_full_write_result inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_outputs = []`
  >- (`inst'.inst_outputs = []` by (Cases_on `inst'.inst_outputs` >> gvs[]) >>
      simp[] >> irule current_full_write_empty_paired >>
      drule_all current_step_inst_base_paired >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  FIRST [
    (irule current_full_family_pure >> simp[] >> qexists_tac `rs` >> simp[]),
    (irule current_full_family_read1 >> simp[] >> qexists_tac `rs` >> simp[]),
    (irule current_full_family_read0 >> simp[] >> qexists_tac `rs` >> simp[]),
    (irule current_full_family_special >> simp[] >> qexists_tac `rs` >> simp[]),
    (gvs[inst_wf_def] >> simp[step_inst_base_opcode_eqs])]
QED

Theorem current_step_inst_base_full_writes:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  step_inst_base inst st = OK after ==>
  ?after' events.
    step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb
Proof
  strip_tac >> drule_all current_step_inst_base_full_result >>
  simp[current_full_write_result_def] >> strip_tac >>
  drule_all current_step_inst_base_paired >>
  simp[current_paired_result_writes_def, current_paired_after_def] >> strip_tac >>
  qexists_tac `events` >> simp[]
QED
