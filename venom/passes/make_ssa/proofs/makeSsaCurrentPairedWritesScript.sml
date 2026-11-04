Theory makeSsaCurrentPairedWrites
Ancestors
  makeSsaCurrentWriteFootprint makeSsaCurrentOrdinary makeSsaCurrentDefs venomExecSemantics
  venomState stateFrame finite_map list rich_list pair
  venomCallOracleProps venomCallOracleDefs venomWf makeSsaCurrentSimDefs

Definition current_indexed_writes_def:
  current_indexed_writes outs events before after <=>
    EVERY (\kv. FST kv < LENGTH outs) events /\
    after.vs_vars = FOLDL (\m kv. m |+ (EL (FST kv) outs,SND kv)) before.vs_vars events
End

Definition current_paired_after_def:
  current_paired_after outs outs' before before' after after' <=>
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\
    after.vs_prev_bb = after'.vs_prev_bb /\
    ?events. current_indexed_writes outs events before after /\
      current_indexed_writes outs' events before' after'
End

Definition current_paired_result_writes_def:
  current_paired_result_writes outs outs' before before' result result' <=>
    case (result,result') of
      (OK after,OK after') => current_paired_after outs outs' before before' after after'
    | (Halt after,Halt after') => current_paired_after outs outs' before before' after after'
    | (Abort reason after,Abort reason' after') => reason = reason' /\
        current_paired_after outs outs' before before' after after'
    | (IntRet ret after,IntRet ret' after') => ret = ret' /\
        current_paired_after outs outs' before before' after after'
    | (Error msg,Error msg') => msg = msg'
    | _ => F
End

Theorem current_paired_result_constructors[simp]:
  (current_paired_result_writes outs outs' st st' (OK a) (OK b) <=>
    current_paired_after outs outs' st st' a b) /\
  (current_paired_result_writes outs outs' st st' (Halt a) (Halt b) <=>
    current_paired_after outs outs' st st' a b) /\
  (current_paired_result_writes outs outs' st st' (Abort r a) (Abort r' b) <=>
    r = r' /\ current_paired_after outs outs' st st' a b) /\
  (current_paired_result_writes outs outs' st st' (IntRet ret a) (IntRet ret' b) <=>
    ret = ret' /\ current_paired_after outs outs' st st' a b) /\
  (current_paired_result_writes outs outs' st st' (Error e) (Error e') <=> e = e')
Proof
  simp[current_paired_result_writes_def]
QED

Theorem current_indexed_writes_nil[simp]:
  current_indexed_writes outs [] before after <=> after.vs_vars = before.vs_vars
Proof
  simp[current_indexed_writes_def]
QED

Theorem current_indexed_writes_append:
  current_indexed_writes outs events before after /\ k < LENGTH outs ==>
  current_indexed_writes outs (events ++ [(k,value)]) before
    (update_var (EL k outs) value after)
Proof
  simp[current_indexed_writes_def, update_var_def, FOLDL_APPEND]
QED

Theorem current_paired_after_unchanged:
  execution_frame after = execution_frame after' /\
  after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb /\
  after.vs_vars = before.vs_vars /\ after'.vs_vars = before'.vs_vars ==>
  current_paired_after outs outs' before before' after after'
Proof
  strip_tac >> simp[current_paired_after_def] >> qexists_tac `[]` >> simp[]
QED

Theorem current_paired_after_update:
  current_paired_after outs outs' before before' after after' /\
  k < LENGTH outs /\ k < LENGTH outs' ==>
  current_paired_after outs outs' before before'
    (update_var (EL k outs) value after) (update_var (EL k outs') value after')
Proof
  simp[current_paired_after_def] >> rpt strip_tac
  >- gvs[execution_frame_def, update_var_def]
  >- gvs[update_var_def] >>
  qexists_tac `events ++ [(k,value)]` >>
  conj_tac >> irule current_indexed_writes_append >> simp[]
QED

Theorem current_paired_after_single:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_after [x] [y] st st' (update_var x w st) (update_var y w st')
Proof
  strip_tac >> simp[current_paired_after_def, update_var_def, execution_frame_def] >>
  qexists_tac `[(0,w)]` >> simp[current_indexed_writes_def, update_var_def]
QED

Theorem current_paired_single_output:
  LENGTH outs = LENGTH outs' /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes outs outs' st st'
    (case outs of [x] => OK (update_var x w st) | _ => Error e)
    (case outs' of [y] => OK (update_var y w st') | _ => Error e)
Proof
  strip_tac >> Cases_on `outs` >> Cases_on `outs'` >> gvs[] >>
  rename1 `LENGTH xs = LENGTH ys` >>
  Cases_on `xs` >> Cases_on `ys` >> gvs[] >>
  simp[current_paired_after_def, update_var_def, execution_frame_def] >>
  qexists_tac `[(0,w)]` >> simp[current_indexed_writes_def, update_var_def]
QED

Theorem current_exec_read0_paired:
  f st = f st' /\ LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_read0 f inst st) (exec_read0 f inst' st')
Proof
  strip_tac >> simp[exec_read0_def] >>
  irule current_paired_single_output >> simp[]
QED

Theorem current_exec_pure1_paired:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_pure1 f inst st) (exec_pure1 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_pure1_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_pure1_def] >>
  rename1 `eval_operand op st = eval_operand op' st'` >>
  Cases_on `eval_operand op' st'` >> gvs[] >>
  irule current_paired_single_output >> simp[]
QED

Theorem current_exec_pure2_paired:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_pure2 f inst st) (exec_pure2 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_pure2_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_pure2_def] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[exec_pure2_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  irule current_paired_after_single >> simp[]
QED

Theorem current_exec_pure3_paired:
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_single_output >> simp[]
QED

Theorem current_exec_read1_paired:
  (!w. f w st = f w st') /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_read1 f inst st) (exec_read1 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_read1_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_read1_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  irule current_paired_after_single >> simp[]
QED

Theorem current_exec_write2_paired:
  (!a b. execution_frame (f a b st) = execution_frame (f a b st') /\
    (f a b st).vs_current_bb = (f a b st').vs_current_bb /\
    (f a b st).vs_prev_bb = (f a b st').vs_prev_bb /\
    (f a b st).vs_vars = st.vs_vars /\ (f a b st').vs_vars = st'.vs_vars) /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_write2 f inst st) (exec_write2 f inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[exec_write2_def] >>
  rename1 `LIST_REL _ tail tail'` >>
  Cases_on `tail` >> Cases_on `tail'` >> gvs[exec_write2_def] >>
  rename1 `LIST_REL _ rest rest'` >>
  Cases_on `rest` >> Cases_on `rest'` >> gvs[exec_write2_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  irule current_paired_after_unchanged >> simp[]
QED

Theorem current_exec_alloca_paired:
  inst'.inst_id = inst.inst_id /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  Cases_on `FLOOKUP st'.vs_allocas inst.inst_id` >> simp[]
  >- (simp[current_paired_after_def, update_var_def, execution_frame_def] >>
      conj_tac
      >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
          simp[execution_frame_def] >> disch_then (mp_tac o AP_TERM
            ``\s:venom_state. s with <|
              vs_allocas := st'.vs_allocas |+ (inst.inst_id,(st'.vs_alloca_next,w2n sz));
              vs_alloca_next := st'.vs_alloca_next + w2n sz|>``) >> simp[]) >>
      qexists_tac `[(0,n2w st'.vs_alloca_next)]` >>
      simp[current_indexed_writes_def, update_var_def]) >>
  PairCases_on `x` >> simp[] >> irule current_paired_after_single >> simp[]
QED

Theorem current_paired_after_two:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_after [x;y] [x';y'] st st'
    (update_var y b (update_var x a st))
    (update_var y' b (update_var x' a st'))
Proof
  strip_tac >> simp[current_paired_after_def, execution_frame_def, update_var_def] >>
  qexists_tac `[(0,a);(1,b)]` >> simp[current_indexed_writes_def, update_var_def]
QED

Theorem current_bump_paired:
  inst.inst_opcode = BUMP /\ inst'.inst_opcode = BUMP /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_after_two >> simp[]
QED

Theorem current_paired_after_rebase:
  current_paired_after outs outs' middle middle' after after' /\
  middle.vs_vars = before.vs_vars /\ middle'.vs_vars = before'.vs_vars ==>
  current_paired_after outs outs' before before' after after'
Proof
  simp[current_paired_after_def, current_indexed_writes_def] >> metis_tac[]
QED

Theorem current_paired_result_rebase:
  current_paired_result_writes outs outs' middle middle' result result' /\
  middle.vs_vars = before.vs_vars /\ middle'.vs_vars = before'.vs_vars ==>
  current_paired_result_writes outs outs' before before' result result'
Proof
  Cases_on `result` >> Cases_on `result'` >>
  simp[current_paired_result_writes_def] >> metis_tac[current_paired_after_rebase]
QED

Theorem current_exec_ext_call_paired:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_ext_call inst st gas addr value ao az ro rz static)
    (exec_ext_call inst' st' gas addr value ao az ro rz static)
Proof
  strip_tac >>
  `venom_call_request st addr value ao az static =
   venom_call_request st' addr value ao az static`
    by metis_tac[venom_call_request_frame] >>
  qabbrev_tac `rq = venom_call_request st addr value ao az static` >>
  `FST (consume_call_outcome rq (w2n ro) (w2n rz) st) =
   FST (consume_call_outcome rq (w2n ro) (w2n rz) st')`
    by metis_tac[consume_call_outcome_frame, PAIR_EQ] >>
  `execution_frame (SND (consume_call_outcome rq (w2n ro) (w2n rz) st)) =
   execution_frame (SND (consume_call_outcome rq (w2n ro) (w2n rz) st'))`
    by metis_tac[consume_call_outcome_frame_transport] >>
  simp[Abbr `rq`, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  rename1 `execution_frame after = execution_frame after'` >>
  irule current_paired_result_rebase >> qexistsl_tac [`after`,`after'`] >>
  conj_tac >- gvs[consume_call_outcome_eq] >>
  conj_tac >- gvs[consume_call_outcome_eq] >>
  irule current_paired_single_output >> simp[Excl "consume_call_outcome_eq"] >>
  gvs[consume_call_outcome_eq]
QED

Theorem current_exec_delegatecall_paired:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_result_rebase >> qexistsl_tac [`x1`,`after'`] >> simp[] >>
  irule current_paired_single_output >> simp[]
QED

Theorem current_exec_create_paired:
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (exec_create inst st value off sz salt) (exec_create inst' st' value off sz salt)
Proof
  strip_tac >> drule current_create_request_agree >> strip_tac >>
  Cases_on `w2n sz > 2 * max_code_size`
  >- (Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >>
      gvs[exec_create_def] >> rename1 `LENGTH xs = LENGTH ys` >>
      Cases_on `xs` >> Cases_on `ys` >> gvs[exec_create_def] >>
      irule current_paired_after_unchanged >>
      gvs[halt_state_def, set_returndata_def, execution_frame_def,
          venom_state_component_equality]) >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st` >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st'` >>
  drule_all current_consume_create_agree >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  rename1 `execution_frame after = execution_frame after'` >>
  irule current_paired_result_rebase >> qexistsl_tac [`after`,`after'`] >> simp[] >>
  irule current_paired_single_output >> simp[]
QED

Theorem current_assign_paired:
  inst.inst_opcode = ASSIGN /\ inst'.inst_opcode = ASSIGN /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_after_single >> simp[]
QED

Theorem current_special_read0_paired:
  (inst.inst_opcode = GETFMP \/ inst.inst_opcode = INITIAL_FMP) /\
  inst'.inst_opcode = inst.inst_opcode /\
  LENGTH inst.inst_operands = LENGTH inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_after_single >> simp[]
QED

Theorem current_dalloca_paired:
  inst.inst_opcode = DALLOCA /\ inst'.inst_opcode = DALLOCA /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  simp[current_paired_after_def, update_var_def, execution_frame_def] >>
  conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexists_tac `[(0,st'.vs_fmp)]` >> simp[current_indexed_writes_def]
QED

Theorem current_param_paired:
  (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/
   inst.inst_opcode = RETPC_PARAM) /\
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_after_single >> simp[]
QED


Theorem current_terminal_paired:
  (inst.inst_opcode = STOP \/ inst.inst_opcode = SINK \/ inst.inst_opcode = INVALID) /\
  inst'.inst_opcode = inst.inst_opcode /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  irule current_paired_after_unchanged >>
  gvs[halt_state_def, set_returndata_def, execution_frame_def, venom_state_component_equality]
QED

Theorem current_jump_paired:
  execution_frame st = execution_frame st' /\ st.vs_current_bb = st'.vs_current_bb ==>
  current_paired_after outs outs' st st' (jump_to lbl st) (jump_to lbl st')
Proof
  strip_tac >> irule current_paired_after_unchanged >>
  gvs[jump_to_def, execution_frame_def, venom_state_component_equality]
QED

Theorem current_jmp_paired:
  inst.inst_opcode = JMP /\ inst'.inst_opcode = JMP /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\ st.vs_current_bb = st'.vs_current_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_operands` >>
  gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = op::tail` >> Cases_on `tail` >>
  gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  Cases_on `op` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  irule current_jump_paired >> simp[]
QED

Theorem current_djmp_paired:
  inst.inst_opcode = DJMP /\ inst'.inst_opcode = DJMP /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\ st.vs_current_bb = st'.vs_current_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[step_inst_base_opcode_eqs, rename_current_operands_def] >>
  rename1 `inst.inst_operands = op::tail` >>
  `eval_operand (HD (rename_current_operands rs [op])) st' = eval_operand op st`
    by (irule current_eval_operand_occurrence >> simp[] >> qexists_tac `op::tail` >> simp[]) >>
  gvs[current_rename_operands_map] >>
  rewrite_tac[GSYM current_rename_operands_map, current_rename_operands_extract_labels] >>
  qmatch_goalsub_abbrev_tac `eval_operand renamed st'` >>
  Cases_on `eval_operand renamed st'` >> gvs[] >>
  Cases_on `extract_labels tail` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >> irule current_jump_paired >> simp[]
QED

Theorem current_jnz_paired:
  inst.inst_opcode = JNZ /\ inst'.inst_opcode = JNZ /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\ st.vs_current_bb = st'.vs_current_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = a::tail` >> Cases_on `tail` >>
  gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = a::b::rest` >> Cases_on `b` >>
  gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  Cases_on `rest` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = a::Label yes::c::last` >> Cases_on `c` >>
  gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  Cases_on `last` >> gvs[step_inst_base_opcode_eqs, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;Label yes;Label no]` >>
  `eval_operand (HD (rename_current_operands rs [a])) st' = eval_operand a st`
    by (irule current_eval_operand_occurrence >> simp[] >> qexists_tac `[a;Label yes;Label no]` >> simp[]) >>
  gvs[current_rename_operands_map] >>
  Cases_on `eval_operand a st` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >> irule current_jump_paired >> simp[]
QED

Theorem current_sha3_paired:
  inst.inst_opcode = SHA3 /\ inst'.inst_opcode = SHA3 /\
  LIST_REL (\a b. eval_operand a st = eval_operand b st')
    inst.inst_operands inst'.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
  irule current_paired_single_output >> simp[]
QED

Theorem current_create_paired:
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >>
  asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       pure_asm_rewrite_tac[optionTheory.option_case_def, current_paired_result_constructors]) >>
  qpat_assum `inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `inst'.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule current_exec_create_paired >> simp[]
QED

Theorem current_external_call_paired:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
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
       pure_asm_rewrite_tac[optionTheory.option_case_def, current_paired_result_constructors]) >>
  qpat_assum `inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `inst'.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
  FIRST [irule current_exec_ext_call_paired, irule current_exec_delegatecall_paired] >>
  simp[]
QED

Theorem current_write_memory_paired:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_after outs outs' st st'
    (write_memory_with_expansion off bytes st)
    (write_memory_with_expansion off bytes st')
Proof
  strip_tac >> irule current_paired_after_unchanged >>
  gvs[write_memory_with_expansion_def, execution_frame_def, venom_state_component_equality]
QED

Theorem current_copy3_paired:
  (opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = RETURNDATACOPY \/
   opc = MCOPY \/ opc = DLOADBYTES) /\
  inst.inst_opcode = opc /\ inst'.inst_opcode = opc /\
  LENGTH inst.inst_operands = 3 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b;c]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand c st = _` (assume_tac o SYM) >>
  `st.vs_call_ctx = st'.vs_call_ctx /\ st.vs_code = st'.vs_code /\
   st.vs_data_section = st'.vs_data_section /\ st.vs_memory = st'.vs_memory /\
   st.vs_returndata = st'.vs_returndata` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[]) >>
  (Cases_on `eval_operand b st` >- simp[]) >>
  (Cases_on `eval_operand c st` >- simp[]) >>
  simp[mcopy_def]
  >~ [`current_paired_result_writes _ _ _ _ (if _ then _ else _) _`]
  >- (IF_CASES_TAC
      >- (simp[] >> irule current_paired_after_unchanged >>
          gvs[halt_state_def, set_returndata_def, execution_frame_def,
              venom_state_component_equality]) >>
      simp[] >> irule current_write_memory_paired >> simp[]) >>
  irule current_write_memory_paired >> simp[]
QED

Theorem current_extcodecopy_paired:
  inst.inst_opcode = EXTCODECOPY /\ inst'.inst_opcode = EXTCODECOPY /\
  LENGTH inst.inst_operands = 4 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b;c;d]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand c st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand d st = _` (assume_tac o SYM) >>
  `st.vs_accounts = st'.vs_accounts` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[]) >>
  (Cases_on `eval_operand b st` >- simp[]) >>
  (Cases_on `eval_operand c st` >- simp[]) >>
  (Cases_on `eval_operand d st` >- simp[]) >>
  simp[] >> irule current_write_memory_paired >> simp[]
QED

Theorem current_istore_paired:
  inst.inst_opcode = ISTORE /\ inst'.inst_opcode = ISTORE /\
  LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[]) >>
  (Cases_on `eval_operand b st` >- simp[]) >>
  simp[] >> irule current_paired_after_unchanged >>
  gvs[istore_def, mstore_def, write_memory_with_expansion_def,
      execution_frame_def, venom_state_component_equality]
QED

Theorem current_selfdestruct_paired:
  inst.inst_opcode = SELFDESTRUCT /\ inst'.inst_opcode = SELFDESTRUCT /\
  LENGTH inst.inst_operands = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  `st.vs_call_ctx = st'.vs_call_ctx /\ st.vs_accounts = st'.vs_accounts` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >- simp[] >>
  simp[] >> irule current_paired_after_unchanged >>
  gvs[halt_state_def, set_returndata_def, execution_frame_def,
      venom_state_component_equality]
QED

Theorem current_ret_paired:
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_fmp = st'.vs_fmp` by
    (qpat_x_assum `execution_frame _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >>
     simp[execution_frame_def]) >>
  drule_all current_eval_operands_agree >> strip_tac >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands st` >> gvs[] >>
  Cases_on `x` >> gvs[] >> irule current_paired_after_unchanged >> simp[]
QED

Theorem current_store_effects_paired:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_after outs outs' st st' (mstore off w st) (mstore off w st') /\
  current_paired_after outs outs' st st' (mstore8 off w st) (mstore8 off w st') /\
  current_paired_after outs outs' st st' (sstore key w st) (sstore key w st') /\
  current_paired_after outs outs' st st' (tstore key w st) (tstore key w st')
Proof
  strip_tac >> rpt conj_tac >> irule current_paired_after_unchanged >>
  gvs[mstore_def, mstore8_def, sstore_def, tstore_def,
      execution_frame_def, venom_state_component_equality]
QED

Theorem current_assert_paired:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst'.inst_opcode = inst.inst_opcode /\ LENGTH inst.inst_operands = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >> simp[] >>
  Cases_on `x = 0w` >> simp[] >> irule current_paired_after_unchanged >>
  gvs[execution_frame_def, halt_state_def, revert_state_def, set_returndata_def,
      venom_state_component_equality]
QED

Theorem current_return_paired:
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
  inst'.inst_opcode = inst.inst_opcode /\ LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  `st.vs_memory = st'.vs_memory` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
     simp[execution_frame_def]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >> simp[] >>
  Cases_on `eval_operand b st` >> simp[] >>
  irule current_paired_after_unchanged >>
  gvs[execution_frame_def, halt_state_def, revert_state_def, set_returndata_def,
      venom_state_component_equality]
QED

Theorem current_setfmp_paired:
  inst.inst_opcode = SETFMP /\ inst'.inst_opcode = SETFMP /\
  LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = [] /\ inst'.inst_outputs = [] /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >- simp[] >>
  simp[] >> irule current_paired_after_unchanged >>
  gvs[execution_frame_def, venom_state_component_equality]
QED

Theorem current_wf_nop_paired:
  inst.inst_opcode = NOP /\ inst'.inst_opcode = NOP /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  irule current_paired_after_unchanged >> simp[]
QED

Theorem current_log_paired:
  inst.inst_opcode = LOG /\ inst'.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: rest /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> reverse (Cases_on `LENGTH rest = w2n tc + 2`)
  >- (gvs[rename_current_operands_def] >>
      asm_rewrite_tac[step_inst_base_def] >> simp[]) >>
  `eval_operand (EL 0 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 0 (REVERSE rest)) st` by
    (`MEM (EL 0 (REVERSE rest)) (REVERSE rest)` by
       (irule EL_MEM >> simp[]) >>
     simp[current_rename_operands_el] >> irule current_eval_operand_occurrence >>
     simp[] >> qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operand (EL 1 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 1 (REVERSE rest)) st` by
    (`MEM (EL 1 (REVERSE rest)) (REVERSE rest)` by
       (irule EL_MEM >> simp[]) >>
     simp[current_rename_operands_el] >> irule current_eval_operand_occurrence >>
     simp[] >> qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operands (rename_current_operands rs (DROP 2 (REVERSE rest))) st' =
   eval_operands (DROP 2 (REVERSE rest)) st` by
    (irule current_eval_operands_subset >> simp[] >>
     qexists_tac `inst.inst_operands` >> gvs[] >>
     rpt strip_tac >> drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  gvs[rename_current_operands_def] >>
  asm_rewrite_tac[step_inst_base_def] >>
  simp[GSYM current_rename_operands_reverse, GSYM current_rename_operands_drop] >>
  (Cases_on `eval_operand (HD (REVERSE rest)) st` >- simp[]) >>
  (Cases_on `eval_operand (EL 1 (REVERSE rest)) st` >- simp[]) >>
  (Cases_on `eval_operands (DROP 2 (REVERSE rest)) st` >- simp[]) >>
  simp[] >> irule current_paired_after_unchanged >>
  gvs[execution_frame_def, venom_state_component_equality]
QED

Theorem current_dret_paired:
  inst.inst_opcode = DRET /\ inst'.inst_opcode = DRET /\
  inst.inst_outputs = [] /\ inst'.inst_outputs = [] /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule current_parse_dret_shape >> strip_tac >>
  drule_all current_eval_operands_agree >> strip_tac >>
  `st.vs_call_entry_fmp = st'.vs_call_entry_fmp` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_simp_tac (srw_ss()) [step_inst_base_DRET] >>
  Cases_on `parse_dret_shape inst` >- simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_operands inst.inst_operands st` >- simp[] >> simp[] >>
  Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))` >- simp[] >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_all current_pack_dret_frame >> strip_tac >>
  imp_res_tac current_pack_dret_fields >>
  simp[] >> irule current_paired_after_unchanged >>
  gvs[execution_frame_def, venom_state_component_equality]
QED

(* Dispatch only at the semantic-family boundary, never through call internals. *)
val current_paired_dispatch : tactic =
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
        if mem opc pure2 then pure current_exec_pure2_paired
        else if mem opc ["ADDMOD","MULMOD"] then pure current_exec_pure3_paired
        else if mem opc ["ISZERO","NOT"] then pure current_exec_pure1_paired
        else if mem opc ["MLOAD","SLOAD","TLOAD","DLOAD","ILOAD","BLOCKHASH","BLOBHASH","BALANCE","CALLDATALOAD","EXTCODESIZE","EXTCODEHASH"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_read1_paired >>
          simp[] >> qpat_x_assum `execution_frame _ = _` mp_tac >>
          simp[execution_frame_def, venom_state_component_equality,
               mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
        else if mem opc ["ADDRESS","CALLER","CALLVALUE","GAS","ORIGIN","GASPRICE","CHAINID","COINBASE","TIMESTAMP","NUMBER","PREVRANDAO","GASLIMIT","BASEFEE","BLOBBASEFEE","SELFBALANCE","CALLDATASIZE","RETURNDATASIZE","MEMTOP","CODESIZE"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_read0_paired >>
          simp[] >> qpat_x_assum `execution_frame _ = _` mp_tac >>
          simp[execution_frame_def, venom_state_component_equality]
        else if mem opc ["MSTORE","MSTORE8","SSTORE","TSTORE"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_write2_paired >>
          simp[] >> rpt gen_tac >>
          gvs[mstore_def,mstore8_def,sstore_def,tstore_def,
              execution_frame_def,venom_state_component_equality]
        else if opc = "NOP" then direct current_wf_nop_paired
        else if mem opc ["DLOADBYTES","MCOPY","CODECOPY","CALLDATACOPY","RETURNDATACOPY"] then direct current_copy3_paired
        else if mem opc ["ASSERT","ASSERT_UNREACHABLE"] then direct current_assert_paired
        else if mem opc ["RETURN","REVERT"] then direct current_return_paired
        else if mem opc ["STOP","SINK","INVALID"] then direct current_terminal_paired
        else if mem opc ["RET","RETFMP"] then direct current_ret_paired
        else if opc = "ASSIGN" then direct current_assign_paired
        else if opc = "DALLOCA" then direct current_dalloca_paired
        else if opc = "BUMP" then direct current_bump_paired
        else if mem opc ["GETFMP","INITIAL_FMP"] then direct current_special_read0_paired
        else if mem opc ["CREATE","CREATE2"] then direct current_create_paired
        else if mem opc ["CALL","STATICCALL","DELEGATECALL"] then direct current_external_call_paired
        else if opc = "SHA3" then direct current_sha3_paired
        else if opc = "DRET" then direct current_dret_paired
        else if opc = "EXTCODECOPY" then direct current_extcodecopy_paired
        else if opc = "ISTORE" then direct current_istore_paired
        else if opc = "SETFMP" then direct current_setfmp_paired
        else if opc = "LOG" then
          fs[inst_wf_def] >>
          qpat_assum `inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
          irule current_log_paired >> simp[] >>
          qexists_tac `rs` >> gvs[]
        else if opc = "SELFDESTRUCT" then direct current_selfdestruct_paired
        else if mem opc ["PARAM","FMP_PARAM","RETPC_PARAM"] then direct current_param_paired
        else if opc = "ALLOCA" then
          fs[inst_wf_def] >>
          simp[step_inst_base_opcode_eqs, current_rename_operands_map] >>
          irule current_exec_alloca_paired >> simp[]
        else if opc = "DJMP" then direct current_djmp_paired
        else if opc = "JNZ" then direct current_jnz_paired
        else if opc = "JMP" then direct current_jmp_paired
        else if opc = "PHI" then gvs[]
        else if opc = "INVOKE" then simp[step_inst_base_opcode_eqs]
        else FAIL_TAC ("unrouted paired " ^ opc)
    in tac g end);

Theorem current_paired_family_arithmetic[local]:
  MEM inst.inst_opcode [Exp;Div;DELEGATECALL;CREATE;CALLVALUE;CALLER;CALLDATASIZE;
    CALLDATALOAD;CALLDATACOPY;BLOCKHASH;ASSIGN;ASSERT_UNREACHABLE;ASSERT;AND;ALLOCA;ADDMOD;ADD] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_dynamic[local]:
  MEM inst.inst_opcode [DRET;DLOADBYTES;DJMP;DALLOCA;CREATE2;CHAINID;CALL;BYTE;BUMP;BASEFEE;BALANCE;ADDRESS] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_code[local]:
  MEM inst.inst_opcode [EXTCODESIZE;EXTCODEHASH;EXTCODECOPY;EQ;DLOAD;COINBASE;CODESIZE;CODECOPY;BLOBHASH;BLOBBASEFEE] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_control[local]:
  MEM inst.inst_opcode [JNZ;JMP;ISZERO;ISTORE;INVOKE;GETFMP;GAS;FMP_PARAM] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_initial[local]:
  MEM inst.inst_opcode [INVALID;INITIAL_FMP;ILOAD;GT;GASPRICE;GASLIMIT] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_effects[local]:
  MEM inst.inst_opcode [ORIGIN;OFFSET;NUMBER;NOT;NOP;Mod;MULMOD;MUL;MSTORE;MEMTOP;LOG] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_memory[local]:
  MEM inst.inst_opcode [MSTORE8;OR;MLOAD;MCOPY;LT] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_returns[local]:
  MEM inst.inst_opcode [TSTORE;TIMESTAMP;SUB;SSTORE;SLT;SHR;SHL;SGT;SETFMP;SELFDESTRUCT;SAR;REVERT;RETURN;RETFMP;RET;PHI] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_terminal[local]:
  MEM inst.inst_opcode [STOP;STATICCALL;SMOD;SINK;SIGNEXTEND;SHA3;SDIV;PREVRANDAO] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_paired_family_remaining[local]:
  MEM inst.inst_opcode [TLOAD;SLOAD;SELFBALANCE;RETURNDATASIZE;RETURNDATACOPY;RETPC_PARAM;PARAM;XOR] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >> current_paired_dispatch
QED

Theorem current_step_inst_base_paired:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_paired_result_writes inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  (fn g as (asms,_) =>
    let
      val eq = valOf (List.find (fn t => is_eq t andalso
        is_const (rhs t) andalso type_of (rhs t) = ``:opcode``) asms)
      val opc = fst (dest_const (rhs eq))
      val families = [
        (["Exp","Div","DELEGATECALL","CREATE","CALLVALUE","CALLER","CALLDATASIZE",
          "CALLDATALOAD","CALLDATACOPY","BLOCKHASH","ASSIGN","ASSERT_UNREACHABLE",
          "ASSERT","AND","ALLOCA","ADDMOD","ADD"], current_paired_family_arithmetic),
        (["DRET","DLOADBYTES","DJMP","DALLOCA","CREATE2","CHAINID","CALL","BYTE",
          "BUMP","BASEFEE","BALANCE","ADDRESS"], current_paired_family_dynamic),
        (["EXTCODESIZE","EXTCODEHASH","EXTCODECOPY","EQ","DLOAD","COINBASE",
          "CODESIZE","CODECOPY","BLOBHASH","BLOBBASEFEE"], current_paired_family_code),
        (["JNZ","JMP","ISZERO","ISTORE","INVOKE","GETFMP","GAS","FMP_PARAM"], current_paired_family_control),
        (["INVALID","INITIAL_FMP","ILOAD","GT","GASPRICE","GASLIMIT"], current_paired_family_initial),
        (["ORIGIN","OFFSET","NUMBER","NOT","NOP","Mod","MULMOD","MUL","MSTORE","MEMTOP","LOG"], current_paired_family_effects),
        (["MSTORE8","OR","MLOAD","MCOPY","LT"], current_paired_family_memory),
        (["TSTORE","TIMESTAMP","SUB","SSTORE","SLT","SHR","SHL","SGT","SETFMP",
          "SELFDESTRUCT","SAR","REVERT","RETURN","RETFMP","RET","PHI"], current_paired_family_returns),
        (["STOP","STATICCALL","SMOD","SINK","SIGNEXTEND","SHA3","SDIV","PREVRANDAO"], current_paired_family_terminal),
        (["TLOAD","SLOAD","SELFBALANCE","RETURNDATASIZE","RETURNDATACOPY","RETPC_PARAM","PARAM","XOR"], current_paired_family_remaining)]
      val th = snd (valOf (List.find (fn (ops,_) => mem opc ops) families))
    in (if opc = "PHI" then gvs[] else
        irule th >> simp[] >> qexists_tac `rs` >> simp[]) g end)
QED
