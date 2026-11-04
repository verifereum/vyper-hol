Theory makeSsaCurrentPairedWrites
Ancestors
  makeSsaCurrentWriteFootprint makeSsaCurrentOrdinary venomExecSemantics
  venomState stateFrame finite_map list rich_list pair
  venomCallOracleProps venomCallOracleDefs

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
