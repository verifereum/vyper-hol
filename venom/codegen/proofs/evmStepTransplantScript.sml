(*
 * A step that pushes no context, taken in a nested frame, is the same
 * step taken with the head context alone, up to the outer contexts: one
 * that continues keeps them below the new head, and one that ends the
 * frame (INR in the single-context run) returns to the parent as
 * frame_outcome says.
 *
 * TOP-LEVEL:
 *   step_transplant_continue - a continuing step
 *   step_transplant_end      - a step that ends the frame
 *)

Theory evmStepTransplant
Ancestors
  callTrace frameOutcome vfmExecution vfmExecutionProp vfmSameFrame
  vfmStepLength vfmHandleStep vfmContextLength vfmRunCall

Theorem transplant_handle_exception_memory_total[local]:
  s.contexts = (d, rb) :: (p, prb) :: rest /\
  d.msgParams.outputTo = Memory mr /\
  d.gasUsed <= d.msgParams.gasLimit /\
  d.msgParams.gasLimit - d.gasUsed <= p.gasUsed /\
  LENGTH p.stack < stack_limit ==>
  ?s'. handle_exception e s = (INL (), s') /\
       frame_outcome s (INL ()) s' e
         (if e = NONE \/ e = SOME Reverted then d.returnData else []) [] /\
       (e = NONE ==> s'.rollback = s.rollback)
Proof
  strip_tac >>
  Cases_on `e = NONE` >>
  Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       reraise_def, assert_def, fail_def,
       inc_pc_def, push_stack_def, write_memory_def,
       pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, unuse_gas_def,
       update_gas_refund_def, push_logs_def, frame_outcome_def]
QED

Theorem transplant_handle_exception_singleton[local]:
  s.contexts = [(d, rb)] /\ d.gasUsed <= d.msgParams.gasLimit ==>
  handle_exception e s =
    (INR e, if e = NONE \/ e = SOME Reverted then s else
       s with contexts :=
         [(d with <|gasUsed := d.msgParams.gasLimit; returnData := []|>, rb)])
Proof
  strip_tac >> Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, reraise_def, assert_def, fail_def]
QED

Theorem transplant_handler_wf_bounds[local]:
  wf_state s /\ s.contexts = (d, rb) :: (p, prb) :: rest ==>
  d.gasUsed <= d.msgParams.gasLimit /\
  d.msgParams.gasLimit - d.gasUsed <= p.gasUsed /\
  LENGTH p.stack < stack_limit
Proof
  simp[wf_state_def, wf_context_def, stack_room_ok_def,
       gas_stack_ok_def, unused_gas_def] >>
  strip_tac >> first_x_assum (qspec_then `0` mp_tac) >>
  gvs[wf_context_def]
QED

Theorem transplant_handle_step_memory[local]:
  s.contexts = (d, rb) :: rest /\
  d.msgParams.outputTo = Memory mr /\ ~vfm_abort e ==>
  handle_step e s = handle_exception e s
Proof
  strip_tac >>
  `s.contexts <> [] /\
   (!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a)` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``]
    vfmStaticCallsTheory.handle_create_reraises) >>
  strip_tac >> simp[handle_step_def, handle_def, reraise_def]
QED

Theorem transplant_handle_step_boundary[local]:
  wf_state s /\ s.contexts = (d, rb) :: (p, prb) :: rest /\
  d.msgParams.outputTo = Memory mr /\ ~vfm_abort e ==>
  ?d' t s'.
    handle_step e (s with contexts := [(d, rb)]) = (INR e, t) /\
    t.contexts = [(d', rb)] /\ d'.logs = d.logs /\
    handle_step e s = (INL (), s') /\
    frame_outcome s (INL ()) s' e d'.returnData [] /\
    (e = NONE ==> s'.rollback = t.rollback)
Proof
  strip_tac >>
  drule_all transplant_handler_wf_bounds >> strip_tac >>
  `handle_step e s = handle_exception e s` by
    (irule transplant_handle_step_memory >> simp[] >> metis_tac[]) >>
  `handle_step e (s with contexts := [(d, rb)]) =
   handle_exception e (s with contexts := [(d, rb)])` by
    (irule transplant_handle_step_memory >> simp[] >> metis_tac[]) >>
  drule_all transplant_handle_exception_memory_total >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  `handle_exception e (s with contexts := [(d, rb)]) =
     (INR e, if e = NONE \/ e = SOME Reverted then
       s with contexts := [(d, rb)] else
       (s with contexts := [(d, rb)]) with contexts :=
         [(d with <|gasUsed := d.msgParams.gasLimit; returnData := []|>, rb)])` by
    (irule transplant_handle_exception_singleton >> simp[]) >>
  Cases_on `e = NONE \/ e = SOME Reverted` >> gvs[]
QED

Theorem step_transplant_continue:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INL (), t) ==>
  ?c'. t.contexts = [(c', rb)] /\
       step es = (INL (), t with contexts := (c', rb) :: rest)
Proof
  cheat
QED

(* c' is the head as the single-context run leaves it; the frame's
   logs grow from c.logs by lgs. *)
Theorem step_transplant_end:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!a. c.msgParams.outputTo <> Code a) /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INR e, t) /\ ~vfm_abort e ==>
  ?c' rb' es' lgs.
    t.contexts = [(c', rb')] /\ c'.logs = c.logs ++ lgs /\
    step es = (INL (), es') /\
    frame_outcome es (INL ()) es' e c'.returnData lgs /\
    (e = NONE ==> es'.rollback = t.rollback)
Proof
  cheat
QED
