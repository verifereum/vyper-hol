(* TOP-LEVEL: frame_outcome, frame_resource_starved, creation_resource_starved,
 * frame_outcome_single_frame_run.
 *
 * Frame-level observations and their settlement back into a caller.
 *)
Theory frameOutcome
Ancestors
  vfmExecution vfmRunCall vfmRunFrame frameGas

(* ===== Frame outcomes ===== *)

Definition frame_outcome_def:
  frame_outcome es r es' exc out lgs <=>
    ?ctxt rb rest.
      es.contexts = (ctxt, rb) :: rest /\
      es'.txParams = es.txParams /\
      case rest of
        [] =>                                     (* single-frame state *)
          r = INR exc /\
          ?ctxt' rb'.
            es'.contexts = [(ctxt', rb')] /\
            ctxt'.returnData = out /\
            (exc = NONE ==> ctxt'.logs = ctxt.logs ++ lgs)
      | _ :: _ =>                                (* nested state *)
          r = INL () /\
          ?pre ctxt' rest' mr.
            ctxt.msgParams.outputTo = Memory mr /\
            ~vfm_abort exc /\
            run_frame es = SOME (INR exc,pre) /\
            pre.contexts = (ctxt', rb) :: rest' /\
            MAP FST rest' = MAP FST rest /\
            FRONT rest' = FRONT rest /\
            ctxt'.msgParams.outputTo = Memory mr /\
            handle_exception exc pre = (r,es') /\
            out = (if exc = NONE \/ exc = SOME Reverted
                   then ctxt'.returnData else []) /\
            (exc = NONE ==> ctxt'.logs = ctxt.logs ++ lgs) /\
            (exc <> NONE ==> es'.rollback = rb)
End

Theorem frame_outcome_nested_run:
  wf_state es /\ 2 <= LENGTH es.contexts /\
  frame_outcome es r es' exc out lgs ==>
  run_call es = SOME (r,es')
Proof
  rw[frame_outcome_def] >> Cases_on `rest` >> gvs[] >>
  drule_all run_frame_call >> simp[]
QED

(* A nested frame preserves the suspended contexts. CREATE can update
   the saved account state of the bottom frame. *)
Theorem frame_outcome_nested_caller:
  es.contexts = (ctxt,rb) :: (parent,prb) :: rest /\
  frame_outcome es r es' exc out lgs ==>
  ?parent' prb' rest' mr.
    ctxt.msgParams.outputTo = Memory mr /\
    es'.contexts = (parent',prb') :: rest' /\
    MAP FST rest' = MAP FST rest /\
    (rest <> [] ==> prb' = prb) /\
    parent'.returnData = out /\
    parent'.stack = b2w (exc = NONE) :: parent.stack /\
    parent'.pc = SUC parent.pc /\
    parent'.logs = parent.logs ++ (if exc = NONE then ctxt.logs ++ lgs else []) /\
    parent'.memory = buffer_write mr.offset (TAKE mr.size out) parent.memory
Proof
  strip_tac >> gvs[frame_outcome_def] >>
  Cases_on `rest'` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  `rest <> [] ==> h1 = prb` by
    (Cases_on `rest` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  Cases_on `exc = NONE` >> Cases_on `exc = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, get_return_data_def, get_output_to_def,
      reraise_def, assert_def, fail_def, inc_pc_def, push_stack_def,
      write_memory_def, pop_and_incorporate_context_def, pop_context_def,
      set_rollback_def, unuse_gas_def, update_gas_refund_def, push_logs_def,
      AllCaseEqs()] >>
  qpat_x_assum `_ = es'` (SUBST_ALL_TAC o SYM) >> simp[]
QED

Theorem frame_outcome_nested_length:
  2 <= LENGTH es.contexts /\
  frame_outcome es r es' exc out lgs ==>
  SUC (LENGTH es'.contexts) = LENGTH es.contexts
Proof
  rw[frame_outcome_def] >> Cases_on `rest` >> gvs[] >>
  `pre.contexts <> []` by simp[] >>
  qpat_assum `MAP FST rest' = _`
    (assume_tac o AP_TERM ``LENGTH : context list -> num``) >>
  drule_all vfmRunCallTheory.handle_exception_inl_pops >> gvs[]
QED

(* Our frame ran out of gas or stack before settlement. *)
Definition frame_resource_starved_def:
  frame_resource_starved es r es' <=>
    ?exc out lgs. (exc = OutOfGas \/ exc = StackOverflow) /\
                  frame_outcome es r es' (SOME exc) out lgs /\
                  frame_raises es exc
End

(* A creation frame ran out of gas or stack.  Its code deposit raises
   OutOfGas after RETURN, outside step_inst, so no instruction is named;
   deployment runs it as a single frame, where r = INR exc. *)
Definition creation_resource_starved_def:
  creation_resource_starved es r es' <=>
    ?exc out lgs. (exc = OutOfGas \/ exc = StackOverflow) /\
                  frame_outcome es r es' (SOME exc) out lgs
End

(* ===== Single-frame bridge ===== *)

(* TOP-LEVEL: L9.  No producer of frame_outcome is assumed or proved here. *)
Theorem frame_outcome_single_frame_run:
  LENGTH es.contexts = 1 /\
  run_call es = SOME (r, es') /\
  frame_outcome es r es' exc out lgs ==>
  run es = SOME (INR exc, es')
Proof
  rpt strip_tac >>
  drule run_call_eq_run_single_context >> strip_tac >>
  gvs[frame_outcome_def] >>
  Cases_on `rest` >> gvs[]
QED
