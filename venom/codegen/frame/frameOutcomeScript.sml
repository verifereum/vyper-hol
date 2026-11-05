(* TOP-LEVEL: frame_outcome, frame_resource_starved, add_frame_gas,
 * frame_inst_at, frame_inst_raises,
 * frame_outcome_single_frame_run.
 *
 * Frame-level boundary for run_call.  The relations themselves use only
 * vfmExecution; vfmRunCall supplies the proof-only single-frame bridge.
 * Deriving frame_outcome from an arbitrary EVM run is a separate obligation.
 *)
Theory frameOutcome
Ancestors
  vfmExecution vfmRunCall

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
      | (parent, prb) :: rest' =>                 (* nested state *)
          r = INL () /\
          ?parent' prb' rest'' mr.
            ctxt.msgParams.outputTo = Memory mr /\
            es'.contexts = (parent', prb') :: rest'' /\
            MAP FST rest'' = MAP FST rest' /\
            (rest' <> [] ==> prb' = prb) /\
            parent'.returnData = out /\
            parent'.stack = b2w (exc = NONE) :: parent.stack /\
            parent'.pc = SUC parent.pc /\
            parent'.logs =
              parent.logs ++ (if exc = NONE then ctxt.logs ++ lgs else []) /\
            parent'.memory =
              buffer_write mr.offset (TAKE mr.size out) parent.memory /\
            (exc <> NONE ==> es'.rollback = rb)
End

Definition frame_resource_starved_def:
  frame_resource_starved es r es' <=>
    ?exc out lgs. (exc = OutOfGas \/ exc = StackOverflow) /\
                  frame_outcome es r es' (SOME exc) out lgs
End

(* es with g more gas for our (top) frame.  Every frame on the stack gets
   g more gas limit and every caller g more gas used, so the callers'
   unused gas is unchanged and wf_state's gas invariants (gas_stack_ok,
   wf_context) still hold. *)
Definition add_frame_gas_def:
  add_frame_gas g es =
    case es.contexts of
      [] => es
    | (c, rb) :: rest =>
        es with contexts :=
          (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g),
           rb) ::
          MAP (\(c, rb).
                 (c with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
                  rb)) rest
End

(* s is a state of es's frame (run_call's loop, our frame on top) and op
   is the instruction step runs there. *)
Definition frame_inst_at_def:
  frame_inst_at es s op <=>
    ?ctxt rb rest.
      RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
                 step a = (INL (), b)) es s /\
      s.contexts = (ctxt, rb) :: rest /\
      LENGTH s.contexts = LENGTH es.contexts /\
      case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
        SOME op' => op = op'
      | NONE => op = if LENGTH ctxt.msgParams.code <= ctxt.pc then Stop
                     else Invalid
End

(* Our frame's instruction op raises exc.  Stated on step_inst, not on
   step's result: step catches the exception and pops the frame, and in a
   nested frame frame_outcome tells a failure apart only from success.
   The raise must leave the stack at our depth: a precompile runs inside
   the CALL that pushed its frame, and its failure is the callee's. *)
Definition frame_inst_raises_def:
  frame_inst_raises es exc op <=>
    ?s s'.
      frame_inst_at es s op /\
      step_inst op s = (INR (SOME exc), s') /\
      LENGTH s'.contexts = LENGTH es.contexts
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
