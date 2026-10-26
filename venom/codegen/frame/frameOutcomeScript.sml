(* TOP-LEVEL: frame_outcome, frame_resource_starved,
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
