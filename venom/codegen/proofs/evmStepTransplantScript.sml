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
