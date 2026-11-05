(*
 * One step of a frame's run against its call trace, GAS readings and
 * run_call.  The frame is at depth LENGTH es.contexts; a step either
 * stays at that depth, enters a child (one deeper) whose run_call comes
 * back to it, or ends the frame (an exception or a drop below it).
 *
 * TOP-LEVEL:
 *   frame_obs_plain_step, frame_obs_gas_step, frame_obs_call_same_depth,
 *   frame_obs_call_enter, frame_obs_terminal - call_trace/gas_readings
 *   run_call_same_depth_step, run_call_enter_return,
 *   run_call_terminal_step - run_call
 *)

Theory frameObsStep
Ancestors
  callTrace frameOutcome vfmExecution vfmExecutionProp vfmDecreasesGas
  vfmAccountFrame vfmContextLength

(* ===== call_trace and gas_readings ===== *)

Theorem frame_obs_plain_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) <> SOME Gas /\
  ~observable_call (FST (HD es.contexts)) ==>
  call_trace es = call_trace es1 /\ gas_readings es = gas_readings es1
Proof
  cheat
QED

Theorem frame_obs_gas_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) = SOME Gas ==>
  call_trace es = call_trace es1 /\
  gas_readings es = HD (FST (HD es1.contexts)).stack :: gas_readings es1
Proof
  cheat
QED

Theorem frame_obs_call_same_depth:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  observable_call (FST (HD es.contexts)) ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es1
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es1 /\
  gas_readings es = gas_readings es1
Proof
  cheat
QED

(* The child's run_call ends at the first state back at the frame's depth. *)
Theorem frame_obs_call_enter:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  observable_call (FST (HD es.contexts)) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es2
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es2 /\
  gas_readings es = gas_readings es2
Proof
  cheat
QED

Theorem frame_obs_terminal:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  call_trace es = [] /\ gas_readings es = []
Proof
  cheat
QED

(* ===== run_call ===== *)

Theorem run_call_same_depth_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts ==>
  run_call es1 = run_call es
Proof
  cheat
QED

Theorem run_call_enter_return:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  run_call es2 = run_call es
Proof
  cheat
QED

Theorem run_call_terminal_step:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  run_call es = SOME (r, es1)
Proof
  cheat
QED
