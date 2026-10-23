(* Executable specification probes for the pinned Python reclaim interface.
 * This is not the production transfer or a proof of its equivalence. Eligibility
 * abstracts _dalloca_allocation/_allocation_is_live; veto abstracts captures.
 * Python stacks are bottom-first; these probes use HOL's newest-first order.
 *)
Theory fmpReclaimProbe
Ancestors
  fmpReclaimDefs

Definition reclaim_probe_pop_def:
  reclaim_probe_pop eligible veto (stack:string list) =
    if veto then (NONE,stack) else
    let popped = TAKEWHILE eligible stack in
    (if popped = [] then NONE else SOME (LAST popped),
     DROPWHILE eligible stack)
End

Definition reclaim_probe_point_def:
  reclaim_probe_point op needs <=>
    MEM op [DALLOCA; JMP; JNZ; DJMP] \/ (op = INVOKE /\ needs)
End

(* A summary-level interpreter: the allocation output is supplied separately,
 * just as _step reads inst.output. Reachability uses NONE as in HOL dataflow. *)
Definition reclaim_probe_step_def:
  reclaim_probe_step op out needs publishes eligible veto NONE = (NONE,NONE) /\
  reclaim_probe_step op out needs publishes eligible veto (SOME st) =
    let (restore,stack) =
      if reclaim_probe_point op needs then
        reclaim_probe_pop eligible (veto \/ ~st.frs_can_reclaim) st.frs_stack
      else (NONE,st.frs_stack) in
    let next = st with frs_stack := stack in
    (restore, SOME
      (if op = SETFMP \/ (op = INVOKE /\ publishes) then
         next with <| frs_stack := []; frs_captures := [] |>
       else if op = DALLOCA then next with frs_stack := out::stack
       else if op = GETFMP then
         next with frs_captures := out::st.frs_captures
       else next))
End

Theorem reclaim_probe_partial_pop:
  reclaim_probe_pop (\v. v <> "live") F ["dead";"live"] =
    (SOME "dead",["live"]) /\
  reclaim_probe_pop (\v. v <> "live") F ["live";"dead"] =
    (NONE,["live";"dead"]) /\
  reclaim_probe_pop (\v. v <> "unknown") F ["dead";"unknown";"old"] =
    (SOME "dead",["unknown";"old"]) /\
  reclaim_probe_pop (K T) F ["new";"old"] = (SOME "old",[])
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_capture_veto:
  reclaim_probe_pop (K T) T ["new";"old"] = (NONE,["new";"old"])
Proof
  EVAL_TAC
QED

Definition reclaim_probe_state_def:
  reclaim_probe_state = fmp_empty_reclaim_state with
    <| frs_stack := ["new";"old"]; frs_captures := ["capture"] |>
End

Theorem reclaim_probe_push_after_pop:
  reclaim_probe_step DALLOCA "fresh" F F (K T) F
    (SOME reclaim_probe_state) =
    (SOME "old", SOME (reclaim_probe_state with frs_stack := ["fresh"]))
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_get_and_set:
  reclaim_probe_step GETFMP "cap2" F F (K T) F
    (SOME reclaim_probe_state) =
    (NONE, SOME (reclaim_probe_state with frs_captures := ["cap2";"capture"])) /\
  reclaim_probe_step SETFMP "unused" F F (K T) T
    (SOME reclaim_probe_state) =
    (NONE, SOME (reclaim_probe_state with <| frs_stack := []; frs_captures := [] |>))
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_invoke:
  reclaim_probe_step INVOKE "unused" T F (K T) F
    (SOME reclaim_probe_state) =
    (SOME "old", SOME (reclaim_probe_state with frs_stack := [])) /\
  reclaim_probe_step INVOKE "unused" T T (K T) F
    (SOME reclaim_probe_state) =
    (SOME "old", SOME (reclaim_probe_state with <| frs_stack := []; frs_captures := [] |>)) /\
  reclaim_probe_step INVOKE "unused" F F (K T) F
    (SOME reclaim_probe_state) = (NONE,SOME reclaim_probe_state)
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_boundaries:
  EVERY (\op. FST (reclaim_probe_step op "unused" F F (K T) F
    (SOME reclaim_probe_state)) = SOME "old") [JMP;JNZ;DJMP] /\
  reclaim_probe_step RET "unused" F F (K T) F
    (SOME reclaim_probe_state) = (NONE,SOME reclaim_probe_state) /\
  reclaim_probe_step DALLOCA "fresh" F F (K T) F NONE = (NONE,NONE) /\
  reclaim_probe_step JMP "unused" F F (K T) F
    (SOME (reclaim_probe_state with frs_can_reclaim := F)) =
    (NONE,SOME (reclaim_probe_state with frs_can_reclaim := F))
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_join:
  fmp_common_top ["top";"left"] ["top";"right"] = ["top"] /\
  fmp_common_top ["left";"bottom"] ["right";"bottom"] = [] /\
  fmp_reclaim_option_join NONE (SOME reclaim_probe_state) =
    SOME reclaim_probe_state /\
  (fmp_reclaim_join reclaim_probe_state
    (reclaim_probe_state with <| frs_stack := ["new"]; frs_captures := ["cap2"] |>)).frs_stack =
    ["new"] /\
  MEM "capture" (fmp_reclaim_join reclaim_probe_state
    (reclaim_probe_state with frs_captures := ["cap2"])).frs_captures /\
  MEM "cap2" (fmp_reclaim_join reclaim_probe_state
    (reclaim_probe_state with frs_captures := ["cap2"])).frs_captures
Proof
  EVAL_TAC
QED
