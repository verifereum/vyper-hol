(* Executable specification probes for the pinned Python reclaim interface.
 * This is not the production transfer or a proof of its equivalence. Eligibility
 * abstracts _dalloca_allocation/_allocation_is_live; veto abstracts captures.
 * Python stacks are bottom-first; these probes use HOL's newest-first order.
 *)
Theory fmpReclaimProbe
Ancestors
  fmpReclaimDefs rich_list

Definition reclaim_probe_pop_def:
  reclaim_probe_pop eligible veto (stack:string list) =
    if veto then (NONE,stack) else
    let (popped,retained) = SPLITP (\v. ~eligible v) stack in
    (if popped = [] then NONE else SOME (LAST popped), retained)
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

(* Historical approximations retained locally as investigation evidence, not
 * exported as production reclaim interfaces. *)
Definition fmp_capture_escaped_def:
  fmp_capture_escaped fn cap <=>
    EXISTS (\inst. MEM cap (inst_uses inst)) (fn_insts fn)
End
Definition fmp_direct_memory_use_def:
  fmp_direct_memory_use inst base <=>
    (MEM inst.inst_opcode [MLOAD; MSTORE; MSTORE8; SHA3] /\
      TAKE 1 inst.inst_operands = [Var base]) \/
    (inst.inst_opcode = MCOPY /\ MEM (Var base) (TAKE 2 inst.inst_operands))
End
Definition fmp_inst_has_unsafe_derived_use_def:
  fmp_inst_has_unsafe_derived_use vars inst <=>
    EXISTS (\v. MEM v (inst_uses inst) /\ ~fmp_direct_memory_use inst v /\
      ~fmp_transparent_opcode inst.inst_opcode) vars
End
Definition fmp_derived_step_def:
  fmp_derived_step [] vars = vars /\
  fmp_derived_step (inst::rest) vars =
    fmp_derived_step rest
      (if fmp_transparent_opcode inst.inst_opcode /\ fmp_inst_uses_any vars inst
       then list_union inst.inst_outputs vars else vars)
End
Definition fmp_derived_vars_def:
  fmp_derived_vars fn base =
    FUNPOW (fmp_derived_step (fn_insts fn)) (LENGTH (fn_insts fn)) [base]
End

(* Checked evidence that the old capture/escape approximation is not the
 * Python interface: an ordinary address-only MLOAD already counts as escape;
 * CALL input-buffer addresses pin allocations under the old whitelist. *)
Theorem reclaim_probe_old_capture_approximation:
  fmp_capture_escaped
    (fn with fn_blocks := [<| bb_label := "entry";
      bb_instructions := [mk_inst 0 MLOAD [Var "cap"] ["value"]] |>]) "cap"
Proof
  EVAL_TAC
QED

Theorem reclaim_probe_old_call_pinning:
  fmp_inst_has_unsafe_derived_use ["ptr"]
    (mk_inst 0 CALL
      [Lit 100w; Lit 1w; Lit 0w; Var "ptr"; Lit 32w; Lit 0w; Lit 0w]
      ["ok"])
Proof
  EVAL_TAC
QED

(* Dataflow indices are pre-instruction boundaries, including the endpoint.
 * The transfer callback receives the instruction, but NOT this index. *)
Theorem reclaim_probe_forward_index:
  df_at NONE
    <| ds_inst := SND (df_fold_forward (\inst st. SOME inst.inst_id)
         "entry" [mk_inst 7 GETFMP [] ["cap"]; mk_inst 9 JMP [] []]
         0 NONE FEMPTY);
       ds_boundary := FEMPTY |> "entry" 0 = NONE /\
  df_at NONE
    <| ds_inst := SND (df_fold_forward (\inst st. SOME inst.inst_id)
         "entry" [mk_inst 7 GETFMP [] ["cap"]; mk_inst 9 JMP [] []]
         0 NONE FEMPTY);
       ds_boundary := FEMPTY |> "entry" 1 = SOME 7 /\
  df_at NONE
    <| ds_inst := SND (df_fold_forward (\inst st. SOME inst.inst_id)
         "entry" [mk_inst 7 GETFMP [] ["cap"]; mk_inst 9 JMP [] []]
         0 NONE FEMPTY);
       ds_boundary := FEMPTY |> "entry" 2 = SOME 9
Proof
  EVAL_TAC
QED

(* A back-edge derivation listed before its source needs re-iteration. *)
Theorem reclaim_probe_loop_capture_derivation:
  let fn' = fn with fn_blocks := [<| bb_label := "loop";
    bb_instructions :=
      [mk_inst 0 ASSIGN [Var "back"] ["head"];
       mk_inst 1 ADD [Var "cap"; Lit 32w] ["back"]] |>] in
  MEM "head" (fmp_derived_vars fn' "cap") /\
  reclaim_probe_pop (K T)
    (EXISTS (\v. MEM v ["head"]) (fmp_derived_vars fn' "cap"))
    ["new";"old"] = (NONE,["new";"old"])
Proof
  EVAL_TAC
QED

(* Escape is occurrence-sensitive, not membership-sensitive: one address
 * occurrence cannot excuse a second occurrence storing the pointer value. *)
Theorem reclaim_probe_escape_occurrences:
  FILTER ($= "ptr") ["ptr";"ptr"] <> FILTER ($= "ptr") ["ptr"] /\
  LENGTH (FILTER ($= "ptr") ["ptr";"ptr"]) >
    LENGTH (FILTER ($= "ptr") ["ptr"])
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpReclaimProbe");
