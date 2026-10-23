(* Construction probes only: these do not assert runtime ABI simulation. *)
Theory groupedDispatchProps
Ancestors vyperCompiler moduleLowering compileEnv
Libs wordsLib

Definition probe_common_def:
  probe_common label = <|
    ec_env := (ARB : compile_env);
    ec_pos_args := [];
    ec_common_label := label;
    ec_nonreentrant := F; ec_nkey := 0; ec_transient := T;
    ec_view := F; ec_payable := T;
    ec_body := []; ec_return := NONE |>
End

Definition probe_group_def:
  probe_group label sel = ExternalDefaults (probe_common label)
    [(sel,label ++ "_0",4,0); (sel+1,label ++ "_1",36,1)]
    [("x",BaseT (UintT 256),Literal (BaseT (UintT 256)) (IntL 7))] 4
End

Definition dispatch_blocks_def:
  dispatch_blocks st = REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb;
        bb_instructions := st.cs_current_insts |>]
End

Definition dispatch_ops_def:
  dispatch_ops st = MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions)
                       (dispatch_blocks st)
End

Theorem grouped_empty:
  compile_external_groups mid [] st = ([],st)
Proof
  simp[compile_external_groups_def, comp_return_def]
QED

Theorem grouped_one_job:
  MAP (\j. case j of ExternalCommonJob c vs =>
         (c.ec_common_label,LENGTH vs) | ExternalLegacyJob p => ("legacy",0))
    (FST (compile_external_groups (Var "mid") [probe_group "f" 10]
                                 (initial_compile_state "entry"))) = [("f",1)]
Proof
  EVAL_TAC
QED

Theorem grouped_two_jobs:
  MAP (\j. case j of ExternalCommonJob c vs =>
         (c.ec_common_label,LENGTH vs) | ExternalLegacyJob p => ("legacy",0))
    (FST (compile_external_groups (Var "mid")
       [probe_group "f" 10;probe_group "g" 20]
       (initial_compile_state "entry"))) = [("f",1);("g",1)]
Proof
  EVAL_TAC
QED

Theorem grouped_one_shape:
  dispatch_ops (SND (compile_external_groups (Var "mid")
    [probe_group "f" 10] (initial_compile_state "entry"))) =
    [[ALLOCA; EQ; JNZ]; [MSTORE; JMP]; [EQ; JNZ];
     [CALLDATASIZE; LT; ISZERO; ASSERT; CALLDATALOAD; MSTORE; JMP]; []]
Proof
  EVAL_TAC
QED

Definition probe_single_def:
  probe_single = ExternalSingle (30,"plain",F)
    ("plain",ARB : compile_env,[],4,T,F,0,T,F,[],NONE)
End

Theorem grouped_mixed_order:
  MAP (\j. case j of ExternalCommonJob c vs =>
         (c.ec_common_label,LENGTH vs) | ExternalLegacyJob p => ("legacy",0))
    (FST (compile_external_groups (Var "mid")
       [probe_group "f" 10;probe_single;probe_group "g" 20]
       (initial_compile_state "entry"))) = [("f",1);("legacy",0);("g",1)]
Proof
  EVAL_TAC
QED

Theorem grouped_mixed_allocation_count:
  LENGTH (FILTER ($= ALLOCA) (FLAT (dispatch_ops
    (SND (compile_external_groups (Var "mid")
       [probe_group "f" 10;probe_single;probe_group "g" 20]
       (initial_compile_state "entry")))))) = 2
Proof
  EVAL_TAC
QED

(* No common label has been materialized when dispatch finishes. The last
   instruction jumps to fallback, before the deferred jobs are consumed. *)
Theorem grouped_dispatch_defers_common:
  let result = compile_group_dispatch_linear
    [probe_group "f" 10;probe_group "g" 20] "fallback"
    (initial_compile_state "entry") in
  ~MEM "f" (MAP (\b. b.bb_label) (dispatch_blocks (SND result))) /\
  ~MEM "g" (MAP (\b. b.bb_label) (dispatch_blocks (SND result))) /\
  (LAST (SND result).cs_current_insts).inst_opcode = JMP /\
  (LAST (SND result).cs_current_insts).inst_operands = [Label "fallback"]
Proof
  EVAL_TAC
QED

Theorem grouped_common_bodies_once:
  let (jobs,st) = compile_group_dispatch_linear
    [probe_group "f" 10;probe_group "g" 20] "fallback"
    (initial_compile_state "entry") in
  let final = SND (compile_external_jobs jobs st) in
    LENGTH (FILTER (\b. b.bb_label = "f") (dispatch_blocks final)) = 1 /\
    LENGTH (FILTER (\b. b.bb_label = "g") (dispatch_blocks final)) = 1
Proof
  EVAL_TAC
QED

(* The all-supplied entry still has just the owning group's single alloca;
   its calldata decode writes the very operand returned in the common job. *)
Theorem grouped_shared_pointer:
  let (jobs,st) = compile_external_groups (Var "mid")
    [probe_group "f" 10] (initial_compile_state "entry") in
  (case HD jobs of ExternalCommonJob c vs => MAP (\(n,p,t,e). p) vs
                 | ExternalLegacyJob p => []) = [Var "%0"] /\
  MAP (\i. HD i.inst_operands)
      (FILTER (\i. i.inst_opcode = MSTORE)
        (FLAT (MAP (\b. b.bb_instructions) (dispatch_blocks st)))) =
    [Var "%0";Var "%0"]
Proof
  EVAL_TAC
QED

val () = List.app (fn th =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail "grouped dispatch probe has oracle/axiom dependencies")
  [grouped_empty, grouped_one_job, grouped_two_jobs, grouped_one_shape,
   grouped_mixed_order, grouped_mixed_allocation_count,
   grouped_dispatch_defers_common, grouped_common_bodies_once,
   grouped_shared_pointer];
