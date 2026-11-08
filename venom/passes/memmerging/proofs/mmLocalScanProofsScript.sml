(* Each local merging phase with its actual original-DFG provenance. *)
Theory mmLocalScanProofs
Ancestors
  mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner
  venomWf stateEquiv rich_list
Libs
  wordsLib finite_mapLib

Definition mm_local_phase_def:
  mm_local_phase dfg phase (b,t) =
    case phase of
      NONE => transform_block_memzero_supply dfg t b
    | SOME m => transform_block_mode_supply dfg m t b
End

Definition mm_local_prefix_def:
  mm_local_prefix fn0 supply index k =
    FOLDL (\bt phase. mm_local_phase (dfg_build_function fn0) phase bt)
      (EL index fn0.fn_blocks,supply)
      (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
End

Theorem mm_local_prefix_zero[local]:
  mm_local_prefix fn0 supply index 0 = (EL index fn0.fn_blocks,supply)
Proof
  simp[mm_local_prefix_def]
QED

Theorem mm_local_prefix_suc[local]:
  k < 4 ==>
  mm_local_prefix fn0 supply index (SUC k) =
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (mm_local_prefix fn0 supply index k)
Proof
  simp[mm_local_prefix_def, TAKE_SUC_BY_TAKE, FOLDL_SNOC]
QED

Theorem mm_local_phase_label[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==> cc.bb_label = bb.bb_label
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Definition mm_local_zero_fn_def:
  mm_local_zero_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
       mk_inst 2 MSTORE [Lit 32w; Lit 0w] [];
       mk_inst 3 STOP [] []] |>]
End

Definition mm_local_probe_supply_def:
  mm_local_probe_supply fn =
    <| irs_next_inst := 20; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := fn_ir_inst_ids fn;
       irs_used_vars := fn_ir_vars fn;
       irs_used_labels := fn_ir_labels fn |>
End

Theorem mm_local_zero_input[local]:
  fn_inst_wf mm_local_zero_fn /\ wf_function mm_local_zero_fn /\
  wf_ssa mm_local_zero_fn /\
  ir_supply_covers_fn (mm_local_probe_supply mm_local_zero_fn) mm_local_zero_fn
Proof
  EVAL_TAC
QED

Definition mm_local_probe_after_def:
  mm_local_probe_after fn k =
    mm_local_phase (dfg_build_function fn)
      (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
      (mm_local_prefix fn (mm_local_probe_supply fn) 0 k)
End

Theorem mm_local_zero_computed[local]:
  mm_local_probe_after mm_local_zero_fn 0 =
  (<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 NOP [] [];
       mk_inst 20 CALLDATASIZE [] ["formal_var_0"];
       mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] [];
       mk_inst 3 STOP [] []] |>,
   (mm_local_probe_supply mm_local_zero_fn) with
     <| irs_next_inst := 21; irs_next_var := 1;
        irs_used_inst_ids := 20 :: fn_ir_inst_ids mm_local_zero_fn;
        irs_used_vars := "formal_var_0" :: fn_ir_vars mm_local_zero_fn |> )
Proof
  EVAL_TAC
QED

Theorem mm_local_zero_output[local]:
  let bt = mm_local_probe_after mm_local_zero_fn 0 in
  let fn' = mm_local_zero_fn with fn_blocks := [FST bt] in
    fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
    ir_supply_covers_fn (SND bt) fn' /\
    fn_entry_label fn' = fn_entry_label mm_local_zero_fn
Proof
  EVAL_TAC
QED

Definition mm_local_copy_fn_def:
  mm_local_copy_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 MCOPY [Lit 128w; Lit 0w; Lit 32w] [];
       mk_inst 2 STOP [] []] |>]
End

Theorem mm_local_copy_input[local]:
  fn_inst_wf mm_local_copy_fn /\ wf_function mm_local_copy_fn /\
  wf_ssa mm_local_copy_fn /\
  ir_supply_covers_fn (mm_local_probe_supply mm_local_copy_fn) mm_local_copy_fn
Proof
  EVAL_TAC
QED

Theorem mm_local_copy_computed[local]:
  MAP (\i. (i.inst_id,i.inst_opcode,i.inst_operands,i.inst_outputs))
    (FST (mm_local_probe_after mm_local_copy_fn 3)).bb_instructions =
  [(20,MLOAD,[Lit 0w],["formal_var_0"]);
   (1,MSTORE,[Lit 128w; Var "formal_var_0"],[]);
   (2,STOP,[],[])]
Proof
  EVAL_TAC
QED

Theorem mm_local_copy_output[local]:
  let bt = mm_local_probe_after mm_local_copy_fn 3 in
  let fn' = mm_local_copy_fn with fn_blocks := [FST bt] in
    fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
    ir_supply_covers_fn (SND bt) fn' /\
    fn_entry_label fn' = fn_entry_label mm_local_copy_fn
Proof
  EVAL_TAC
QED

Definition mm_local_dload_fn_def:
  mm_local_dload_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 DLOAD [Lit 0w] ["a"];
       mk_inst 2 MSTORE [Lit 128w; Var "a"] [];
       mk_inst 3 DLOAD [Lit 32w] ["b"];
       mk_inst 4 MSTORE [Lit 160w; Var "b"] [];
       mk_inst 5 ASSIGN [Var "a"] ["retained"];
       mk_inst 6 STOP [] []] |>]
End

Theorem mm_local_dload_input[local]:
  fn_inst_wf mm_local_dload_fn /\ wf_function mm_local_dload_fn /\
  wf_ssa mm_local_dload_fn /\
  ir_supply_covers_fn (mm_local_probe_supply mm_local_dload_fn) mm_local_dload_fn
Proof
  EVAL_TAC
QED

Theorem mm_local_dload_computed[local]:
  MAP (\i. (i.inst_id,i.inst_opcode,i.inst_operands,i.inst_outputs))
    (FST (mm_local_probe_after mm_local_dload_fn 2)).bb_instructions =
  [(1,DLOAD,[Lit 0w],["a"]);
   (2,NOP,[],[]);
   (3,NOP,[],[]);
   (4,DLOADBYTES,[Lit 128w; Lit 0w; Lit 64w],[]);
   (5,ASSIGN,[Var "a"],["retained"]);
   (6,STOP,[],[])]
Proof
  EVAL_TAC
QED

Theorem mm_local_dload_output[local]:
  let bt = mm_local_probe_after mm_local_dload_fn 2 in
  let fn' = mm_local_dload_fn with fn_blocks := [FST bt] in
    fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
    ir_supply_covers_fn (SND bt) fn' /\
    fn_entry_label fn' = fn_entry_label mm_local_dload_fn
Proof
  EVAL_TAC
QED

Theorem mm_local_stage_correct:
  !fn0 supply index k bb sk fn bb' sk' fn'.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  FOLDL (\(b,t) phase. case phase of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) t b
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m t b)
    (EL index fn0.fn_blocks,supply)
    (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) sk bb
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m sk bb) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
  ir_supply_covers_fn sk' fn' /\
  fn_entry_label fn' = fn_entry_label fn0 /\
  (!fuel ctx eom s.
    fn_entry_state fn s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn s) /\
    ~(?err. run_function fuel ctx fn s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn s) (run_function fuel ctx fn' s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn' s))
Proof
  cheat
QED
