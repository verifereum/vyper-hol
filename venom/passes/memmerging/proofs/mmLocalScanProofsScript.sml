(* Each local merging phase with its actual original-DFG provenance. *)
Theory mmLocalScanProofs
Ancestors
  mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner
  venomWf stateEquiv rich_list

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
