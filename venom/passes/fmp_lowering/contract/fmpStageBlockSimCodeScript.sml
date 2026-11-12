(*
 * Target-side facts for FmpLowering's block simulation (fmpStageBlockSim):
 * the lowered function's blocks are well formed with distinct labels, a
 * straight-line run of a block's non-final instructions is skipped by
 * exec_block, a related INVOKE has a target instruction to run, and a
 * related RET returns the source's values.
 *
 * TOP-LEVEL:
 *   fmp_stage_target_shape   - the lowered function is well formed
 *   exec_block_run_prefix    - exec_block skips a run of non-final insts
 *   fmp_target_run_exec_block - likewise for fmp_target_run
 *   fmp_stage_invoke_target  - a related INVOKE has a target instruction
 *   fmp_stage_ret_step       - a related RET returns the same values
 *)
Theory fmpStageBlockSimCode
Ancestors
  fmpStageOpBase fmpStageControl fmpStageRel runInstsProps venomWf
  o1PassContract ptrDiscipline contextCodegenRel analysisSimDefs
  venomExecSemantics venomState venomInst finite_map list

(* Why: the block simulation reads the target's next instruction off the
   lowered block (unique labels) and knows that only its last
   instruction is a terminator. *)
Theorem fmp_stage_target_shape:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ALL_DISTINCT (fn_labels fn') /\ EVERY bb_well_formed fn'.fn_blocks
Proof
  cheat
QED

(* Why: the restores, DALLOCA's expansion and the root run straight-line
   (run_insts); when an instruction of the block follows them, none of
   them is the block's terminator, so exec_block runs them the same way. *)
Theorem exec_block_run_prefix:
  !n fuel ctx bb s s1.
    bb_well_formed bb /\ s.vs_inst_idx + n < LENGTH bb.bb_instructions /\
    run_insts fuel ctx (TAKE n (DROP s.vs_inst_idx bb.bb_instructions)) s =
      OK s1 ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s1 with vs_inst_idx := s.vs_inst_idx + n)
Proof
  cheat
QED

Theorem fmp_target_run_exec_block:
  fmp_target_run fuel C' name t n t1 /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  EVERY bb_well_formed fn'.fn_blocks /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx + n < LENGTH bb'.bb_instructions ==>
  exec_block fuel C' bb' t = exec_block fuel C' bb' t1
Proof
  cheat
QED

(* Why: fmp_invoke_sim takes the target INVOKE as given; at a related
   point past the restores the target has an instruction there (the
   lowered INVOKE). *)
Theorem fmp_stage_invoke_target:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?inst'. active_inst fn' inst' t
Proof
  cheat
QED

(* Why: fmp_stage_result's RET case.  RET returns its front operands,
   which carry no provenance (no pointer reaches RET: ptr_use_static_ok)
   and no taint (taint_ok) and aren't the return pc (opaque_use_ok), so
   the relation makes them equal; RET changes no state. *)
Theorem fmp_stage_ret_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RET /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  step_inst k C inst s = IntRet ir s1 ==>
  s1 = s /\ ir.iret_adopt_fmp = NONE /\
  ?jr. (!k'. step_inst k' C' inst t = IntRet jr t) /\
       jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE
Proof
  cheat
QED
