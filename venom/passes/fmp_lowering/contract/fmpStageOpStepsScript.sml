(*
 * FmpLowering's stage simulation, one source instruction at a time: an
 * ordinary instruction, a halting terminator, a jump, and the tail of a
 * revert forwarding.  The block simulation (fmpStageBlockSim) chains them
 * with the restores, DALLOCA, RETPC_PARAM and INVOKE steps.
 *
 * TOP-LEVEL:
 *   fmp_stage_op_step        - an ordinary instruction, to the next index
 *   fmp_stage_halt_step      - a halting terminator, to related halts
 *   fmp_stage_jump_step      - a jump, to the same label
 *   fmp_stage_revert_forward - a revert forwarding's RETURNDATACOPY, to
 *                              related ends of the block
 *)
Theory fmpStageOpSteps
Ancestors
  fmpStageOpFrame fmpStageOpSimPure fmpStageOpSimMem fmpStageTermSim fmpStageControl
  fmpStageOpBase fmpStageRel ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst list

(* Why: the target runs the same instruction (fmp_stage_kept_inst, at the
   control map's index, since an ordinary instruction is no reclaim
   point), to a related local result (fmpStageOpSimPure, fmpStageOpSimMem), from which the
   relation at the next index follows (fmp_stage_op_frame). *)
Theorem fmp_stage_op_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?inst' k' r'.
    active_inst fn' inst' t /\ step_inst k' C' inst' t = r' /\
    case r of
      OK s1 =>
        ?t1. r' = OK t1 /\
          fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
            (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
            (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
            (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  cheat
QED

(* Why: the target runs the same terminator, past its point's restore
   (fmp_stage_kept_inst), to a related halt (fmp_stage_sim_halt). *)
Theorem fmp_stage_halt_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [JMP; JNZ; DJMP; RET] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?inst' k' r'.
    active_inst fn' inst' t /\ step_inst k' C' inst' t = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?t1. r' = OK t1 /\ t1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt t1)
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  cheat
QED

(* Why: as for halts, with fmp_stage_sim_jump. *)
Theorem fmp_stage_jump_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?lbl inst'.
    r = OK (jump_to lbl s) /\ active_inst fn' inst' t /\
    !k'. step_inst k' C' inst' t = OK (jump_to lbl t)
Proof
  cheat
QED

(* Why: a revert forwarding copies the callee's revert data and reverts
   with it, with only ASSIGNs in between, none of them reclaim points: the
   target runs the same instructions, and both runs end in a revert (or
   abort alike before it), which dead_result_rel relates whatever the
   memory holds.  The copy may write anywhere (access_ok exempts it), so
   no relation holds between the instructions. *)
Theorem fmp_stage_revert_forward:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ in_revert_forward fn s /\
  inst.inst_opcode = RETURNDATACOPY /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block k C bb s = r /\ terminates r ==>
  ?fn' bb' k' r'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block k' C' bb' t = r' /\ dead_result_rel D r r'
Proof
  cheat
QED
