(*
 * A halting terminator or a jump of FmpLowering's stage simulation, past
 * its point's restore: the target runs the same instruction to related
 * results.
 *
 * TOP-LEVEL:
 *   fmp_stage_sim_halt - STOP, RETURN, REVERT, SINK, SELFDESTRUCT, INVALID
 *   fmp_stage_sim_jump - JMP, JNZ, DJMP jump to the same label
 *)
Theory fmpStageTermSim
Ancestors
  fmpStageTermSimBasic fmpStageTermSimReturn
  fmpStageTermSimSelfdestruct fmpStageTermSimJump
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel o1LowerDloadShared
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst

(* Why: the halting state's shared parts agree up to D (ld_shared_agree);
   RETURN's payload is read through access_ok, so its untainted bytes
   agree; REVERT's payload dead_result_rel doesn't compare; SELFDESTRUCT's
   beneficiary is an untainted scalar. *)
Theorem fmp_stage_sim_halt:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  MEM inst.inst_opcode [STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?t1. r' = OK t1 /\ t1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt t1)
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = RETURN`
  >- (irule fmp_stage_return_result >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = SELFDESTRUCT`
  >- (irule fmp_stage_selfdestruct_result >> metis_tac[]) >>
  irule fmp_stage_basic_result >> fs[listTheory.MEM] >> metis_tac[]
QED

(* Why: a jump's condition and table index are untainted scalars with no
   provenance (taint_ok, fn_static_ptr_ok), so they agree; the labels are
   literal; and the frames agree on the current block. *)
Theorem fmp_stage_sim_jump:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?lbl. r = OK (jump_to lbl s) /\
        !k'. step_inst k' C' inst t = OK (jump_to lbl t)
Proof
  MATCH_ACCEPT_TAC fmp_stage_jump_result
QED
