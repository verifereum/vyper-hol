(*
 * The assembly step against the EVM frame's own next state, for the
 * sufficient-gas theorem S7g: asm_frame_step's continuing case names the
 * state the frame reaches next (frame_next), not just one with the same
 * run_call result, and a step that doesn't continue ends the frame.
 *
 * TOP-LEVEL:
 *   asm_frame_step_next - every instruction without an assembly error
 *)

Theory asmFrameNext
Ancestors
  asmFrameRun asmFrameRel frameStep asmSem asmWf symbolResolve
  vfmExecution

(* Why it should hold: asm_frame_step (asmFrameRun) is this with the
   continuing case weakened to run_call es1 = run_call es, and its step
   lemmas build es1 as step's result (frame_continue_transplant,
   asmFrameLocalStep) or as the callee run's return t, with
   step s = (INL (),v) and run_call v = SOME (INL (),t)
   (asm_frame_call_enter_step_ok, asmFrameCallStep; the create and
   delegate steps likewise).  Its starving cases come from the step
   itself raising OutOfGas or StackOverflow, which ends the frame; the
   assembly halts, reverts or faults only at STOP, RETURN, REVERT,
   INVALID, an out-of-range RETURNDATACOPY, an oversized CREATE and
   SELFDESTRUCT, each of which ends the EVM frame too.
   Either the frame ends with es's step (it starves, or the assembly
   halts, reverts or faults), or the assembly step continues and the
   relation holds again at the frame's next state. *)
Theorem asm_frame_step_next:
  !prog data es0 as es.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
    as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
    (!e. asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
           (EL as.as_pc prog) as <> AsmError e) ==>
    frame_last es \/
    ?as1 es1.
      asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        (EL as.as_pc prog) as = AsmOK as1 /\
      frame_next es es1 /\ asm_frame_rel prog data es0 as1 es1
Proof
  rpt strip_tac >>
  drule_all (cj 2 asm_frame_step) >> simp[]
QED
