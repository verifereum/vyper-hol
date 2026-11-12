(*
 * The asm-to-EVM half of S7g's surplus bound, for any assembly program:
 * a frame related to an assembly state whose run is bounded (N steps,
 * memory below H) keeps D gas after each step before a RETURNDATACOPY,
 * given g gas, where g depends only on H, N and D.
 *
 * TOP-LEVEL:
 *   asm_frame_gas_surplus - the bound, generic in the program
 *)

Theory asmFrameSurplus
Ancestors
  asmFrameNext asmFrameGas frameStep asmRunBounded asmFrameRel frameGas
  vfmExecution vfmExecutionProp

(* Why it should hold.  Induction on N along the frame's own states:
   asm_frame_step_next steps the assembly and the frame together
   (frame_reaches_next / frame_reaches_last place every frame state of
   frame_inst_at on that chain), asm_run_bounded supplies each step's
   side conditions until a RETURNDATACOPY or a terminal step, and
   asm_frame_gas_step bounds each step's cost by frame_op_gas H, with a
   CALL leaving at least (gas - frame_op_gas H) DIV 64.  So
   g = G N with G 0 = frame_op_gas H + D and
   G (SUC k) = 64 * G k + frame_op_gas H + D (or any larger recurrence)
   works.  A RETURNDATACOPY state before s is excluded by the hypothesis. *)
Theorem asm_frame_gas_surplus:
  !H N D. ?g. !prog data es0 a e s op r s'.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
    wf_state e /\ g <= frame_gas_left e /\
    asm_run_bounded (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog H N a /\
    frame_inst_at e s op /\
    (!t. frame_inst_at e t ReturnDataCopy ==>
         ~RTC (\x y. LENGTH x.contexts >= LENGTH s.contexts /\
                     step x = (INL (), y)) t s) /\
    step_inst op s = (r, s') /\ LENGTH s'.contexts = LENGTH s.contexts
    ==>
    r <> INR (SOME OutOfGas) /\ D <= frame_gas_left s'
Proof
  cheat
QED

(* Lockstep corollary: a frame related to a bounded run of assembly with no
   RETURNDATACOPY never reaches a ReturnDataCopy opcode at its own depth.
   Generic in prog; codegen_no_returndatacopy is its codegen instance. *)
Theorem asm_frame_no_returndatacopy:
  !prog data es0 a e H N t.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
    asm_run_bounded (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog H N a /\
    ~MEM (AsmOp "RETURNDATACOPY") prog
    ==>
    ~frame_inst_at e t ReturnDataCopy
Proof
  cheat
QED
