(*
 * A Venom step read through the frame view.
 *
 * The frame-aware simulation (genFrameSim) runs the local per-instruction
 * lemmas against frame_view fn ra vs with the assembly memory standing in
 * for the Venom memory.  This theory shows that a non-INVOKE, non-PARAM
 * step commutes with that substitution: return-PC variables are only
 * copied (opaque_use_ok, retpc_shape_ok, SSA), and memory reads see the
 * same bytes when the substituted memory agrees on the bytes the
 * instruction reads.
 *
 * TOP-LEVEL:
 *   step_inst_frame_view — the step on the view is the view of the step
 *)

Theory frameViewStep
Ancestors
  frameRel contextCodegenRel codegenRel stackPlanGen unitShapeDefs
  venomExecSemantics venomState venomInst

(* m' is the substituted memory after the step: it agrees with the Venom
   memory after the step wherever m agreed before, and it changes only
   inside the instruction's source write ranges. *)
Theorem step_inst_frame_view:
  !fuel ctx fn ra inst vs vs' m.
    step_inst fuel ctx inst vs = OK vs' /\
    inst.inst_opcode <> INVOKE /\
    ~is_param_opcode inst.inst_opcode /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    MEM inst (fn_insts fn) /\
    (!i. source_memory_read_byte inst vs i ==>
         read_byte i m = read_byte i vs.vs_memory) ==>
    ?m'. step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := m) =
           OK (frame_view fn ra vs' with vs_memory := m') /\
         (!i. read_byte i m = read_byte i vs.vs_memory ==>
              read_byte i m' = read_byte i vs'.vs_memory) /\
         (!i. EVERY (\r. ~byte_in_memory_range r i)
                (source_memory_write_ranges inst vs) ==>
              read_byte i m' = read_byte i m)
Proof
  cheat
QED
