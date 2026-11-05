(*
 * The generated assembly has the shape the frame simulation needs.
 *
 * TOP-LEVEL:
 *   codegen_assembly_frame_prog_ok
 *)

Theory codegenAsmProgOk
Ancestors
  asmFrameRel codegenEncodingWf codegen unitShapeDefs asmWf asmSem
  symbolResolve

Theorem codegen_assembly_frame_prog_ok:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  asm_frame_prog_ok prog
Proof
  cheat
QED
