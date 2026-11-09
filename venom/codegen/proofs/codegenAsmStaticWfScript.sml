(*
 * Codegen's assembly is statically well formed for the symbolic machine:
 * labels are unique and never also data headers, every referenced label is
 * defined, the data segment holds no code addresses and sits at the end,
 * and the encoding fits.
 *)
Theory codegenAsmStaticWf
Ancestors
  codegenSymRel codegenAsmProgOk codegenEncodingWf codegen asmSymSem asmWf
  asmOptimizer unitShapeDefs stackPlanGen venomWf fnPlanCover

Theorem codegen_asm_static_wf:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  sym_unit_static_ok unit /\ codegen_ready unit.cu_context ==>
  asm_static_wf prog
Proof
  cheat
QED
