(*
 * Step 5 of the asm optimizer proof: the assembly codegen emits is
 * label_disciplined (asmSymSem) from codegen's entry state, the premise
 * the asm finalizer contract and the forward bridge need.
 *
 * The premises are codegen_entry_asm_sim's, the label-flow facts of the
 * unit (no CODESIZE; code_end pointers only copied or read by CODECOPY;
 * their offsets below 2^255; a byte-only data segment; INVOKE targets in
 * the context), every data label of the program in env with its bytes
 * from the code (asm_data_env_ok; asm_data_env gives one), and a run that
 * ends (Halt or Abort).  The symbolic run then ends with it
 * (symFnStep's sym_fn_sims_all), so it never misuses a label at any fuel
 * (sym_run_terminal_never_bad).
 *
 * TOP-LEVEL:
 *   codegen_label_disciplined
 *)
Theory codegenLabelDisciplined
Ancestors
  symFnStep symFnSimSpec codegenAsmStaticWf codegenSymRel codegenEntrySim
  codegenEntryRel asmSymBridge asmSymSem fnSimSpec contextCodegenRel
  codegenRel unitShapeDefs venomExecSemantics venomState

Theorem codegen_label_disciplined:
  !fuel rpolicy unit cp prog Inv vs es env.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_ok prog env vs.vs_code /\
    ((?vs'. run_context fuel unit.cu_context vs = Halt vs') \/
     (?a vs'. run_context fuel unit.cu_context vs = Abort a vs'))
    ==>
    label_disciplined env prog (entry_asm_state vs es)
Proof
  cheat
QED
