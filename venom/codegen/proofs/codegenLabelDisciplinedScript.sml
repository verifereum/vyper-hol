(*
 * Step 5 of the asm optimizer proof: the assembly codegen emits is
 * label_disciplined (asmSymSem) from codegen's entry state, the premise
 * the asm finalizer contract and the forward bridge need.
 *
 * The entry is stated over a Venom state vs and an assembly state as
 * (codegen_asm_entry_rel), not over an EVM frame: codegen_entry_asm_sim's
 * initial_ctx_rel ties the frame's code to assemble prog and its oracle
 * lists to vs at once, while the optimized program's run needs prog's
 * code and labels with another frame's oracle lists.  initial_ctx_rel
 * gives codegen_asm_entry_rel for entry_asm_state.
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
 *   codegen_asm_entry_rel         - the assembly entry state of codegen's
 *                                   program for Venom state vs
 *   initial_ctx_codegen_asm_entry_rel - initial_ctx_rel gives it for
 *                                   entry_asm_state
 *   codegen_entry_asm_sim_state   - codegen_entry_asm_sim from it
 *   codegen_label_disciplined     - the program is label_disciplined from it
 *)
Theory codegenLabelDisciplined
Ancestors
  symFnStep symFnSimSpec codegenAsmStaticWf codegenSymRel codegenEntrySim
  codegenEntryRel asmSymBridge asmSymSem fnSimSpec frameRel
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomState

(* The assembly state as starts codegen's program prog for the Venom
   state vs at the context's entry: at PC 0 with an empty stack, memory
   and shared state related, and vs a fresh, non-static entry state whose
   labels are prog's offsets. *)
Definition codegen_asm_entry_rel_def:
  codegen_asm_entry_rel cp prog vs as <=>
    as.as_pc = 0 /\ as.as_stack = [] /\
    ~vs.vs_halted /\ ~vs.vs_call_ctx.cc_static /\
    vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (!l. FLOOKUP vs.vs_labels l =
         OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    shared_state_rel vs as
End

Theorem initial_ctx_codegen_asm_entry_rel:
  !cp prog ctx vs es.
    initial_ctx_rel cp prog ctx vs es ==>
    codegen_asm_entry_rel cp prog vs (entry_asm_state vs es)
Proof
  cheat
QED

Theorem codegen_entry_asm_sim_state:
  !fuel rpolicy unit cp prog Inv vs as.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    codegen_asm_entry_rel cp prog vs as
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog))
                 (build_offset_to_pc prog) prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog n as = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog n as = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
Proof
  cheat
QED

Theorem codegen_label_disciplined:
  !fuel rpolicy unit cp prog Inv vs as env.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    codegen_asm_entry_rel cp prog vs as /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_ok prog env vs.vs_code /\
    ((?vs'. run_context fuel unit.cu_context vs = Halt vs') \/
     (?a vs'. run_context fuel unit.cu_context vs = Abort a vs'))
    ==>
    label_disciplined env prog as
Proof
  cheat
QED
