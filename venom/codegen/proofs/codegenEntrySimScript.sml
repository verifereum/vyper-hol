(*
 * The Venom-to-assembly half of codegen_correct (S7): the context's run
 * from its entry is simulated by the generated assembly, started in the
 * entry assembly state of the EVM frame.
 *
 * TOP-LEVEL (CHEATED, a skeleton piece):
 *   codegen_entry_asm_sim - run_context against asm_steps from
 *                           entry_asm_state
 *)

Theory codegenEntrySim
Ancestors
  codegenEntryRel venomToAsmProps frameRel codegenRel contextCodegenRel
  codegen asmSem venomExecSemantics venomState

(* Why it should hold: run_context runs the entry function (the first
   function: initial_ctx_rel and the planner's layout put its region at
   assembly index 0) with run_function, so this is gen_fn_simulation for
   it, with no return address (entry_fn_no_ret, from
   codegen_context_obligations, also rules out IntRet).  entry_asm_state
   meets fn_entry_state_rel: initial_ctx_rel gives the empty variable map,
   the parameter count (stack_params_rel with no variables: none, and
   an empty stack), the memory relation and the shared fields.  The
   remaining gen_fn_simulation premises come from codegen_context_obligations,
   codegen_reachability_package and initial_ctx_rel's label agreement. *)
Theorem codegen_entry_asm_sim:
  !fuel rpolicy unit cp prog Inv vs es.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmHalt as' /\
         venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
Proof
  cheat
QED
