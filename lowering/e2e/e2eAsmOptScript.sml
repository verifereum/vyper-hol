(* Producers for the asm_opt_finalizer case of the top theorems.
 *
 * The Venom run and the stages S1-S6 are taken on the entry state of the
 * unoptimized layout: the frame es with its code swapped for the
 * unoptimized runtime followed by the same immutables section
 * (opt_entry_frame). codegen_correct_asm_opt then relates that Venom run to
 * the EVM frame es, which runs the optimized code.
 *
 * TOP-LEVEL: compile_vyper_runtime_phases_asm_opt, opt_entry_frame,
 * opt_entry_initial_venom_state_rel, opt_entry_initial_ctx_rel,
 * opt_entry_code_layout_valid, opt_entry_fields, o1_output_label_flow_ok,
 * o1_pipeline_memory_obligations_raw, o1_output_code_end_offset_ok, o1_output_sym_unit_static_ok.
 *)
Theory e2eAsmOpt
Ancestors
  e2eProducers e2eDefs e2eEntry immutableCodeLayout codegenAsmOpt
  codegenSymRel o1PipelineCorrect compilePhasesProps compileVyper codegen
  asmOptimizer contextCodegenRel unitShapeDefs vyperLoweringCorrect
  contextPlanLayoutProps unitMemInv stepWriteFootprint o1PassContract
  contextRawReachable

(* L1 for the optimizer: the runtime is the optimized assembly of the O1
   output's generated assembly. *)
Theorem compile_vyper_runtime_phases_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog prog' cp.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
           data_segment_asm out.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    assembly_target_safe rpolicy.rpol_target prog' /\
    runtime_bc = assemble prog'
Proof
  simp[compile_vyper_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  rename1 `lower_vyper_runtime_unit tops rpolicy = SOME unit` >>
  rename1 `run_venom_pipeline (K T) (K T) (K T)
             rpolicy o1_pipeline_spec unit = SOME out` >>
  qpat_x_assum `codegen_assembly rpolicy out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* The frame es with the unoptimized runtime prog in place of the optimized
   prog', followed by es's immutables section. *)
Definition opt_entry_frame_def:
  opt_entry_frame prog prog' es =
    frame_code_swap
      (assemble prog ++
       DROP (LENGTH (assemble prog')) (FST (HD es.contexts)).msgParams.code)
      es
End

(* entry_venom_state_initial_venom_state_rel on the swapped frame. *)
Theorem opt_entry_initial_venom_state_rel:
  !tops prog prog' am tx es cp.
  call_state_rel tops (assemble prog') am tx es ==>
  initial_venom_state_rel tops am tx
    (entry_venom_state prog cp (opt_entry_frame prog prog' es))
Proof
  cheat
QED

(* entry_venom_state_initial_ctx_rel on the swapped frame. *)
Theorem opt_entry_initial_ctx_rel:
  !tops prog prog' am tx es u cp.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog <> [] ==>
  initial_ctx_rel cp prog u.cu_context
    (entry_venom_state prog cp (opt_entry_frame prog prog' es))
    (opt_entry_frame prog prog' es)
Proof
  cheat
QED

(* generated_entry_code_layout_shape on the swapped frame. *)
Theorem opt_entry_code_layout_valid:
  !tops prog prog' am tx es cp policy unit.
  call_state_rel tops (assemble prog') am tx es /\
  codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit ==>
  code_layout_valid (entry_venom_state prog cp (opt_entry_frame prog prog' es))
Proof
  cheat
QED

(* The swapped frame's entry state reads everything but the code and the
   layout from es; its code is prog's followed by the section es's code
   has after prog'. *)
Theorem opt_entry_fields:
  !tops prog prog' am tx es cp vs.
  call_state_rel tops (assemble prog') am tx es /\
  vs = entry_venom_state prog cp (opt_entry_frame prog prog' es) ==>
    vs.vs_outcomes = MAP SND (call_trace es) /\
    vs.vs_gas_readings = gas_readings es /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_call_ctx.cc_calldata =
      buffer_to_list (FST (HD es.contexts)).msgParams.data /\
    vs.vs_fmp = vs.vs_initial_fmp /\ ~vs.vs_call_ctx.cc_static /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    (FST (HD es.contexts)).msgParams.code =
      assemble prog' ++ vs.vs_data_section /\
    (FST (HD es.contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD es.contexts)).msgParams.code /\
    frame_code_swap (assemble prog ++ vs.vs_data_section) es =
      opt_entry_frame prog prog' es
Proof
  cheat
QED

(* ===== Static facts of the O1 output the label discipline needs ===== *)

(* The O1 output reads code only through CODECOPY from runtime_begin or a
   code_end pointer, and never takes CODESIZE, for programs that do not
   read self.code. *)
Theorem o1_output_label_flow_ok:
  !tops rpolicy unit out.
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out ==>
  label_flow_ok out.po_unit.cu_context
Proof
  cheat
QED

(* o1_pipeline_memory_obligations with its invariant named: the states
   reachable from vs. *)
Theorem o1_pipeline_memory_obligations_raw:
  !out cp vs.
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_lowered_inv out.po_unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp
    ==>
    codegen_memory_obligations (raw_reachable vs) out.po_unit.cu_context cp /\
    codegen_reachability_package (raw_reachable vs) out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  drule o1_lowered_inv_fixed_pointer >> strip_tac >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  metis_tac[mem_inv_codegen_obligations, step_write_footprint_holds]
QED

(* Every code_end ADD's offset is below 2^255 in the states reachable from
   the O1 output's entry state. *)
Theorem o1_output_code_end_offset_ok:
  !tops rpolicy unit out cp vs.
  supported_program tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  generate_context_plan out.po_unit.cu_context = SOME cp /\
  o1_lowered_inv out.po_unit.cu_context vs /\
  code_layout_valid vs /\
  vs.vs_initial_fmp = n2w cp.cp_initial_fmp ==>
  code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context
Proof
  cheat
QED

(* The O1 output's data segment holds bytes only, runtime_begin is a data
   header if read, and INVOKE targets are functions. *)
Theorem o1_output_sym_unit_static_ok:
  !tops rpolicy unit out.
  supported_program tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out ==>
  sym_unit_static_ok out.po_unit
Proof
  cheat
QED
