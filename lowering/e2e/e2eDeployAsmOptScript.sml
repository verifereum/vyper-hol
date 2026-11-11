(* Producers for the asm_opt_finalizer case of e2e_deploy_correctness.
 *
 * As for the runtime (e2eAsmOpt): the constructor's Venom run and the stages
 * S1-S6 are taken on the creation frame with the unoptimized deploy code in
 * place of the optimized one, followed by the same constructor arguments
 * (opt_entry_frame). codegen_correct_asm_opt then relates that Venom run to
 * the shadow of the real creation frame, which runs the optimized code.
 *
 * TOP-LEVEL: compile_vyper_deploy_phases_asm_opt,
 * compile_vyper_runtime_nonempty_asm_opt, opt_deploy_state_rel,
 * opt_deploy_entry_fields, o1_deploy_label_flow_ok,
 * o1_deploy_code_end_offset_ok, o1_deploy_sym_unit_static_ok.
 *)
Theory e2eDeployAsmOpt
Ancestors
  e2eAsmOpt e2eProducers e2eDeployDefs ctorDeployDefs deployFrameReplay
  e2eEntry codegenAsmOpt codegenSymRel o1PipelineCorrect compilePhasesProps
  compileVyper codegen asmOptimizer contextRawReachable

(* L1 of the deployment for the optimizer: the deploy code is the optimized
   assembly of the deployment unit's generated assembly. *)
Theorem compile_vyper_deploy_phases_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy dunit dout prog prog' cplan.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    deploy_bc = assemble prog'
Proof
  simp[compile_vyper_def, deploy_phases_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  qpat_x_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* compile_vyper_runtime_nonempty for the optimizer. *)
Theorem compile_vyper_runtime_nonempty_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  runtime_bc <> []
Proof
  cheat
QED

(* The creation frame with the unoptimized deploy code satisfies the
   deployment's state relation for that code: the account is fresh, so only
   the frame's code changes. *)
Theorem opt_deploy_state_rel:
  !tops prog prog' am tx es.
  deploy_state_rel tops (assemble prog') am tx es ==>
  deploy_state_rel tops (assemble prog) am tx (opt_entry_frame prog prog' es)
Proof
  cheat
QED

(* The swapped frame's entry state has prog's code followed by the
   constructor arguments, which follow prog' in es's code; swapping the
   shadow frame's code is the shadow of the swapped frame. *)
Theorem opt_deploy_entry_fields:
  !tops prog prog' am tx es cp.
  deploy_state_rel tops (assemble prog') am tx es ==>
  let vs = deploy_entry_state prog cp tops (opt_entry_frame prog prog' es) in
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    (FST (HD (shadow_root es).contexts)).msgParams.code =
      assemble prog' ++ vs.vs_data_section /\
    (FST (HD (shadow_root es).contexts)).msgParams.parsed =
      parse_code 0 FEMPTY (FST (HD (shadow_root es).contexts)).msgParams.code /\
    frame_code_swap (assemble prog ++ vs.vs_data_section) (shadow_root es) =
      shadow_root (opt_entry_frame prog prog' es)
Proof
  cheat
QED

(* ===== Static facts of the deployment unit's O1 output ===== *)

(* The constructor's O1 output reads code only through CODECOPY from
   runtime_begin or a code_end pointer, and never takes CODESIZE. *)
Theorem o1_deploy_label_flow_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\ ~program_reads_self_code tops ==>
  label_flow_ok dout.po_unit.cu_context
Proof
  cheat
QED

(* Every code_end ADD's offset is below 2^255 in the states reachable from
   the constructor's entry state. *)
Theorem o1_deploy_code_end_offset_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es ==>
  code_end_offset_ok (raw_reachable (deploy_entry_state prog cplan tops es))
    dout.po_unit.cu_context
Proof
  cheat
QED

(* The deployment unit's data segment holds bytes only, runtime_begin is a
   data header if read, and INVOKE targets are functions. *)
Theorem o1_deploy_sym_unit_static_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx ==>
  sym_unit_static_ok dout.po_unit
Proof
  cheat
QED
