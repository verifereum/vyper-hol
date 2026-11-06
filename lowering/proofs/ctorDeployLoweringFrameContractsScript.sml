Theory ctorDeployLoweringFrameContracts
Ancestors
  ctorDeployLoweringFramePayload ctorDeployLoweringFrameReachability

(* C1.semantic_contract_test: exact contract-closure audit, not a theorem
   asserting a supplier and not a counterexample.

   Desired observation: deploy_oracle_storage_payload requires EVERY outcome
   of the actual trace to have contract_storage_well_formed in the installed
   deploy_evaluation_context. The existing call_outcomes_ok hypothesis uses
   the old context. Final account agreement is not this observation.

   Candidate: codegenCorrectness.codegen_correct (admitted).
   Premise                              Producer / remaining obligation
   ------------------------------------ ----------------------------------
   generate_context_plan ... = SOME cp  deploy_phases_def
   codegen_assembly ... = SOME prog      deploy_phases_def
   unit_shape_ok dout.po_unit            codegen_assembly_success_shape
                                         from deploy_phases codegen success
   codegen_context_obligations Inv ...   e2eProducers.
                                         o1_pipeline_codegen_obligations
                                         (admitted), BUT requires semantic
                                         codegen_memory_obligations Inv.
   codegen_reachability_package Inv ...  o1_pipeline_memory_obligations gives
                                         both this and memory obligations
                                         from o1_lowered_inv and initial_fmp.
   o1_lowered_inv                        run_venom_pipeline_correct gives it
                                         conditionally on raw memory, ptr,
                                         taint, dload bounds for a reconstructed
                                         gas_variant input, plus structural
                                         O1 premises. deploy_unit_memory_ok
                                         and deploy_unit_dload_ok require
                                         ALL source gas schedules non-exempt;
                                         this is NOT a frozen frame premise.
   initial_ctx_rel                       deploy_entry_state_ok for shadow_root
                                         needs unit shape and code <= dimword DIV 2,
                                         from deploy_initcode_half_bounded.
                                         This is for the entry state, not every
                                         arbitrary gas_variant state.

   Even granting all these premises, codegen_correct concludes run_call and
   (frame_resource_starved OR venom_frame_rel). It is not a supplier:
   - frame_resource_starved_def only specifies an OutOfGas/StackOverflow
     frame_outcome; no bound on previous requests, outcomes or prefix PCs.
   - venom_frame_rel_def compares vs_requests with call_requests es ONLY
     in Halt. Revert and exceptional aborts carry frame_outcome only;
     Error is T. No branch asserts installed-context storage validity.
   - Therefore even an independently proved call-free successful Venom run
     would not discharge the resource-starved / revert / error cases. The
     conclusion does not give a prefix simulation or actual trace emptiness.
   This rejects the direct-wrapper route on its conclusion, independently
   of the still conditional O1 memory suppliers. It does not refute codegen.

   Candidate: deploy_ctor_entry_reaches_body (admitted, acyclic).
   Premises: deploy_phases, deploy_source_ok, deploy_state_rel, gas_variant,
   deploy_ctor_code and deploy_ctor_start are all frozen frame premises.
   Conclusion: related body-start stmt_state_rel, source/body identification,
   and forward run_from/run_context reachability. stmt_state_rel contains
   state_rel/allocation facts, not oracle_storage_ok. Forward reachability
   is not a claim about every actual EVM prefix, and supplies no storage
   property for an actual outcome.

   Rejected circular candidates (no imports attempted):
   - deploy_unit_execution_correct: ctorDeployLowering explicitly imports
     ctorDeployLoweringFrame, uses deploy_ctor_body_frame. Also returns a
     source exemption OR final Venom result, not actual trace safety.
   - e2e_deploy_correctness: uses ctorDeployLowering and the preceding result
     (and ctorDeployFrame). It requires compile_vyper identity finalization,
     runtime not starting EF and source support/typing/storage. Its conclusion
     retains the resource-starved disjunction and only relates final frames.
     It cannot be used to establish a premise of its own lowering dependency.

   Existing actual-trace consumer (already proved):
   call_trace_empty_guarded_step_invariant requires an invariant P initially,
   preserved only when ISL(FST(step t)), and exclusion of observable_call at
   original context depth. This handles exceptional terminal steps without
   incorrectly assuming a terminal state satisfies P. The payload boundary
   then makes storage validity vacuous if the actual trace is empty.

   One concrete missing producer-to-observation contract to test next (NOT
   asserted or proved here; in particular no claim that Inv automatically
   supplies machine-PC confinement):

     generate_context_plan unit.cu_context = SOME cp /\
     codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
     codegen_context_obligations Inv unit.cu_context cp /\
     codegen_reachability_package Inv unit.cu_context vs /\
     initial_ctx_rel cp prog unit.cu_context vs es /\
     (!fn inst s. Inv unit.cu_context fn inst s /\
         MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
         ~MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2])
     ==>
     !t. RTC (\s t. ISL (FST (step s)) /\ t = SND (step s)) es t /\
         LENGTH t.contexts = LENGTH es.contexts ==>
         ~observable_call (FST (HD t.contexts))

   The existing reachability_closed/Inv and initial_ctx_rel are the natural
   semantic invariant inputs. codegen_correct's comment explicitly says its
   current non-GAS EVM lemmas do not prove the trace-aware statement; its
   final-result disjunction cannot replace a prefix invariant. This proposed
   contract still needs validation of synthesized control flow, dynamic jumps,
   parsing and data confinement. Separately a deployment producer must prove
   the Inv opcode exclusion and its unconditional memory preconditions.
   This audit authorizes none of those proofs. No acyclic exact supplier was
   found among the inspected semantic contracts; no actual bad outcome was
   constructed. Stop for strategic review.
*)
