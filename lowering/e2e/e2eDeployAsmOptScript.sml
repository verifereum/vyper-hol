(* Producers for the asm_opt_finalizer case of e2e_deploy_correctness.
 *
 * As for the runtime (e2eAsmOpt): the constructor's Venom run and the stages
 * S1-S6 are taken on opt_deploy_entry_state, the creation frame's entry
 * state (its accounts, call trace and GAS readings) with the unoptimized
 * layout: prog's code and labels followed by the constructor arguments.
 * codegen_correct_asm_opt then relates that Venom run to the shadow of the
 * creation frame, which runs the optimized code.  The deployment stages S1
 * are stated for a frame whose code is the unoptimized deploy code;
 * opt_deploy_frame gives one whose entry state is opt_deploy_entry_state up
 * to GAS readings and call outcomes, and deploy_unit_outcomes_free carries
 * the stages' facts across the call outcomes, which the call-free
 * constructor never reads.
 *
 * TOP-LEVEL: compile_vyper_deploy_phases_asm_opt,
 * compile_vyper_deploy_nonempty_asm_opt, opt_deploy_entry_state,
 * opt_deploy_frame, deploy_unit_outcomes_free,
 * opt_deploy_codegen_asm_entry_rel, opt_deploy_asm_frame_rel,
 * lower_vyper_deploy_unit_sym_src_ok.
 *)
Theory e2eDeployAsmOpt
Ancestors
  e2eAsmOpt e2eProducers e2eDeployDefs ctorDeployDefs deployFrameReplay
  e2eEntry codegenAsmOpt codegenSymRel codegenEntryRel asmFrameRel
  o1PipelineCorrect o1PassContract compilePhasesProps compileVyper codegen
  asmOptimizer contextRawReachable asmDataSuffixProps contextPlanLayoutProps
  loweringStateRelDefs vyperArith frameRel codegenRel callTrace
  ctorDeployLowering ctorDeployMemory ctorDeployDload memSafeRun frameObsStep
  deployOutcomesFreeDeploy deployOutcomesFreeTransport deployOutcomesFreeBoundary

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

(* compile_vyper_runtime_nonempty_asm_opt for the deployment code. *)
Theorem compile_vyper_deploy_nonempty_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  deploy_bc <> []
Proof
  cheat
QED

(* deploy_entry_state with prog's layout over es's code, which has prog'
   in front of the constructor arguments. *)
Definition opt_deploy_entry_state_def:
  opt_deploy_entry_state prog prog' cplan tops es =
    opt_entry_state prog prog' cplan es with vs_alloca_next := imm_len tops
End

(* A creation frame with the unoptimized deploy code whose entry state is
   opt_deploy_entry_state up to GAS readings and call outcomes: es with
   prog's code and its gas used up, so that its first step fails and it
   records no call. *)
(* A single frame whose gas is used up fails its first step, so it
   records no call and reads no gas. *)
Theorem exhausted_frame_obs_empty[local]:
  !ctxt' rb es.
  ctxt'.gasUsed = ctxt'.msgParams.gasLimit ==>
  call_trace (es with contexts := [(ctxt', rb)]) = [] /\
  gas_readings (es with contexts := [(ctxt', rb)]) = []
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `step (es with contexts := [(ctxt', rb)])` >>
  drule_then irule frameObsStepTheory.frame_obs_terminal >> disj1_tac >>
  qspec_then `es with contexts := [(ctxt', rb)]` mp_tac
    (REWRITE_RULE [vfmDecreasesGasTheory.decreases_gas_cred_def]
       vfmDecreasesGasTheory.decreases_gas_cred_step) >>
  asm_rewrite_tac[] >>
  simp[vfmDecreasesGasTheory.contexts_weight_def,
       vfmExecutionPropTheory.unused_gas_def] >>
  Cases_on `q` >> simp[pairTheory.LEX_DEF] >>
  Cases_on `r.contexts` >> simp[]
QED

Theorem opt_deploy_frame:
  !policy tops prog prog' runtime_bc rpolicy dunit dout cplan am tx es.
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_state_rel tops (assemble prog') am tx es ==>
  ?es_p. deploy_state_rel tops (assemble prog) am tx es_p /\
         gas_variant
           (opt_deploy_entry_state prog prog' cplan tops es with
              vs_outcomes := [])
           (deploy_entry_state prog cplan tops es_p)
Proof
  rw[deploy_state_rel_def] >>
  qexists_tac `es with contexts :=
    [(ctxt with <| gasUsed := ctxt.msgParams.gasLimit;
                   msgParams := (ctxt.msgParams with
                     <| code := assemble prog ++ args_bytes;
                        parsed := parse_code 0 FEMPTY
                                    (assemble prog ++ args_bytes) |>) |>, rb)]` >>
  qmatch_goalsub_abbrev_tac `es with contexts := [(ctxt_p, rb)]` >>
  `call_trace (es with contexts := [(ctxt_p, rb)]) = [] /\
   gas_readings (es with contexts := [(ctxt_p, rb)]) = []` by
    (irule exhausted_frame_obs_empty >> simp[Abbr`ctxt_p`]) >>
  conj_tac
  >- (qexistsl_tac [`ctxt_p`, `rb`, `args_bytes`] >>
      qpat_x_assum `call_trace _ = []` (fn th => REWRITE_TAC [th]) >>
      gvs[Abbr`ctxt_p`, vfmExecutionPropTheory.wf_state_def,
          vfmExecutionPropTheory.wf_context_def,
          vfmExecutionPropTheory.all_accounts_def,
          vfmExecutionPropTheory.stack_room_ok_def,
          vfmExecutionPropTheory.gas_stack_ok_def,
          vfmExecutionPropTheory.outputTo_consistent_stack_def,
          vfmExecutionPropTheory.outputTo_consistent_ctx_def,
          e2eDefsTheory.call_outcomes_ok_def]) >>
  simp[gas_variant_def, opt_deploy_entry_state_def, deploy_entry_state_def,
       opt_entry_state_def, e2eEntryTheory.entry_venom_state_def] >>
  qpat_x_assum `call_trace _ = []` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `gas_readings _ = []` (fn th => REWRITE_TAC [th]) >>
  gvs[Abbr`ctxt_p`, venomStateTheory.venom_state_component_equality,
      rich_listTheory.DROP_LENGTH_APPEND]
QED

(* deploy_unit_execution_correct, deploy_unit_memory_ok, deploy_unit_dload_ok
   and deploy_unit_dload_in_section for an entry state whose call outcomes
   are arbitrary: the constructor is call-free, so the deployment unit never
   reads them. *)
Theorem deploy_unit_outcomes_free:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant (vs with vs_outcomes := [])
      (deploy_entry_state prog cplan tops es)
    ==>
    (?marks.
       deploy_source_exempt tops
         (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
            [(NONE, tops)] []) \/
       ?fuel. deploy_venom_result_rel tops runtime_bc tx
                (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                   [(NONE, tops)] [])
                (run_context fuel dunit.cu_context vs)) /\
    ((!marks. ~deploy_source_exempt tops
                (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                   [(NONE, tops)] [])) ==>
     raw_unit_memory_ok dunit.cu_context vs /\
     ptr_discipline (imm_len tops) dunit.cu_context vs /\
     taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context vs /\
     (code_layout_valid vs ==>
      mem_inv dload_offset_ok dunit.cu_context vs /\
      mem_inv dload_headroom_ok dunit.cu_context vs /\
      mem_inv (\c f inst s. inst_dload_in_section inst s /\
                            s.vs_code = vs.vs_code /\
                            s.vs_data_section = vs.vs_data_section)
        dunit.cu_context vs))
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule_all deploy_entry_excludes_outcomes >> strip_tac >>
  `!fuel. run_context fuel dunit.cu_context vs =
    map_result_state (\t. t with vs_outcomes := vs.vs_outcomes)
      (run_context fuel dunit.cu_context (vs with vs_outcomes := []))` by
    (gen_tac >> drule_all run_context_entry_outcomes_replace >>
     disch_then (qspecl_then [`fuel`, `vs with vs_outcomes := []`, `vs.vs_outcomes`] mp_tac) >>
     simp[]) >>
  conj_tac
  >- (drule_all deploy_unit_execution_correct >> simp[] >>
      metis_tac[deploy_result_outcomes_replace]) >>
  strip_tac >>
  `!marks. ~deploy_source_exempt tops
    (load_contract NONE (gas_explicit marks (vs with vs_outcomes := []).vs_gas_readings)
      am tx [(NONE,tops)] [])` by simp[] >>
  `raw_unit_memory_ok dunit.cu_context (vs with vs_outcomes := []) /\
   ptr_discipline (imm_len tops) dunit.cu_context (vs with vs_outcomes := []) /\
   taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context
     (vs with vs_outcomes := [])` by
    (drule_all deploy_unit_memory_ok >> simp[]) >>
  conj_tac
  >- (drule_all raw_unit_memory_ok_outcomes_replace >>
      disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_all ptr_discipline_outcomes_replace >>
      disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_all taint_within_outcomes_replace >>
      disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]) >>
  strip_tac >>
  `code_layout_valid (vs with vs_outcomes := [])` by simp[] >>
  `mem_inv dload_offset_ok dunit.cu_context (vs with vs_outcomes := []) /\
   mem_inv dload_headroom_ok dunit.cu_context (vs with vs_outcomes := [])` by
    (drule_all deploy_unit_dload_ok >> simp[]) >>
  `mem_inv (\c f inst s. inst_dload_in_section inst s /\
      s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
      dunit.cu_context (vs with vs_outcomes := [])` by
    (drule_all deploy_unit_dload_in_section >> simp[]) >>
  conj_tac
  >- (drule_all dload_offset_ok_outcomes_replace >>
      disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_all dload_headroom_ok_outcomes_replace >>
      disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]) >>
  drule_all dload_in_section_outcomes_replace >>
  disch_then (qspec_then `vs.vs_outcomes` mp_tac) >> simp[]
QED

(* deploy_entry_state_ok's entry relation for opt_deploy_entry_state: the
   entry assembly state of the shadow frame relates to it for prog's
   layout. *)
Theorem shadow_root_single[local]:
  es.contexts = [(ctxt, rb)] ==>
  (shadow_root es).contexts =
    [(ctxt with msgParams updated_by
        (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>), rb)] /\
  (shadow_root es).txParams = es.txParams /\
  (shadow_root es).rollback = es.rollback /\
  (shadow_root es).originalAccounts = es.originalAccounts /\
  (shadow_root es).msdomain = es.msdomain /\
  call_trace (shadow_root es) = call_trace es /\
  gas_readings (shadow_root es) = gas_readings es
Proof
  strip_tac >>
  `frame_obs (shadow_root es) = frame_obs es` by
    (irule shadow_root_frame_obs >> simp[]) >>
  asm_rewrite_tac[call_trace_def, gas_readings_def] >>
  simp[shadow_root_def, shadow_root_contexts_def]
QED

Theorem opt_deploy_codegen_asm_entry_rel:
  !tops prog prog' am tx es cplan u.
  deploy_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u ==>
  codegen_asm_entry_rel cplan prog (opt_deploy_entry_state prog prog' cplan tops es)
    (entry_asm_state (opt_deploy_entry_state prog prog' cplan tops es)
       (shadow_root es))
Proof
  rpt strip_tac >> fs[deploy_state_rel_def] >>
  drule shadow_root_single >> strip_tac >>
  simp[codegenLabelDisciplinedTheory.codegen_asm_entry_rel_def, entry_asm_state_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, opt_deploy_entry_state_def,
       opt_entry_state_def, entry_venom_state_frame_fields,
       entry_venom_state_fresh] >>
  gvs[entry_venom_state_def, venomStateTheory.init_venom_state_def, contextCodegenRelTheory.context_memory_rel_def]
QED

(* The shadow frame runs prog''s code from the entry assembly state with
   that code. *)
Theorem opt_deploy_asm_frame_rel:
  !tops prog prog' am tx es cplan u.
  deploy_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog' <> [] ==>
  asm_frame_rel prog'
    (opt_deploy_entry_state prog prog' cplan tops es).vs_data_section
    (shadow_root es)
    (entry_asm_state (opt_deploy_entry_state prog prog' cplan tops es)
       (shadow_root es) with
       as_code := assemble prog' ++
         (opt_deploy_entry_state prog prog' cplan tops es).vs_data_section)
    (shadow_root es)
Proof
  rpt strip_tac >>
  `wf_state (shadow_root es)` by fs[deploy_state_rel_def, shadow_root_wf_state] >>
  fs[deploy_state_rel_def] >>
  drule shadow_root_single >> strip_tac >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[e2eDefsTheory.tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  simp[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
       opt_deploy_entry_state_def, opt_entry_state_def, data_suffix_assemble,
       asm_pc_to_offset_zero, entry_venom_state_frame_fields] >>
  gvs[entry_venom_state_def, venomStateTheory.init_venom_state_def, wordsTheory.w2n_n2w, listTheory.DROP_APPEND] >>
  rewrite_tac[GSYM CONJ_ASSOC]
QED

(* The deployment unit's source-side static facts: no CODESIZE, CODECOPY
   only from runtime_begin, no code_end label yet, a byte-only data segment,
   and runtime_begin among its headers. *)
Theorem lower_vyper_deploy_unit_sym_src_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  label_flow_ok dunit.cu_context /\
  (!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) dunit.cu_data_segment /\
  ((?fn inst. MEM fn dunit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") dunit.cu_data_segment)
Proof
  cheat
QED
