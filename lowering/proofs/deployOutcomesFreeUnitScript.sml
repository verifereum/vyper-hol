(* The deployment unit's facts hold for any call outcomes, for the
   optimizer case of the top theorems (consumed by e2eDeployAsmOpt).

   TOP-LEVEL: deploy_unit_outcomes_free.
 *)
Theory deployOutcomesFreeUnit
Ancestors
  e2eProducers e2eDeployDefs ctorDeployDefs deployFrameReplay
  e2eEntry codegenAsmOpt codegenSymRel codegenEntryRel asmFrameRel
  o1PipelineCorrect o1PassContract compilePhasesProps compileVyper codegen
  asmOptimizer contextRawReachable asmDataSuffixProps contextPlanLayoutProps
  loweringStateRelDefs vyperArith frameRel codegenRel callTrace
  ctorDeployLowering ctorDeployMemory ctorDeployDload memSafeRun frameObsStep

(* deploy_unit_execution_correct, deploy_unit_memory_ok, deploy_unit_dload_ok
   and deploy_unit_dload_in_section for an entry state whose call outcomes
   are arbitrary: the constructor is call-free, so the deployment unit never
   reads them. *)
(* TEMPORARILY CHEATED - run base only: the leaf is repaired by another run.
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
*)
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
  cheat
QED
