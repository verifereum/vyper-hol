(* The sufficient-gas companions over the accepted finalizers: each joins
 * its identity case from e2eGasSufficient with its assembly-optimizer case,
 * as vyper_call_correct and e2e_deploy_correctness do.
 *
 * TOP-LEVEL:
 *   vyper_call_gas_sufficient -- the companion of vyper_call_correct
 *   e2e_deploy_gas_sufficient -- the companion of e2e_deploy_correctness
 *)
Theory e2eGasSufficientTop
Ancestors
  e2eGasSufficient e2eCorrectness e2eDefs e2eProducers e2eEntry
  unitTransformDefs ptrDiscipline lowerDloadDefs e2eComposition
  o1PipelineCorrect o1PassContract contextCodegenRel
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource passSimulationDefs
  codegenCorrectness frameGas frameStep venomRunBounded asmOptimizer callTrace
  e2eDeployCorrectness e2eDeployDefs ctorDeployDefs ctorDeployLowering
  ctorDeployFrame ctorDeployInitcode ctorDeployEntry ctorDeployDead
  ctorDeployCallFree o1OpcodeAbsence deployFrameReplay
  e2eAsmOpt e2eDeployAsmOpt codegenAsmOpt codegenGasAsmOpt codegenAsmProgOk
  vfmExecution vfmContext list rich_list pair

(* ===== The assembly optimizer's cases ===== *)

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code, as for
   vyper_call_correct_asm_opt.  The optimizer's gas side is
   codegen_gas_sufficient_asm_opt (codegenGasAsmOpt). *)
Theorem vyper_call_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?g. !g'.
      g <= g' /\
      call_outcomes_storage_ok am tx (MAP SND (call_trace (add_frame_gas g' es))) /\
      (!obs. ~gas_source_exempt tops
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  drule compile_vyper_runtime_nonempty_asm_opt >> strip_tac >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  (* the optimizer case's static facts of the O1 output *)
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  `label_flow_ok out.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok out.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  (* S1b, S6b and S7g-opt, at bounds that hold for every entry state *)
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`] mp_tac
    lower_vyper_runtime_unit_run_bounded >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`0`, `rpolicy`, `unit`, `out`, `cplan`, `fuel`] mp_tac
    run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient_asm_opt >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  `!vs. mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
          out.po_unit.cu_context vs` by
    metis_tac[o1_runtime_unit_create_size_ok] >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the entry state at the new gas, as in vyper_call_correct_asm_opt *)
  `call_state_rel tops (assemble prog') am tx (add_frame_gas g' es)` by
    simp[call_state_rel_add_frame_gas] >>
  `call_outcomes_ok am tx (MAP SND (call_trace (add_frame_gas g' es)))` by
    metis_tac[call_state_rel_call_outcomes_ok] >>
  `wf_state es` by fs[call_state_rel_def] >>
  qpat_x_assum `call_state_rel _ _ _ _ es` kall_tac >>
  qpat_x_assum `valid_vyper_call _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC [GSYM (Q.SPECL [`g'`, `es`] add_frame_gas_calldata)] >>
  strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `add_frame_gas g' es`,
               `cplan`] mp_tac opt_entry_initial_venom_state_rel >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `add_frame_gas g' es`,
               `cplan`, `out.po_unit`] mp_tac opt_entry_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `add_frame_gas g' es`,
               `cplan`, `out.po_unit`] mp_tac opt_entry_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `add_frame_gas g' es`,
               `cplan`, `rpolicy`, `out.po_unit`] mp_tac
    opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `add_frame_gas g' es`,
               `cplan`, `opt_entry_state prog prog' cplan (add_frame_gas g' es)`]
    mp_tac opt_entry_fields >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan (add_frame_gas g' es)` >>
  `o1_run_state_ok vs` by fs[o1_run_state_ok_def] >>
  qabbrev_tac `D = external_call_dead tx
                     (call_external (SOME vs.vs_outcomes) [] am tx)` >>
  `dead_wf D` by simp[Abbr`D`, external_call_dead_wf] >>
  (* every input state S4 may pick: a gas variant of vs *)
  `!vi. gas_variant vi vs ==>
        raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline 0 unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi /\
        mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                 s.vs_code = vi.vs_code /\
                                 s.vs_data_section = vi.vs_data_section)
          unit.cu_context vi /\
        terminates (run_context fuel unit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     `initial_venom_state_rel tops am tx vi` by
       (irule gas_variant_initial_venom_state_rel >> qexists_tac `vs` >>
        simp[]) >>
     `vi.vs_outcomes = vs.vs_outcomes` by
       (irule gas_variant_outcomes >> simp[]) >>
     `vi.vs_call_ctx = vs.vs_call_ctx` by
       (irule gas_variant_call_ctx >> simp[]) >>
     `valid_vyper_call tops tx vi.vs_call_ctx.cc_calldata ret /\
      call_outcomes_ok am tx vi.vs_outcomes /\
      !marks. ~source_exempt tops
        (call_external (SOME vi.vs_outcomes)
           (gas_explicit marks vi.vs_gas_readings) am tx)` by fs[gas_source_exempt_def] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >> simp[]) >>
     drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
     `mem_inv dload_offset_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_offset_ok >> simp[] >>
        qexistsl_tac [`am`, `ret`, `rpolicy`, `tops`, `tx`] >> gvs[]) >>
     `mem_inv dload_headroom_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
     `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
        unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_in_section >> simp[] >>
        qexistsl_tac [`am`, `ret`, `rpolicy`, `tops`, `tx`] >> gvs[]) >>
     gvs[Abbr`D`] >>
     qpat_x_assum `!vs. _ ==> terminates (run_context fuel _ _)` irule >>
     simp[]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _` irule >>
     simp[] >> metis_tac[]) >>
  (* S4's input state, for the codegen obligations *)
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (`LENGTH vs.vs_code <= dimword (:256) DIV 2` by
       (qpat_x_assum `code_layout_valid vs` mp_tac >>
        rewrite_tac[code_layout_valid_def] >> strip_tac >>
        first_assum ACCEPT_TAC) >>
     `0 < LENGTH (assemble prog)` by (Cases_on `assemble prog` >> fs[]) >>
     qpat_x_assum `0 < _` mp_tac >>
     qpat_x_assum `LENGTH vs.vs_code <= _` mp_tac >>
     qpat_x_assum `vs.vs_code = _` SUBST1_TAC >> simp[]) >>
  drule_all o1_pipeline_code_end_offset_ok >> strip_tac >>
  `ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
    (qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` irule >> metis_tac[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `!g' Inv vs es. _` irule >> simp[] >>
  qexistsl_tac [`raw_reachable vs`, `vs`] >> simp[]
QED

(* PLANNED ADMISSION: the constructor's Venom run does not depend on
   vs_outcomes, at any fuel.  The constructor is call-free, so its unit never
   reads them; the same fact as e2eDeployAsmOptTheory.deploy_unit_outcomes_free,
   in the form S6b's uniform fuel needs. *)
Theorem deploy_unit_run_outcomes_free:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   fuel vs os.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    (terminates (run_context fuel dunit.cu_context (vs with vs_outcomes := os)) <=>
     terminates (run_context fuel dunit.cu_context vs))
Proof
  cheat
QED

Theorem shadow_root_add_frame_gas_single[local]:
  es.contexts = [(c, rb)] ==>
  shadow_root (add_frame_gas g es) = add_frame_gas g (shadow_root es)
Proof
  rw[shadow_root_def, add_frame_gas_def, shadow_root_contexts_def,
     vfmContextTheory.execution_state_component_equality] >>
  simp[vfmContextTheory.context_component_equality,
       vfmContextTheory.message_parameters_component_equality]
QED

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code, as for
   e2e_deploy_correctness_asm_opt.  S7g-d's program-free tail
   (deploy_frame_gas_tail) over the optimized frame. *)
Theorem e2e_deploy_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      call_outcomes_storage_ok am tx (MAP SND (call_trace (add_frame_gas g' es))) /\
      EVERY (\co. contract_storage_well_formed (deploy_evaluation_context tops am tx)
                    (initial_state (am with <|accounts := co.co_accounts;
                                              tStorage := co.co_tStorage|>) []))
        (MAP SND (call_trace (add_frame_gas g' es))) /\
      (!obs. ~deploy_gas_source_exempt tops
         (load_contract NONE obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases_asm_opt >> strip_tac >>
  drule compile_vyper_runtime_nonempty_asm_opt >> strip_tac >>
  qpat_x_assum `deploy_bc = assemble prog'` SUBST_ALL_TAC >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan /\
   lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  (* the optimizer case's static facts of the constructor's O1 output *)
  drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  `o1_source_unit_ok dunit` by metis_tac[] >>
  `label_flow_ok dout.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok dout.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  (* no RETURNDATACOPY anywhere in the creation code *)
  drule_all lower_vyper_deploy_unit_call_free_entry >> strip_tac >>
  `!fn inst. MEM fn dout.po_unit.cu_context.ctx_functions /\
             MEM inst (fn_insts fn) ==> inst.inst_opcode <> RETURNDATACOPY` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`rpolicy`, `dunit`, `dout`, `efn`] mp_tac
       o1_pipeline_leaf_entry_no_returndatacopy >>
     impl_tac >- fs[] >> disch_then drule_all >> simp[]) >>
  drule_all codegen_assembly_no_returndatacopy >> strip_tac >>
  (* S1b-d, S6b and S7g-opt, at bounds that hold for every creation frame *)
  drule_all deploy_unit_run_bounded >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`,
               `code_deposit_cost * max_code_size`] mp_tac
    codegen_gas_surplus_asm_opt >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the creation frame at the new gas, and its root-shadowed frame *)
  `?c0 rb0. es.contexts = [(c0, rb0)] /\ wf_state es` by
    fs[deploy_state_rel_def] >>
  `deploy_state_rel tops (assemble prog') am tx (add_frame_gas g' es)` by
    (irule deploy_state_rel_add_frame_gas >> fs[]) >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  qabbrev_tac `es1 = add_frame_gas g' es` >>
  `?ctxt rb. es1.contexts = [(ctxt, rb)] /\
             ctxt.msgParams.outputTo = Code tx.target /\ wf_state es1` by
    fs[deploy_state_rel_def] >>
  `shadow_root es1 = add_frame_gas g' (shadow_root es)` by
    (simp[Abbr`es1`] >> irule shadow_root_add_frame_gas_single >> fs[]) >>
  `wf_state (shadow_root es1)` by simp[shadow_root_wf_state] >>
  `g' <= frame_gas_left (shadow_root es1)` by
    metis_tac[wf_state_frame_gas_left, shadow_root_wf_state] >>
  (* the Venom entry state, and a frame with prog's code for S1b-d *)
  drule_all opt_deploy_frame >> strip_tac >>
  qabbrev_tac `vs = opt_deploy_entry_state prog prog' cplan tops es1` >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  `o1_run_state_ok (vs with vs_outcomes := [])` by
    metis_tac[gas_variant_run_state_ok] >>
  `o1_run_state_ok vs` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
       code_layout_valid_def] >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_code = assemble prog ++ vs.vs_data_section` by
    simp[Abbr `vs`, opt_deploy_entry_state_def, opt_entry_state_def,
         entry_venom_state_def] >>
  qabbrev_tac `D = deploy_dead tops runtime_bc am tx` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  (* every input state S4 may pick: a gas variant of vs *)
  `!vi. gas_variant vi vs ==>
        raw_unit_memory_ok dunit.cu_context vi /\
        ptr_discipline (imm_len tops) dunit.cu_context vi /\
        taint_within D dunit.cu_context vi /\
        mem_inv dload_offset_ok dunit.cu_context vi /\
        mem_inv dload_headroom_ok dunit.cu_context vi /\
        mem_inv (\c f inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\
                              s.vs_data_section = vi.vs_data_section)
          dunit.cu_context vi /\
        terminates (run_context fuel dunit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     `gas_variant (vi with vs_outcomes := [])
        (deploy_entry_state prog cplan tops es_p)` by
       gvs[gas_variant_def, venomStateTheory.venom_state_component_equality] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >>
        fs[o1_run_state_ok_def]) >>
     `terminates (run_context fuel dunit.cu_context vi)` by
       (qspecl_then [`policy`, `tops`, `assemble prog`, `runtime_bc`,
                     `rpolicy`, `dunit`, `dout`, `prog`, `cplan`, `am`, `tx`,
                     `fuel`, `vi`, `[]`] mp_tac deploy_unit_run_outcomes_free >>
        impl_tac >- simp[] >> disch_then (SUBST1_TAC o GSYM) >>
        qpat_x_assum `!es vs. _ ==> terminates (run_context fuel _ _)` irule >>
        qexists_tac `es_p` >> simp[]) >>
     qspecl_then [`policy`, `tops`, `assemble prog`, `runtime_bc`, `rpolicy`,
                  `dunit`, `dout`, `prog`, `cplan`, `am`, `tx`, `es_p`, `vi`]
       mp_tac deploy_unit_outcomes_free >>
     impl_tac >- simp[] >> disch_then (mp_tac o CONJUNCT2) >>
     impl_tac >- simp[] >> simp[Abbr`D`]) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _` irule >>
     simp[] >> metis_tac[]) >>
  (* S4's input state, for the codegen obligations and the return value *)
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (`LENGTH vs.vs_code <= dimword (:256) DIV 2` by
       fs[o1_run_state_ok_def, code_layout_valid_def] >>
     `0 < LENGTH (assemble prog)` by (Cases_on `assemble prog` >> fs[]) >>
     qpat_x_assum `0 < _` mp_tac >>
     qpat_x_assum `LENGTH vs.vs_code <= _` mp_tac >>
     qpat_x_assum `vs.vs_code = _` (fn th => REWRITE_TAC [th]) >> simp[]) >>
  qspecl_then [`D`, `imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`] mp_tac
    o1_pipeline_code_end_offset_ok >>
  impl_tac >- simp[] >> strip_tac >>
  `raw_unit_memory_ok dunit.cu_context vs_in /\
   ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
   taint_within D dunit.cu_context vs_in /\
   mem_inv dload_offset_ok dunit.cu_context vs_in /\
   mem_inv dload_headroom_ok dunit.cu_context vs_in /\
   mem_inv (\c f inst s. inst_dload_in_section inst s /\
                         s.vs_code = vs_in.vs_code /\
                         s.vs_data_section = vs_in.vs_data_section)
     dunit.cu_context vs_in /\
   terminates (run_context fuel dunit.cu_context vs_in)` by metis_tac[] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) dout.po_unit.cu_context` by
    metis_tac[] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  (* what the constructor returns, through the optimizer-agnostic S1d *)
  `gas_variant (vs_in with vs_outcomes := [])
     (deploy_entry_state prog cplan tops es_p)` by
    gvs[gas_variant_def, venomStateTheory.venom_state_component_equality] >>
  qspecl_then [`policy`, `tops`, `assemble prog`, `runtime_bc`, `rpolicy`,
               `dunit`, `dout`, `prog`, `cplan`, `am`, `tx`, `es_p`, `vs_in`]
    mp_tac deploy_unit_outcomes_free >>
  impl_tac >- simp[] >> strip_tac >- metis_tac[] >>
  rename1 `run_context efuel dunit.cu_context vs_in` >>
  `terminates (run_context efuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?vfuel. dead_result_rel D (run_context efuel dunit.cu_context vs_in)
             (run_context vfuel dout.po_unit.cu_context vs)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx
         [(NONE, tops)] [])` by fs[deploy_gas_source_exempt_def] >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`,
               `gas_explicit marks vs_in.vs_gas_readings`] mp_tac
    deploy_venom_result_rel_dead >>
  simp[] >> disch_then drule_all >> strip_tac >>
  (* the optimized code's frame *)
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es1`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es1`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `sh = shadow_root es1` >>
  `!t. ~frame_inst_at sh t ReturnDataCopy` by
    (gen_tac >>
     qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`,
                  `M`, `raw_reachable vs`, `vs`, `sh`, `t`] mp_tac
       codegen_no_returndatacopy_asm_opt >>
     impl_tac >- simp[] >> simp[]) >>
  `!s op r s'. frame_inst_at sh s op /\ step_inst op s = (r, s') /\
               LENGTH s'.contexts = LENGTH s.contexts ==>
               r <> INR (SOME OutOfGas) /\
               code_deposit_cost * max_code_size <= frame_gas_left s'` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!g' Inv vs es s op r s'. _`
       (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `shadow_root es`,
                     `s`, `op`, `r`, `s'`] mp_tac) >>
     qpat_x_assum `sh = add_frame_gas _ _` (assume_tac o GSYM) >>
     impl_tac >- fs[] >> simp[]) >>
  qspecl_then [`vfuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs`, `vs`, `sh`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`r`, `es'`]
                (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qspecl_then [`es1`, `ctxt`, `rb`, `tx`, `tops`, `runtime_bc`,
               `load_contract NONE (gas_explicit marks vs_in.vs_gas_readings)
                  am tx [(NONE, tops)] []`,
               `run_context vfuel dout.po_unit.cu_context vs`,
               `r`, `es'`] mp_tac deploy_frame_gas_tail >>
  impl_tac >- (fs[Abbr `sh`] >> first_assum ACCEPT_TAC) >> simp[]
QED

(* ===== The companions ===== *)

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   vyper_call_correct's finalizer premises. *)
Theorem vyper_call_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx ret es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_outcomes_storage_ok am tx
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         (!obs. ~gas_source_exempt tops
            (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
               obs am tx)) /\
         (?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     call_outcomes_storage_ok am tx
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     (!obs. ~gas_source_exempt tops
        (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
           obs am tx))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
        ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all vyper_call_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
     drule_all vyper_call_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> metis_tac[]
QED

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   e2e_deploy_correctness's finalizer premises.  The RETURNDATACOPY escape is
   for constructors that call out; with today's call-free constructors only
   the code-size escape is taken. *)
Theorem e2e_deploy_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_outcomes_storage_ok am tx
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         EVERY (\co. contract_storage_well_formed
                       (deploy_evaluation_context tops am tx)
                       (initial_state (am with <|accounts := co.co_accounts;
                                                 tStorage := co.co_tStorage|>) []))
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         (!obs. ~deploy_gas_source_exempt tops
            (load_contract NONE obs am tx [(NONE, tops)] [])) /\
         r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     call_outcomes_storage_ok am tx
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     EVERY (\co. contract_storage_well_formed
                   (deploy_evaluation_context tops am tx)
                   (initial_state (am with <|accounts := co.co_accounts;
                                             tStorage := co.co_tStorage|>) []))
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     (!obs. ~deploy_gas_source_exempt tops
        (load_contract NONE obs am tx [(NONE, tops)] []))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (r = INR (SOME OutOfGas) ==>
        max_code_size < LENGTH runtime_bc + imm_len tops)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all e2e_deploy_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
     drule_all e2e_deploy_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[]
QED
