(* Deployment certificates and source hypotheses at the raw unit's entry. *)
Theory e2eDeployRawFmp
Ancestors
  e2eDeployDefs ctorDeployDefs ctorDeployInitcode ctorDeployInitcodeAsm
  deployUnitExecution deployUnitExecutionBoundary compileVyper o1PassContract lowerDloadDefs e2eEntry
  asmOptimizer vyperTypeContractSoundness vyperCompiler stackPlanGen list arithmetic
  ctorDeployEntryTransport ctorDeployBodyJoint ctorDeployShape deployUnitExecutionTransport

(* A successful asm_opt compilation exposes the deployment unit's phases, with
   the final assembly optimizer's output as the deployed code. *)
Theorem compile_vyper_deploy_phases_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy dunit dout prog prog' cplan.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    deploy_bc = assemble prog'
Proof
  simp[compile_vyper_def, deploy_phases_def] >> strip_tac >>
  drule compilePhasesPropsTheory.compile_vyper_with_success_phases >> strip_tac >>
  gvs[codegenTheory.finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  qpat_x_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP e2eProducersTheory.codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

Theorem deploy_source_ok_opt_code:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_source_ok tops am tx ==>
    deploy_source_ok tops am
      (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
Proof
  rpt strip_tac >>
  drule_all deploy_bc_size_bounded >> strip_tac >>
  `?args_bytes.
     (FST (HD es.contexts)).msgParams.code = assemble prog' ++ args_bytes /\
     constructor_args_encode tops tx args_bytes` by
    gvs[deploy_state_rel_def] >>
  drule_all constructor_args_size_bounded >> strip_tac >>
  gvs[deploy_source_ok_def, deploy_typing_ok_def, call_tx_well_typed_def,
      opt_deploy_entry_state_def, opt_entry_state_def, LENGTH_APPEND] >>
  decide_tac
QED

Theorem deploy_raw_fmp_exists:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan es.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) ==>
    ?fmp:bytes32.
      w2n (opt_deploy_entry_state prog prog' cplan tops es).vs_initial_fmp <=
        w2n fmp /\
      w2n fmp < 2 ** 254 /\
      imm_len tops + unit_alloca_budget dunit.cu_context +
        32 * ctx_dload_count dunit.cu_context <= w2n fmp
Proof
  rpt strip_tac >>
  `imm_len tops + unit_alloca_budget dunit.cu_context +
     32 * ctx_dload_count dunit.cu_context < 2 ** 254` by
    (qpat_x_assum `deploy_phases _ _ _ _` mp_tac >>
     simp[deploy_phases_def] >> strip_tac >>
     qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
     simp[lower_vyper_deploy_unit_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
     drule run_deploy_lowering_static_headroom >>
     simp[immSectionDeadTheory.imm_len_def,
          ctx_dload_count_def, rich_listTheory.FILTER_FLAT,
          rich_listTheory.LENGTH_FLAT, listTheory.MAP_MAP_o,
          combinTheory.o_DEF] >> decide_tac) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[deploy_phases_def, generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  qabbrev_tac `n = MAX cplan.cp_initial_fmp
    (imm_len tops + unit_alloca_budget dunit.cu_context +
       32 * ctx_dload_count dunit.cu_context)` >>
  `n < 2 ** 254` by simp[Abbr `n`, MAX_DEF] >>
  `n < dimword (:256) /\ cplan.cp_initial_fmp < dimword (:256)` by
    (fs[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  qexists_tac `n2w n` >>
  simp[opt_deploy_entry_state_def, opt_entry_state_def, entry_venom_state_def,
       wordsTheory.w2n_n2w] >>
  fs[Abbr `n`, MAX_DEF] >> decide_tac
QED

(* The deploy gas link's certificate premise at the raw free-memory pointer. *)
Theorem deploy_unit_execution_correct_raw_fmp:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es fmp.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_source_ok tops am tx ==>
    ?shadow_ctx. !vs.
      raw_variant fmp vs (opt_deploy_entry_state prog prog' cplan tops es) ==>
      ?marks. deploy_unit_execution_correct_with shadow_ctx marks
        tops runtime_bc am
        (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
        dunit vs
Proof
  rpt strip_tac >>
  `deploy_source_ok tops am
    (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)` by
    (drule_all deploy_source_ok_opt_code >> simp[]) >>
  `tx.function_name = "__init__"` by gvs[deploy_state_rel_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule deploy_reconstructed_entry >>
  disch_then (qspecl_then [`prog`, `cplan`] (qx_choose_then `es0` strip_assume_tac)) >>
  drule_all deploy_unit_execution_correct_fixed_shadow >>
  disch_then (qx_choose_then `shadow_ctx` assume_tac) >>
  qexists_tac `shadow_ctx` >> rpt strip_tac >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    gvs[raw_variant_def, gas_variant_def, opt_deploy_entry_state_def,
        opt_entry_state_def, entry_venom_state_def,
        venomStateTheory.venom_state_component_equality] >>
  `call_outcomes_ok am
     (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code)
     vs.vs_outcomes` by
    (qpat_assum `deploy_state_rel tops (assemble prog') am tx es`
       (mp_tac o MATCH_MP deploy_state_rel_call_outcomes_ok) >>
     simp[e2eDefsTheory.call_outcomes_ok_def]) >>
  qabbrev_tac `s = deploy_entry_state prog cplan tops es0 with
    <|vs_outcomes := vs.vs_outcomes; vs_gas_readings := vs.vs_gas_readings|>` >>
  qpat_x_assum `!outs vs. call_outcomes_ok _ _ outs /\ gas_variant _ _ ==> _`
    (qspecl_then [`vs.vs_outcomes`, `s`] mp_tac) >>
  (impl_tac >- simp[Abbr `s`, gas_variant_def,
                     venomStateTheory.venom_state_fupdfupds]) >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  drule_all deploy_certificate_raw_fmp_transport >>
  disch_then (qspecl_then [`fmp`, `fmp`, `vs.vs_call_entry_fmp`] assume_tac) >>
  `(s with <|vs_fmp := fmp; vs_initial_fmp := fmp;
             vs_call_entry_fmp := vs.vs_call_entry_fmp|>) = vs` by
    gvs[Abbr `s`, raw_variant_def, gas_variant_def,
        venomStateTheory.venom_state_component_equality] >>
  qexists_tac `marks` >> gvs[]
QED

(* Raw-pointer safety and gas-mask boundary used inside the deploy gas link. *)
Theorem deploy_raw_fmp_focus_mask_entry:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es
   vs_out fmp shadow_ctx func.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (!vs. raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func ==>
    ?markf. !gs.
      deploy_unit_execution_correct_with shadow_ctx (markf gs)
        tops runtime_bc am (tx with code := vs_out.vs_code) dunit
        (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                       vs_initial_fmp := fmp|>) /\
      ?D f extra.
        dead_wf D /\
        (fin = asm_opt_finalizer ==>
           !fn inst s.
             raw_reachable
               (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                              vs_initial_fmp := fmp|>)
               dunit.cu_context fn inst s /\
             gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
               (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                              vs_initial_fmp := fmp|>) s ==>
             inst_dload_in_section inst s) /\
        o1_safe_upto D (imm_len tops) (MIN (LENGTH (markf gs)) (LENGTH gs))
          dunit.cu_context
          (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                         vs_initial_fmp := fmp|>) /\
        MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx)
          (gas_events_blocks f dunit.cu_context func
            (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                           vs_initial_fmp := fmp; vs_prev_bb := NONE;
                           vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) =
          markf gs ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  `!gs. ?marks.
     deploy_unit_execution_correct_with shadow_ctx marks
       tops runtime_bc am (tx with code := vs_out.vs_code) dunit
       (vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                      vs_initial_fmp := fmp|>)` by
    (gen_tac >> first_x_assum irule >>
     simp[raw_variant_def, gas_variant_def,
          venomStateTheory.venom_state_component_equality]) >>
  pop_assum mp_tac >> CONV_TAC (LAND_CONV SKOLEM_CONV) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  qexists_tac `markf` >> gen_tac >>
  conj_tac >- simp[] >>
  qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (qspec_then `gs` assume_tac) >>
  drule_at (Pat `deploy_unit_execution_correct_with _ _ _ _ _ _ _ _`)
    deploy_certificate_raw_entry_boundary >>
  simp[] >> disch_then irule >> simp[] >>
  conj_tac >- (qexists_tac `fmp` >> gvs[]) >>
  metis_tac[]
QED
