(* Deployment certificates and source hypotheses at the raw unit's entry. *)
Theory e2eDeployRawFmp
Ancestors
  e2eDeployDefs ctorDeployDefs ctorDeployInitcode ctorDeployInitcodeAsm
  deployUnitExecution deployUnitExecutionBoundary compileVyper o1PassContract lowerDloadDefs e2eEntry
  asmOptimizer vyperTypeContractSoundness vyperCompiler stackPlanGen list arithmetic
  ctorDeployEntryTransport ctorDeployBodyJoint ctorDeployShape deployUnitExecutionTransport
  deployDynamicMemory loweringShapeSource ptrDiscipline callTrace unitTransformDefs venomState
  contextRawReachable ctorDeployLoweringCode ctorDeployBodyShadow ctorDeployLoweringEntryPrefix
  ctorDeployLoweringReturn ctorDeployMemoryRunMemPrefixLayout ctorDeployMemoryRunMemPrefixSource
  deployCtorPlainDefaults

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

Theorem deploy_raw_fmp_exists:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan es.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) ==>
    ?fmp:bytes32.
      w2n (opt_deploy_entry_state_own prog prog' cplan tops es).vs_initial_fmp <=
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
  simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def,
       wordsTheory.w2n_n2w] >>
  fs[Abbr `n`, MAX_DEF] >> decide_tac
QED

Theorem selected_raw_entry_fields[local]:
  raw_variant fmp vs (opt_deploy_entry_state_own prog prog' cplan tops es) ==>
  vs.vs_initial_fmp = fmp /\ vs.vs_outcomes = MAP SND (call_trace es) /\
  vs.vs_call_ctx = (opt_deploy_entry_state_own prog prog' cplan tops es).vs_call_ctx /\
  ~vs.vs_halted /\ vs.vs_allocas = FEMPTY /\
  raw_variant vs.vs_initial_fmp vs
    (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes)
Proof
  qmatch_goalsub_abbrev_tac `raw_variant fmp vs entry` >>
  strip_tac >>
  `vs.vs_initial_fmp = fmp /\ vs.vs_outcomes = entry.vs_outcomes /\
   vs.vs_call_ctx = entry.vs_call_ctx /\
   vs.vs_halted = entry.vs_halted /\ vs.vs_allocas = entry.vs_allocas` by
    fs[raw_variant_def, gas_variant_def, venomStateTheory.venom_state_component_equality] >>
  `entry.vs_outcomes = MAP SND (call_trace es) /\
   ~entry.vs_halted /\ entry.vs_allocas = FEMPTY` by
    simp[Abbr `entry`, opt_deploy_entry_state_own_def, opt_entry_state_own_def,
         entry_venom_state_def, init_venom_state_def] >>
  gvs[raw_variant_def, gas_variant_def, venomStateTheory.venom_state_component_equality]
QED

Theorem selected_raw_entry_rejecting_value[local]:
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  raw_variant fmp vs (opt_deploy_entry_state_own prog prog' cplan tops es) /\
  (!mut nr fbody am_c es0.
    ~deploy_ctor_start tops am tx (mut,nr,fbody,am_c,es0)) ==>
  vs.vs_call_ctx.cc_callvalue <> 0w /\ ~vs.vs_halted /\
  vs.vs_allocas = FEMPTY /\ allocas_below_fmp vs
Proof
  strip_tac >> drule selected_raw_entry_fields >> strip_tac >>
  drule_all ctor_prefix_source_obstruction >> strip_tac >>
  `gas_variant (opt_deploy_entry_state_own prog prog' cplan tops es)
    (opt_deploy_entry_state_own prog prog' cplan tops es with
      vs_outcomes := (opt_deploy_entry_state_own prog prog' cplan tops es).vs_outcomes)` by
    simp[gas_variant_def] >>
  drule_all ctor_prefix_entry_value >>
  fs[allocas_below_fmp_def, raw_variant_def, gas_variant_def, venom_state_component_equality]
QED

(* Replay constructor execution at the same FMP chosen for the raw
   gas and memory proofs. The constructor-free entry uses the FMP
   transport for a unit without dynamic allocations. *)
Theorem deploy_unit_execution_correct_selected_raw_fmp:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es fmp.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_source_ok tops am tx /\
    LENGTH (call_trace es) < 2 ** 64 /\
    w2n (opt_deploy_entry_state_own prog prog' cplan tops es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp ==>
    ?shadow_ctx. !vs.
      raw_variant fmp vs (opt_deploy_entry_state_own prog prog' cplan tops es) ==>
      ?marks. deploy_unit_execution_correct_with shadow_ctx marks
        tops runtime_bc am tx dunit vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_relocated_data_layout >> strip_tac >>
  `IS_SOME (FLOOKUP (lo_reloc prog prog') "runtime_begin")` by simp[] >>
  `?exts ints fb cfo. classify_functions tops = (exts, ints, fb, cfo)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `cfo`
  >- (qexists_tac `dunit.cu_context` >> rpt strip_tac >>
      qabbrev_tac `s = opt_deploy_entry_state_own prog prog' cplan tops es with
        vs_gas_readings := vs.vs_gas_readings` >>
      `gas_variant s (opt_deploy_entry_state_own prog prog' cplan tops es
          with vs_outcomes := s.vs_outcomes)` by
        simp[Abbr `s`, gas_variant_def, venom_state_fupdfupds] >>
      drule_all deploy_no_ctor_correct_with >> strip_tac >>
      `~deploy_dalloca_form_occurs expr_raw_shape_root tops` by
        simp[deploy_dalloca_form_occurs_def] >>
      drule_all deploy_unit_no_dalloca_static >> strip_tac >>
      drule_all deploy_unit_o1_shape_ok >> strip_tac >>
      drule_all deploy_certificate_raw_fmp_transport >>
      disch_then (qspecl_then [`fmp`, `fmp`, `vs.vs_call_entry_fmp`] assume_tac) >>
      `(s with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                 vs_call_entry_fmp := vs.vs_call_entry_fmp|>) = vs` by
        gvs[Abbr `s`, raw_variant_def, gas_variant_def,
            venomStateTheory.venom_state_component_equality] >>
      qexists_tac `[]` >> fs[]) >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  drule_all deploy_ctor_body_shadow >> strip_tac >>
  `supported_program tops /\ supported_program_deploy tops` by
    fs[deploy_source_ok_def] >>
  drule_all deploy_ctor_original_entry_shape >> strip_tac >>
  qexists_tac `shadow_ctx` >> rpt strip_tac >>
  drule selected_raw_entry_fields >> strip_tac >>
  `call_outcomes_ok am tx vs.vs_outcomes` by
    (drule deploy_state_rel_call_outcomes_ok >> simp[]) >>
  reverse (Cases_on `?mut nr' body' am_c es0.
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0)`)
  >- (`!mut nr' body' am_c es0.
          ~deploy_ctor_start tops am tx (mut, nr', body', am_c, es0)` by metis_tac[] >>
      drule_all selected_raw_entry_rejecting_value >> strip_tac >>
      qexists_tac `[]` >> drule_all deploy_ctor_prefix_fail_with_fields >>
      simp[]) >>
  pop_assum strip_assume_tac >>
  `ctx_has_dalloca dunit.cu_context ==>
    !fn inst st. raw_reachable vs dunit.cu_context fn inst st ==> dalloca_no_wrap inst st` by
    (strip_tac >>
     `deploy_dalloca_form_occurs expr_raw_shape_root tops` by
       metis_tac[deploy_unit_no_dalloca_static] >>
     qspecl_then [`fin`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
       `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`,
       `opt_deploy_entry_state_own prog prog' cplan tops es`, `vs`, `fmp`]
       mp_tac deploy_entry_raw_no_wrap >>
     impl_tac >- fs[deploy_source_ok_def] >> metis_tac[]) >>
  `ctx_has_dalloca dunit.cu_context ==>
    imm_len tops + unit_alloca_budget dunit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> fs[] >> decide_tac) >>
  rename1 `compile_stmts _ _ _ (MAP gas_shadow_stmt stmts) _ = _` >>
  drule_all deploy_ctor_plain_defaults_shadow_env >> strip_tac >>
  `compile_stmts (gas_shadow_env T cenv) NoLoop NoneT
     (MAP gas_shadow_stmt stmts) shadow_sa = ((),shadow_sb)` by simp[] >>
  drule_all deploy_ctor_body_joint_raw_with >> simp[]
QED

(* Raw-pointer safety and gas-mask boundary used inside the deploy gas link. *)
Theorem deploy_raw_fmp_focus_mask_entry:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es
   vs_out fmp shadow_ctx func.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
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
  rpt conj_tac >> TRY (qexists_tac `fmp`) >> fs[] >> metis_tac[]
QED
