(* Deployment certificates and source hypotheses at the raw unit's entry. *)
Theory e2eDeployRawFmp
Ancestors
  e2eDeployDefs ctorDeployDefs ctorDeployInitcode ctorDeployInitcodeAsm
  deployUnitExecution compileVyper o1PassContract lowerDloadDefs e2eEntry
  asmOptimizer vyperTypeContractSoundness vyperCompiler stackPlanGen list arithmetic

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
      unit_alloca_budget dunit.cu_context +
        32 * ctx_dload_count dunit.cu_context <= w2n fmp
Proof
  rpt strip_tac >>
  `unit_alloca_budget dunit.cu_context +
     32 * ctx_dload_count dunit.cu_context < 2 ** 254` by
    (qpat_x_assum `deploy_phases _ _ _ _` mp_tac >>
     simp[deploy_phases_def] >> strip_tac >>
     qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
     simp[lower_vyper_deploy_unit_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
     drule run_deploy_lowering_static_headroom >>
     simp[ctx_dload_count_def, rich_listTheory.FILTER_FLAT,
          rich_listTheory.LENGTH_FLAT, listTheory.MAP_MAP_o,
          combinTheory.o_DEF] >> decide_tac) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[deploy_phases_def, generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  qabbrev_tac `n = MAX cplan.cp_initial_fmp
    (unit_alloca_budget dunit.cu_context +
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

(* ADMISSION: moves the deploy certificate to any call outcomes, for a call-free constructor.
   Waits for its proof. *)
Theorem deploy_unit_execution_correct_with_outcomes:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   shadow_ctx marks vs outs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    tx.function_name = "__init__" /\
    deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
      dunit vs ==>
    deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx
      dunit (vs with vs_outcomes := outs)
Proof
  cheat
QED

(* ADMISSION: the deploy gas link's certificate premise at the raw free-memory pointer.
   Waits for its proof. *)
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
  cheat
QED

(* ADMISSION: the raw-pointer safety and gas-mask boundary used inside the deploy gas link's proof.
   Waits for its proof. *)
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
    unit_alloca_budget dunit.cu_context +
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
  cheat
QED
