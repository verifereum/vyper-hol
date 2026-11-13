(* Sufficient gas for the identity finalizer: the cases from which the
 * sufficient-gas companions of vyper_call_correct and e2e_deploy_correctness
 * are joined.  The companions themselves are stated separately.
 *
 * vyper_call_correct holds for any gas, so it lets the frame run out of gas.
 * Here: some amount of gas is enough.  With at least that much more gas,
 * our frame runs out of gas only once it has run a RETURNDATACOPY.  That
 * exemption is needed: when a call fails, the compiled code copies the
 * callee's revert data and reverts with it, and a callee holding all but
 * 1/64 of our gas can return more data than the rest pays to copy, or
 * leave us too little for the REVERT after the copy.
 *
 * Contents:
 *   vyper_call_gas_sufficient_identity -- the call case, identity finalizer
 *   e2e_deploy_gas_sufficient_identity -- the deployment case
 *   call_state_rel_add_frame_gas -- call_state_rel ignores the frame's gas
 *
 * Only gas starvation is ruled out: a StackOverflow outcome, which
 * frame_resource_starved also allows, does not depend on gas.
 *
 * The identity finalizer's case is composed from three planned
 * admissions: S1b (lower_vyper_runtime_unit_run_bounded), S6b
 * (run_venom_pipeline_run_bounded) and S7g (codegen_gas_sufficient).
 *
 * Deployment runs in one creation frame and the constructor makes no calls,
 * so there is no RETURNDATACOPY exemption: with enough gas the creation
 * frame does not end in OutOfGas, unless the code it deposits is longer than
 * max_code_size, which the EVM rejects with OutOfGas at any gas.  Its
 * identity case is composed from S1b-d (deploy_unit_run_bounded), S6b and
 * S7g-d (deploy_frame_gas_sufficient).
 *
 * The call theorem, S1b and S6b rely on the lowering's bounded ABI decoder
 * checking each range before it loads from it, as it does today.
 *)
Theory e2eGasSufficient
Ancestors
  e2eCorrectness e2eDefs e2eProducers e2eEntry unitTransformDefs
  ptrDiscipline lowerDloadDefs e2eComposition
  o1PipelineCorrect o1PassContract contextCodegenRel
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource passSimulationDefs
  codegenCorrectness immutableCodeLayout frameOutcome frameGas
  venomRunBounded unitMemInv
  asmOptimizer callTrace
  e2eDeployCorrectness e2eDeployDefs ctorDeployDefs ctorDeployLowering
  ctorDeployFrame ctorDeployShape ctorDeployDefsReach ctorDeployInitcode
  ctorDeployEntry ctorDeployDead ctorDeployRunBounded ctorDeployImmBudget
  ctorDeployMemoryFrontier deployUnitExecution deployUnitExitSafe
  vfmExecution vfmExecutionProp vfmContext list rich_list pair

(* ===== add_frame_gas keeps the call's state relation ===== *)

(* Only gas fields change, so the account maps and the return data the
   two bounds range over are the same. *)
Theorem add_frame_gas_bounded:
  !B g es.
    (balance_bounded B (add_frame_gas g es) <=> balance_bounded B es) /\
    (returndata_bounded (add_frame_gas g es) <=> returndata_bounded es)
Proof
  rpt gen_tac >> Cases_on `es.contexts`
  >- simp[add_frame_gas_def]
  >> PairCases_on `h` >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  simp[vfmTotalBalanceTheory.balance_bounded_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmReturndataBoundTheory.returndata_bounded_def,
       add_frame_gas_fields, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP]
QED

Theorem call_state_rel_add_frame_gas:
  !tops bc am tx g es.
    call_state_rel tops bc am tx es ==>
    call_state_rel tops bc am tx (add_frame_gas g es)
Proof
  rw[call_state_rel_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  simp[add_frame_gas_wf_state, add_frame_gas_fields, add_frame_gas_bounded] >>
  fs[]
QED

(* The creation frame's relation at the new gas: only gas fields change. *)
Theorem deploy_state_rel_add_frame_gas:
  !tops bc am tx g es.
    deploy_state_rel tops bc am tx es ==>
    deploy_state_rel tops bc am tx (add_frame_gas g es)
Proof
  rw[deploy_state_rel_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  qexistsl_tac [`ctxt with msgParams updated_by (\p. p with gasLimit updated_by $+ g)`,
                `rb`, `args_bytes`] >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    (simp[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]) >>
  fs[add_frame_gas_wf_state, add_frame_gas_fields, add_frame_gas_bounded]
QED

(* ===== The call cases ===== *)

(* vyper_call_correct's hypotheses.  The two that range over the call
   trace, and so over what the callees do with the gas they get, are
   stated at the new gas.  ~source_exempt is S3's: on the exempt inputs
   (malformed data to a dynamic abi_decode) the compiled code may read at
   any offset, so no gas is enough.  It is stated for every list of GAS
   observations, since the source run S4 relates the compiled run to may
   read other GAS values than the EVM run does. *)
Theorem vyper_call_gas_sufficient_identity:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
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
      (!obs. ~source_exempt tops
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  (* S1b, S6b and S7g, at bounds that hold for every entry state *)
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`] mp_tac
    lower_vyper_runtime_unit_run_bounded >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`0`, `rpolicy`, `unit`, `out`, `cplan`, `fuel`] mp_tac
    run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the entry state at the new gas, as in vyper_call_correct *)
  `call_state_rel tops (assemble prog) am tx (add_frame_gas g' es)` by
    simp[call_state_rel_add_frame_gas] >>
  `call_outcomes_ok am tx (MAP SND (call_trace (add_frame_gas g' es)))` by
    metis_tac[call_state_rel_call_outcomes_ok] >>
  `wf_state es` by fs[call_state_rel_def] >>
  qpat_x_assum `call_state_rel _ _ _ _ es` kall_tac >>
  qpat_x_assum `valid_vyper_call _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC [GSYM (Q.SPECL [`g'`, `es`] add_frame_gas_calldata)] >>
  strip_tac >>
  drule_all entry_venom_state_initial_venom_state_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  drule_all entry_venom_state_initial_ctx_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qspecl_then [`prog`, `cplan`, `add_frame_gas g' es`] assume_tac
    entry_venom_state_o1_initial_state_ok >>
  drule_all generated_entry_code_layout_shape >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qabbrev_tac `vs = entry_venom_state prog cplan (add_frame_gas g' es)` >>
  `vs.vs_outcomes = MAP SND (call_trace (add_frame_gas g' es)) /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_call_ctx.cc_calldata =
     buffer_to_list (FST (HD (add_frame_gas g' es).contexts)).msgParams.data`
    by simp[Abbr`vs`, entry_venom_state_def] >>
  `o1_run_state_ok vs` by
    (fs[o1_run_state_ok_def] >>
     gvs[Abbr`vs`, entry_venom_state_def, call_state_rel_def]) >>
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
           (gas_explicit marks vi.vs_gas_readings) am tx)` by simp[] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >>
        fs[o1_run_state_ok_def]) >>
     drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
     `mem_inv dload_offset_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_offset_ok >> simp[] >>
        qexistsl_tac [`am`, `ret`, `rpolicy`, `tops`, `tx`] >> gvs[]) >>
     `mem_inv dload_headroom_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
     gvs[Abbr`D`] >>
     qpat_x_assum `!vs. _ ==> terminates (run_context fuel _ _)` irule >>
     simp[]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _` irule >>
     simp[] >> metis_tac[]) >>
  (* S4's input state, for the codegen obligations *)
  qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`] mp_tac
    run_venom_pipeline_correct >>
  impl_tac >- simp[] >> strip_tac >>
  `ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs` by
    (qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` irule >> metis_tac[]) >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `prog = _` kall_tac >>
  qpat_x_assum `!g' Inv vs es. _` irule >> simp[] >>
  qexistsl_tac [`Inv`, `vs`] >> simp[]
QED


(* ===== The deployment cases ===== *)

(* One gas variant of the creation frame's entry state, under the top's
   finite storage guard and non-exemption: the unit's certificate at its
   own marks is on its exit arm, which gives the S3 facts S4 and S6b ask
   for (through ctorDeployMemoryFrontier's bridges), the pointer taint
   within the dead set of the run's observed horizon H, and the unit's
   result there. *)
Theorem deploy_variant_exit_facts[local]:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vi.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vi (deploy_entry_state prog cplan tops es) /\
    code_layout_valid vi /\
    (!gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs) /\
    (!obs. ~deploy_source_exempt tops
       (load_contract NONE obs am tx [(NONE, tops)] []))
    ==>
    ?H gobs efuel.
      raw_unit_memory_ok dunit.cu_context vi /\
      ptr_discipline (imm_len tops) dunit.cu_context vi /\
      taint_within (deploy_dead H tops runtime_bc am tx) dunit.cu_context vi /\
      mem_inv dload_offset_ok dunit.cu_context vi /\
      mem_inv dload_headroom_ok dunit.cu_context vi /\
      deploy_venom_result_rel H tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context efuel dunit.cu_context vi)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `~ctx_has_dalloca dunit.cu_context` by
    metis_tac[deploy_unit_shape_ok, o1_source_unit_ok_no_dalloca] >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `vi.vs_outcomes = MAP SND (call_trace es)` by
    (drule gas_variant_outcomes >>
     simp[deploy_entry_state_def, entry_venom_state_def]) >>
  `deploy_unit_execution_correct tops runtime_bc am tx dunit vi` by
    (irule deploy_unit_execution_correct >> metis_tac[]) >>
  pop_assum (qx_choose_then `marks` assume_tac o
             REWRITE_RULE [deploy_unit_execution_correct_def]) >>
  qabbrev_tac `gobs = gas_explicit marks vi.vs_gas_readings` >>
  `load_contract (SOME vi.vs_outcomes) gobs am tx [(NONE, tops)] [] =
   load_contract NONE gobs am tx [(NONE, tops)] []` by
    metis_tac[load_contract_call_free] >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `tx`, `dunit`, `vi`]
    mp_tac deploy_unit_exit_safe_runs >>
  impl_tac >- (simp[Abbr`gobs`] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`func`, `efuel`] strip_assume_tac) >>
  qabbrev_tac `H = storage_trace_horizon
                     (deploy_storage_trace (SOME vi.vs_outcomes) gobs am tx tops)` >>
  `func = fn /\ lbl = "__deploy"` by gvs[] >> gvs[] >>
  qexistsl_tac [`H`, `gobs`, `efuel`] >> gvs[] >>
  rpt conj_tac
  >- (qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `fn`,
                   `"__deploy"`, `vi`] mp_tac lowered_unit_raw_memory_ok_from >>
      simp[] >> disch_then irule >> decide_tac)
  >- (qspecl_then [`deploy_dead H tops runtime_bc am tx`, `imm_len tops`,
                   `dunit.cu_context`, `"__deploy"`, `fn`, `"__deploy"`, `vi`]
        mp_tac lowered_unit_ptr_taint >> simp[])
  >- (qspecl_then [`deploy_dead H tops runtime_bc am tx`, `imm_len tops`,
                   `dunit.cu_context`, `"__deploy"`, `fn`, `"__deploy"`, `vi`]
        mp_tac lowered_unit_ptr_taint >> simp[])
  >- (irule lowered_unit_dload_offset_ok >> metis_tac[])
  >> irule lowered_unit_dload_headroom_ok_from >> metis_tac[]
QED

(* e2e_deploy_correctness's hypotheses.  The constructor run's finite
   storage guard depends on the run's GAS observations, so it is stated at
   the new gas for every list of them, as is the exemption premise, the
   deploy counterpart of the call's.  S6b takes the all-dead set: each gas
   variant of the entry state has its own observed horizon, and no common
   finite one exists.  S4 takes its input state before the dead set, which
   is then the dead set at that state's own horizon, so the source's
   result relation carries over to the compiled unit. *)
Theorem e2e_deploy_gas_sufficient_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      (!gs. deploy_storage_ok tops am tx
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~deploy_source_exempt tops
         (load_contract NONE obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases >> strip_tac >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  (* S1b-d, S6b and S7g-d, at bounds that hold for every creation frame *)
  (* S1b-d: one fuel for every run that ends; each variant's run ends on its
     exit arm (below) *)
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  drule_all deploy_unit_fns_fuel_stable >> strip_tac >>
  drule_all run_context_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `cplan`, `fuel'`, `M`] mp_tac
    deploy_frame_gas_sufficient >>
  impl_tac >- fs[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the creation frame at the new gas *)
  `deploy_state_rel tops deploy_bc am tx (add_frame_gas g' es)` by
    simp[deploy_state_rel_add_frame_gas] >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  qabbrev_tac `vs = deploy_entry_state prog cplan tops (add_frame_gas g' es)` >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_outcomes = MAP SND (call_trace (add_frame_gas g' es))` by
    simp[Abbr`vs`, deploy_entry_state_def, entry_venom_state_def] >>
  qabbrev_tac `Du = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf Du` by simp[Abbr`Du`, dead_wf_def] >>
  (* every gas variant of vs: its own exit arm *)
  `!vi. gas_variant vi vs ==>
        ?H gobs efuel.
          raw_unit_memory_ok dunit.cu_context vi /\
          ptr_discipline (imm_len tops) dunit.cu_context vi /\
          taint_within (deploy_dead H tops runtime_bc am tx)
            dunit.cu_context vi /\
          mem_inv dload_offset_ok dunit.cu_context vi /\
          mem_inv dload_headroom_ok dunit.cu_context vi /\
          deploy_venom_result_rel H tops runtime_bc tx
            (load_contract NONE gobs am tx [(NONE, tops)] [])
            (run_context efuel dunit.cu_context vi)` by
    (rpt strip_tac >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >>
        fs[o1_run_state_ok_def]) >>
     irule deploy_variant_exit_facts >> fs[Abbr`vs`] >>
     metis_tac[]) >>
  `!vi. gas_variant vi vs ==>
        terminates (run_context fuel dunit.cu_context vi)` by
    (rpt strip_tac >>
     qpat_x_assum `!vi. gas_variant vi vs ==> ?H gobs efuel. _` drule >>
     strip_tac >>
     qpat_x_assum `!s f. terminates _ ==> _` irule >> qexists_tac `efuel` >>
     metis_tac[deploy_venom_result_rel_terminates]) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _` irule >>
     qexists_tac `Du` >> simp[] >> rpt strip_tac >>
     TRY (simp[Abbr`Du`, taint_within_def] >> NO_TAC) >>
     metis_tac[]) >>
  (* S4's input state, picked before its dead set *)
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`] mp_tac
    run_venom_pipeline_correct_all_dead >>
  impl_tac >- simp[] >> strip_tac >>
  `?H gobs efuel.
     raw_unit_memory_ok dunit.cu_context vs_in /\
     ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
     taint_within (deploy_dead H tops runtime_bc am tx) dunit.cu_context vs_in /\
     mem_inv dload_offset_ok dunit.cu_context vs_in /\
     mem_inv dload_headroom_ok dunit.cu_context vs_in /\
     deploy_venom_result_rel H tops runtime_bc tx
       (load_contract NONE gobs am tx [(NONE, tops)] [])
       (run_context efuel dunit.cu_context vs_in)` by metis_tac[] >>
  qabbrev_tac `D = deploy_dead H tops runtime_bc am tx` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs` by metis_tac[] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  (* what the compiled constructor returns *)
  `terminates (run_context efuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?vfuel. dead_result_rel D (run_context efuel dunit.cu_context vs_in)
             (run_context vfuel dout.po_unit.cu_context vs)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract NONE gobs am tx [(NONE, tops)] [])` by fs[] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `tx`, `gobs`,
               `load_contract NONE gobs am tx [(NONE, tops)] []`,
               `run_context efuel dunit.cu_context vs_in`,
               `run_context vfuel dout.po_unit.cu_context vs`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- fs[Abbr`D`] >> strip_tac >>
  qpat_x_assum `!g' am tx es Inv. _`
    (qspecl_then [`g'`, `am`, `tx`, `es`, `Inv`] mp_tac) >>
  impl_tac
  >- (fs[Abbr`vs`] >>
      qexistsl_tac [`H`, `load_contract NONE gobs am tx [(NONE, tops)] []`,
                    `vfuel`] >>
      fs[]) >>
  simp[]
QED
