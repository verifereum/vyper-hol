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
  ctorDeployEntry ctorDeployMemory ctorDeployDload ctorDeployDead
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

(* The creation frame's relation, at the new gas, from the old one and its
   two call-trace clauses, which range over what the run does with the gas. *)
Theorem deploy_state_rel_add_frame_gas:
  !tops bc am tx g es.
    deploy_state_rel tops bc am tx es /\
    call_outcomes_storage_ok am tx (MAP SND (call_trace (add_frame_gas g es))) /\
    EVERY (\co. contract_storage_well_formed (deploy_evaluation_context tops am tx)
                  (initial_state (am with <|accounts := co.co_accounts;
                                            tStorage := co.co_tStorage|>) []))
      (MAP SND (call_trace (add_frame_gas g es)))
    ==>
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

(* ===== The gas theorems' exemptions ===== *)

(* The correctness exemptions, plus a source run that stops on an oversized
   CREATE initcode: the EVM answers that CREATE with OutOfGas at every gas
   limit (EIP-3860), so no gas is enough. *)
Definition gas_source_exempt_def:
  gas_source_exempt tops
    (src : (value + exception) # abstract_machine # call_request list) <=>
    source_exempt tops src \/
    FST src = INR (Error (RuntimeError "create initcode too large"))
End

Definition deploy_gas_source_exempt_def:
  deploy_gas_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    deploy_source_exempt tops src \/
    src = INR (Error (RuntimeError "create initcode too large"))
End

(* ===== The call cases ===== *)

(* PLANNED ADMISSION: the runtime unit S7g runs reaches no oversized CREATE.
   supported_program's body_stmt_safe excludes CreateTarget, so the lowering
   emits no CREATE or CREATE2 and O1 keeps them absent; the premise then
   holds at every state. *)
Theorem o1_runtime_unit_create_size_ok:
  !tops rpolicy unit out vs.
    supported_program tops /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out
    ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s) out.po_unit.cu_context vs
Proof
  cheat
QED

(* vyper_call_correct's hypotheses.  The two that range over the call
   trace, and so over what the callees do with the gas they get, are
   stated at the new gas.  ~gas_source_exempt is S3's ~source_exempt (on
   the exempt inputs, malformed data to a dynamic abi_decode, the compiled
   code may read at any offset, so no gas is enough) plus no oversized
   CREATE initcode.  It is stated for every list of GAS
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
  `!vs. mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
          out.po_unit.cu_context vs` by
    metis_tac[o1_runtime_unit_create_size_ok] >>
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
           (gas_explicit marks vi.vs_gas_readings) am tx)` by fs[gas_source_exempt_def] >>
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

(* e2e_deploy_correctness's hypotheses.  The two clauses of the creation
   frame's relation that range over the call trace, and so over what the run
   does with the gas, are stated at the new gas (under constructor_call_free
   the trace is empty).  The exemption premise is the deploy counterpart of the call's,
   for every list of GAS observations. *)
Theorem e2e_deploy_gas_sufficient_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
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
  drule_all deploy_unit_run_bounded >>
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
    (irule deploy_state_rel_add_frame_gas >> fs[]) >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  qabbrev_tac `vs = deploy_entry_state prog cplan tops (add_frame_gas g' es)` >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[Abbr`vs`, deploy_entry_state_def, entry_venom_state_def] >>
  qabbrev_tac `D = deploy_dead tops runtime_bc am tx` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  (* every input state S4 may pick: a gas variant of vs *)
  `!vi. gas_variant vi vs ==>
        raw_unit_memory_ok dunit.cu_context vi /\
        ptr_discipline (imm_len tops) dunit.cu_context vi /\
        taint_within D dunit.cu_context vi /\
        mem_inv dload_offset_ok dunit.cu_context vi /\
        mem_inv dload_headroom_ok dunit.cu_context vi /\
        terminates (run_context fuel dunit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     `!marks. ~deploy_source_exempt tops
        (load_contract NONE (gas_explicit marks vi.vs_gas_readings) am tx
           [(NONE, tops)] [])` by fs[deploy_gas_source_exempt_def] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >>
        fs[o1_run_state_ok_def]) >>
     `gas_variant vi (deploy_entry_state prog cplan tops (add_frame_gas g' es))`
       by fs[Abbr`vs`] >>
     drule_all deploy_unit_memory_ok >> strip_tac >>
     drule_all deploy_unit_dload_ok >> strip_tac >>
     qpat_x_assum `!es vs. _ ==> terminates (run_context fuel _ _)`
       (qspecl_then [`add_frame_gas g' es`, `vi`] mp_tac) >>
     impl_tac >- fs[] >>
     fs[Abbr`D`]) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _` irule >>
     simp[] >> metis_tac[]) >>
  (* S4's input state, for the codegen obligations and the return value *)
  qspecl_then [`D`, `imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`] mp_tac
    run_venom_pipeline_correct >>
  impl_tac >- simp[] >> strip_tac >>
  `raw_unit_memory_ok dunit.cu_context vs_in /\
   ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
   taint_within D dunit.cu_context vs_in /\
   mem_inv dload_offset_ok dunit.cu_context vs_in /\
   mem_inv dload_headroom_ok dunit.cu_context vs_in /\
   terminates (run_context fuel dunit.cu_context vs_in)` by metis_tac[] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs` by metis_tac[] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  (* what the compiled constructor returns, as for e2e_deploy_correctness *)
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `cplan`, `am`, `tx`, `add_frame_gas g' es`, `vs_in`]
    mp_tac deploy_unit_execution_correct >>
  impl_tac >- fs[Abbr`vs`] >>
  strip_tac >- metis_tac[] >>
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
  qpat_x_assum `!g' am tx es Inv. _`
    (qspecl_then [`g'`, `am`, `tx`, `es`, `Inv`] mp_tac) >>
  impl_tac
  >- (fs[Abbr`vs`] >>
      qexistsl_tac [`load_contract NONE (gas_explicit marks vs_in.vs_gas_readings)
                       am tx [(NONE, tops)] []`, `vfuel`] >>
      fs[]) >>
  simp[]
QED
