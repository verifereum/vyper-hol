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
 * identity case is composed from S1b-d (uniform fuel, run_context_uniform_fuel), S6b and
 * S7g-d (deploy_frame_gas_sufficient).
 *
 * The call theorem, S1b and S6b rely on the lowering's bounded ABI decoder
 * checking each range before it loads from it, as it does today.
 *)
Theory e2eGasSufficient
Ancestors
  e2eDefs e2eProducers e2eEntry unitTransformDefs
  ptrDiscipline lowerDloadDefs e2eComposition sourceUnitExitSafe
  sourceUnitExecution exprSimHypsDefs
  o1PipelineCorrect o1PipelineCompose o1PassContract contextCodegenRel
  o1StaticPipelineCorrect runtimeLabelReadiness
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource passSimulationDefs
  codegenCorrectness immutableCodeLayout frameOutcome frameGas
  venomRunBounded unitMemInv o1OpcodeAbsence
  loweringRuntimeNoCreate venomPipelineDriverProps
  asmOptimizer callTrace
  e2eDeployCorrectness e2eDeployAtMarks e2eDeployDefs ctorDeployDefs ctorDeployBodyJoint
  ctorDeployFrame ctorDeployShape ctorDeployDefsReach ctorDeployInitcode
  ctorDeployEntry ctorDeployDead ctorDeployRunBounded ctorDeployImmBudget
  ctorDeployMemoryFrontier deployUnitExecution deployUnitExitSafe
  ctorDeployLoweringSource
  vfmExecution vfmExecutionProp vfmContext list rich_list pair

val _ = Parse.hide "tops";

(* ===== Entry facts preserved by add_frame_gas ===== *)

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

Theorem entry_venom_state_add_frame_gas[local]:
  !prog cp g es.
    entry_venom_state prog cp (add_frame_gas g es) =
    entry_venom_state prog cp es with
      <| vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
         vs_gas_readings := gas_readings (add_frame_gas g es) |>
Proof
  rpt gen_tac >> Cases_on `es.contexts`
  >- simp[add_frame_gas_def, entry_venom_state_def] >>
  PairCases_on `h` >> simp[add_frame_gas_def, entry_venom_state_def]
QED

Theorem initial_ctx_rel_add_frame_gas[local]:
  !cp prog ctx vs es g.
    initial_ctx_rel cp prog ctx vs es ==>
    initial_ctx_rel cp prog ctx
      (vs with
        <| vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
           vs_gas_readings := gas_readings (add_frame_gas g es) |>)
      (add_frame_gas g es)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_state (add_frame_gas g es)` by
    (irule add_frame_gas_wf_state >> fs[initial_ctx_rel_def]) >>
  fs[initial_ctx_rel_def] >>
  drule add_frame_gas_contexts >>
  disch_then (qspec_then `g` assume_tac) >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    simp[add_frame_gas_def] >>
  qexistsl_tac [
    `ctxt with msgParams updated_by (\p. p with gasLimit updated_by $+ g)`,
    `rb`,
    `MAP (\x. (FST x with <| gasUsed updated_by $+ g;
                msgParams updated_by (\p. p with gasLimit updated_by $+ g) |>,
              SND x)) rest`] >>
  gvs[initial_state_rel_def, initial_codegen_state_rel_def,
     stack_params_rel_def, msg_ctx_rel_def, blockhash_rel_def,
     add_frame_gas_fields]
QED

(* The source boundary and code layout ignore the two traced streams.
   The codegen boundary keeps the streams of the raised state itself. *)
Theorem call_gas_entry_rel[local]:
  !tops prog am tx es u cp policy g.
    call_state_rel tops (assemble prog) am tx es /\
    codegen_assembly policy u = SOME prog /\ unit_shape_ok u ==>
    initial_venom_state_rel tops am tx
      (entry_venom_state prog cp (add_frame_gas g es)) /\
    initial_ctx_rel cp prog u.cu_context
      (entry_venom_state prog cp (add_frame_gas g es)) (add_frame_gas g es) /\
    code_layout_valid (entry_venom_state prog cp (add_frame_gas g es))
Proof
  rpt strip_tac >> rename1 `entry_venom_state prog cplan (add_frame_gas g es)`
  >- (drule entry_venom_state_initial_venom_state_rel >>
      disch_then (qspec_then `cplan` mp_tac) >>
      simp[entry_venom_state_add_frame_gas, initial_venom_state_rel_def,
           venom_env_rel_def])
  >- (drule_all entry_venom_state_initial_ctx_rel >>
      disch_then (qspec_then `cplan` assume_tac) >>
      drule initial_ctx_rel_add_frame_gas >>
      disch_then (qspec_then `g` mp_tac) >>
      simp[entry_venom_state_add_frame_gas]) >>
  drule_all generated_entry_code_layout_shape >>
  disch_then (qspec_then `cplan` mp_tac) >>
  simp[entry_venom_state_add_frame_gas, code_layout_valid_def]
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

(* ===== The gas theorems' exemptions ===== *)

(* The correctness exemptions, plus a source run that stops on an oversized
   CREATE initcode: the EVM answers that CREATE with OutOfGas at every gas
   limit (EIP-3860), so no gas is enough. *)
Definition gas_source_exempt_def:
  gas_source_exempt tops tx
    (src : (value + exception) # abstract_machine # call_request list) <=>
    source_exempt tops src \/
    FST src = INR (Error (RuntimeError "create initcode too large")) \/
    (tx.is_static /\
     ((?m. m <> "msg.gas: no gas reading" /\
           FST src = INR (Error (RuntimeError m))) \/
      FST src = INR (AssertException "UNREACHABLE")))
End

Definition deploy_gas_source_exempt_def:
  deploy_gas_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    deploy_source_exempt tops src \/
    src = INR (Error (RuntimeError "create initcode too large"))
End

Theorem call_static_abort_gas_source_exempt:
  !H tops ret tx src u.
    tx.is_static /\
    FST src <> INR (Error (RuntimeError "msg.gas: no gas reading")) /\
    external_call_result_rel H tops ret tx src (Abort ExHalt_abort u) ==>
    gas_source_exempt tops tx src
Proof
  rpt gen_tac >> PairCases_on `src` >>
  Cases_on `src0` >> simp[external_call_result_rel_def] >>
  rename1 `INR ex` >> Cases_on `ex` >>
  simp[external_call_result_rel_def, gas_source_exempt_def] >>
  rename1 `Error e` >> Cases_on `e` >>
  simp[external_call_result_rel_def, gas_source_exempt_def]
QED

Theorem call_gas_static_no_abort[local]:
  !tops ret am tx unit vs marks.
    tx.is_static /\ o1_source_unit_ok unit /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~gas_source_exempt tops tx
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx) /\
    FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading")) ==>
    ~(!fuel. terminates (run_context fuel unit.cu_context vs) ==>
       ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u)
Proof
  rpt strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule vyperInterpreterTheory.call_external_trace_result >> strip_tac >>
      gvs[gas_source_exempt_def]) >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >> fs[] >>
  drule vyperInterpreterTheory.call_external_trace_result >> strip_tac >>
  drule_all e2eCorrectnessTheory.selected_run >> strip_tac >>
  `terminates (run_context fuel unit.cu_context vs)` by
    (Cases_on `run_context fuel unit.cu_context vs` >>
     gvs[terminates_def, fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!n. terminates _ ==> _` drule >> strip_tac >>
  `external_call_result_rel (storage_trace_horizon obs) tops ret tx
     (res, am', rqs) (Abort ExHalt_abort u)` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qspecl_then [`storage_trace_horizon obs`, `tops`, `ret`, `tx`,
               `(res, am', rqs)`, `u`] mp_tac
    call_static_abort_gas_source_exempt >> gvs[]
QED

(* ===== The call cases ===== *)

(* The runtime unit S7g runs reaches no oversized CREATE.
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
  rpt strip_tac >> match_mp_tac mem_inv_create_size_ok_no_create >>
  conj_tac
  >- (qpat_x_assum `o1PipelineCorrect$o1_pipeline _ _ = _` mp_tac >>
      simp[o1PipelineCorrectTheory.o1_pipeline_def] >>
      disch_then (assume_tac o MATCH_MP run_venom_pipeline_success_unit_wf) >>
      fs[venomCompilerWfTheory.unit_wf_def]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_no_create >>
  impl_tac >- fs[] >> disch_tac >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qspecl_then [`rpolicy`, `unit`, `out`, `CREATE`] mp_tac
        o1_pipeline_opcode_absence >>
      impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]) >>
  qspecl_then [`rpolicy`, `unit`, `out`, `CREATE2`] mp_tac
    o1_pipeline_opcode_absence >>
  impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]
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
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?g. !g'.
      g <= g' /\
      (!gs. call_storage_ok am tx
         (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~gas_source_exempt tops tx
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx)) /\
      LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  PURE_REWRITE_TAC [frame_raises_inst_raises] >>
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
  `source_deployment_rel tops am tx` by fs[call_state_rel_def, frame_fresh_def,
                                           frame_tx_rel_def, world_rel_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
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
    run_venom_pipeline_run_bounded_static_abort >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  `!vs. mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
          out.po_unit.cu_context vs` by
    metis_tac[o1_runtime_unit_create_size_ok] >>
  qexists_tac `g` >> rpt strip_tac >>
  (* Carry only the entry facts that survive the gas top-up. *)
  drule_all call_gas_entry_rel >>
  disch_then (qspecl_then [`cplan`, `g'`] strip_assume_tac) >>
  `outcomes_accounts_typed
      (SOME (MAP SND (call_trace (add_frame_gas g' es))))` by
    (`wf_state (add_frame_gas g' es) /\
      balance_bounded (2 ** 256 - 1) (add_frame_gas g' es) /\
      returndata_bounded (add_frame_gas g' es)` by
       (fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
           evm_state_ok_def, add_frame_gas_bounded] >>
        irule add_frame_gas_wf_state >> simp[]) >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  `wf_state es` by fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def,
                      world_rel_def, evm_state_ok_def] >>
  qpat_x_assum `valid_vyper_call _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC [GSYM (Q.SPECL [`g'`, `es`] add_frame_gas_calldata)] >>
  strip_tac >>
  qspecl_then [`prog`, `cplan`, `add_frame_gas g' es`] assume_tac
    entry_venom_state_o1_initial_state_ok >>
  qabbrev_tac `vs = entry_venom_state prog cplan (add_frame_gas g' es)` >>
  `vs.vs_outcomes = MAP SND (call_trace (add_frame_gas g' es)) /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_call_ctx.cc_calldata =
     buffer_to_list (FST (HD (add_frame_gas g' es).contexts)).msgParams.data`
    by simp[Abbr`vs`, entry_venom_state_def] >>
  `o1_initial_state_ok vs /\ code_layout_valid vs` by fs[Abbr`vs`] >>
  `vs.vs_fmp = vs.vs_initial_fmp` by
    simp[Abbr`vs`, entry_venom_state_def] >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  (* Each variant has its own storage horizon.  The gas bound needs only
     termination and memory bounds, so one all-dead mask serves them all. *)
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr`D`, dead_wf_def] >>
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
      outcomes_accounts_typed (SOME vi.vs_outcomes) /\
      (!marks.
        call_storage_ok am tx vi.vs_outcomes
          (gas_explicit marks vi.vs_gas_readings)) /\
      !marks. ~source_exempt tops
        (call_external (SOME vi.vs_outcomes)
           (gas_explicit marks vi.vs_gas_readings) am tx)`
       by fs[gas_source_exempt_def] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >>
        fs[o1_run_state_ok_def]) >>
     `~ctx_has_dalloca unit.cu_context` by simp[] >>
     drule_all lower_vyper_runtime_unit_correct >>
     disch_then (qx_choose_then `marks` assume_tac o
       REWRITE_RULE [source_unit_execution_correct_def]) >>
     qspecl_then [`marks`, `tops`, `ret`, `am`, `tx`, `unit`, `vi`, `rpolicy`]
       mp_tac source_unit_exit_safe_runs >>
     impl_tac >- fs[] >> strip_tac >>
     `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by
       (qpat_x_assum `gas_variant vi vs` mp_tac >>
        simp[gas_variant_def] >>
        disch_then (mp_tac o Q.AP_TERM
          `\s:venom_state. w2n s.vs_initial_fmp <= w2n s.vs_fmp`) >>
        simp[Abbr`vs`, entry_venom_state_def]) >>
     drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
     `mem_inv dload_offset_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_offset_ok >> metis_tac[]) >>
     `mem_inv dload_headroom_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
     `terminates (run_context fuel unit.cu_context vi)` by
       (qpat_x_assum `!vs. _ ==> terminates (run_context fuel _ _)` irule >>
        simp[]) >>
     simp[Abbr`D`, taint_within_def]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`D`, `vs`, `vs.vs_initial_fmp`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[raw_variant_gas_variant]) >> simp[]) >>
  (* S4's input state, for the codegen obligations *)
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `o1_lowered_inv out.po_unit.cu_context vs` by
    (Cases_on `tx.is_static`
     >- (qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`,
                      `vs.vs_initial_fmp`] mp_tac
           run_venom_pipeline_correct_static_abort >>
         impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
         `gas_variant vs_in vs` by metis_tac[raw_variant_gas_variant] >>
         `raw_unit_memory_ok unit.cu_context vs_in /\
          ptr_discipline 0 unit.cu_context vs_in /\
          taint_within D unit.cu_context vs_in /\
          mem_inv dload_offset_ok unit.cu_context vs_in /\
          mem_inv dload_headroom_ok unit.cu_context vs_in` by
           (qpat_x_assum `!vi. gas_variant vi vs ==> _`
              (qspec_then `vs_in` mp_tac) >> simp[]) >>
         qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` drule_all >> strip_tac >>
         `initial_venom_state_rel tops am tx vs_in` by
           metis_tac[gas_variant_initial_venom_state_rel] >>
         `vs_in.vs_outcomes = vs.vs_outcomes /\
          vs_in.vs_call_ctx = vs.vs_call_ctx` by
           metis_tac[gas_variant_outcomes, gas_variant_call_ctx] >>
         `valid_vyper_call tops tx vs_in.vs_call_ctx.cc_calldata ret /\
          outcomes_accounts_typed (SOME vs_in.vs_outcomes)` by fs[] >>
         drule_all lower_vyper_runtime_unit_correct_readings_available >>
         strip_tac >>
         `call_storage_ok am tx vs_in.vs_outcomes
            (gas_explicit marks vs_in.vs_gas_readings) /\
          ~gas_source_exempt tops tx
            (call_external (SOME vs_in.vs_outcomes)
              (gas_explicit marks vs_in.vs_gas_readings) am tx)` by fs[] >>
         `FST (call_external (SOME vs_in.vs_outcomes)
            (gas_explicit marks vs_in.vs_gas_readings) am tx) <>
            INR (Error (RuntimeError "msg.gas: no gas reading"))` by
           (qpat_x_assum `(?tail. _) ==> _` mp_tac >>
            impl_tac >- (qexists_tac `[]` >> simp[]) >>
            disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
         drule_all call_gas_static_no_abort >> metis_tac[]) >>
     `o1_run_state_ok vs` by
       (fs[o1_run_state_ok_def] >>
        gvs[Abbr`vs`, entry_venom_state_def, call_state_rel_def,
            frame_fresh_def, frame_tx_rel_def, world_rel_def,
            add_frame_gas_def]) >>
     qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`,
                  `vs.vs_initial_fmp`] mp_tac run_venom_pipeline_correct >>
     impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
     `gas_variant vs_in vs` by metis_tac[raw_variant_gas_variant] >>
     qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` mp_tac >>
     impl_tac >- metis_tac[] >> simp[]) >>
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
    ?(H : (bool # bytes32 # type_value) list # num list) gobs efuel.
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
  `EVERY pre_fmp_ops dunit.cu_context.ctx_functions` by
    (rw[EVERY_MEM] >> irule source_pre_fmp_ops >>
     metis_tac[deploy_unit_shape_ok]) >>
  `vi.vs_initial_fmp = vi.vs_fmp` by
    (qpat_x_assum `gas_variant _ _` mp_tac >> simp[gas_variant_def] >>
     disch_then (mp_tac o AP_TERM
       ``\s:venom_state. s.vs_initial_fmp = s.vs_fmp``) >>
     simp[deploy_entry_state_def, entry_venom_state_def]) >>
  `~ctx_has_dalloca dunit.cu_context` by
    metis_tac[deploy_unit_shape_ok] >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `vi.vs_outcomes = MAP SND (call_trace es)` by
    (drule gas_variant_outcomes >>
     simp[deploy_entry_state_def, entry_venom_state_def]) >>
  `deploy_unit_execution_correct tops runtime_bc am tx dunit vi` by
    (irule deploy_unit_execution_correct_joint >> metis_tac[]) >>
  pop_assum (qx_choose_then `marks` assume_tac o
             REWRITE_RULE [deploy_unit_execution_correct_def]) >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `tx`, `dunit`, `vi`, `[]`]
    mp_tac deploy_unit_exit_safe_runs >>
  REWRITE_TAC [APPEND_NIL] >>
  qabbrev_tac `gobs = gas_explicit marks vi.vs_gas_readings` >>
  `load_contract (SOME vi.vs_outcomes) gobs am tx [(NONE, tops)] [] =
   load_contract NONE gobs am tx [(NONE, tops)] []` by
    metis_tac[load_contract_call_free] >>
  impl_tac >- (rpt conj_tac >> fs[]) >>
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
  >> qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `fn`, `vi`]
       mp_tac lowered_unit_dload_headroom_ok_from >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
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
  (* S1b-d: one fuel for every run that ends; each variant's run ends on its
     exit arm (below) *)
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `dunit`, `am`, `tx`]
    mp_tac deploy_unit_fns_fuel_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `cplan`, `fuel'`, `M`] mp_tac
    (INST_TYPE [alpha |-> ``:256``] deploy_frame_gas_sufficient) >>
  impl_tac >- fs[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the creation frame at the new gas *)
  `deploy_state_rel tops deploy_bc am tx (add_frame_gas g' es)` by
    (irule deploy_state_rel_add_frame_gas >> fs[]) >>
  `wf_state es` by fs[deploy_state_rel_def] >>
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
        ?(H : (bool # bytes32 # type_value) list # num list) gobs efuel.
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
     `!obs. ~deploy_source_exempt tops
        (load_contract NONE obs am tx [(NONE, tops)] [])`
       by fs[deploy_gas_source_exempt_def] >>
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
     simp[] >> qexists_tac `Du` >> simp[] >> rpt strip_tac >>
     TRY (simp[Abbr`Du`, taint_within_def] >> NO_TAC) >>
     metis_tac[]) >>
  (* S4's input state, picked before its dead set *)
  `!eom. max_live_eom dout.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`,
               `vs.vs_initial_fmp`] mp_tac
    run_venom_pipeline_correct_all_dead >>
  impl_tac >- simp[] >> strip_tac >>
  `gas_variant vs_in vs` by
    metis_tac[raw_variant_gas_variant, o1_run_state_ok_def] >>
  `?(H : (bool # bytes32 # type_value) list # num list) gobs efuel.
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
  `!obs. ~deploy_source_exempt tops
     (load_contract NONE obs am tx [(NONE, tops)] [])`
    by fs[deploy_gas_source_exempt_def] >>
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

Theorem call_gas_static_lowered_inv:
  !H tops ret am tx fuel unit out vs_in vs marks tail.
    tx.is_static /\
    (!rest.
      FST (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ rest) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading"))) /\
    ~gas_source_exempt tops tx
      (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ tail) am tx) /\
    external_call_result_rel H tops ret tx
      (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ tail) am tx)
      (run_context fuel unit.cu_context vs_in) /\
    terminates (run_context fuel unit.cu_context vs_in) /\
    (o1_lowered_inv out.po_unit.cu_context vs \/
     (!n. terminates (run_context n unit.cu_context vs_in) ==>
       ?u. run_context n unit.cu_context vs_in = Abort ExHalt_abort u)) ==>
    o1_lowered_inv out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n. terminates _ ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!rest. FST _ <> _` (qspec_then `tail` assume_tac) >>
  gvs[] >> metis_tac[call_static_abort_gas_source_exempt]
QED
