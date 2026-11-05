(* Sufficient gas, the companion to vyper_call_correct.
 *
 * vyper_call_correct holds for any gas, so it lets the frame run out of gas.
 * Here: some amount of gas is enough.  With at least that much more gas,
 * our frame runs out of gas only once it has run a RETURNDATACOPY.  That
 * exemption is needed: when a call fails, the compiled code copies the
 * callee's revert data and reverts with it, and a callee holding all but
 * 1/64 of our gas can return more data than the rest pays to copy, or
 * leave us too little for the REVERT after the copy.
 *
 * TOP-LEVEL:
 *   vyper_call_gas_sufficient -- the companion theorem
 *   call_state_rel_add_frame_gas -- call_state_rel ignores the frame's gas
 *
 * Only gas starvation is ruled out: a StackOverflow outcome, which
 * frame_resource_starved also allows, does not depend on gas.
 *
 * Composed from three planned admissions: S1b
 * (lower_vyper_runtime_unit_run_bounded), S6b
 * (run_venom_pipeline_run_bounded) and S7g (codegen_gas_sufficient).
 *)
Theory e2eGasSufficient
Ancestors
  e2eCorrectness e2eDefs e2eProducers e2eEntry unitTransformDefs
  o1PipelineCorrect o1PassContract contextCodegenRel
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource passSimulationDefs
  codegenCorrectness immutableCodeLayout frameOutcome unitMemInv
  vfmExecution vfmExecutionProp vfmContext list rich_list pair

(* ===== add_frame_gas keeps the frame's state relation ===== *)

Theorem add_frame_gas_contexts[local]:
  es.contexts = (c, rb) :: t ==>
  (add_frame_gas g es).contexts =
    (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g), rb) ::
    MAP (\x. (FST x with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
              SND x)) t
Proof
  rw[add_frame_gas_def] >> simp[MAP_EQ_f, FORALL_PROD]
QED

Theorem add_frame_gas_fields[local]:
  (add_frame_gas g es).rollback = es.rollback /\
  (add_frame_gas g es).txParams = es.txParams /\
  (add_frame_gas g es).msdomain = es.msdomain
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem gas_stack_ok_add_frame_gas[local]:
  es.contexts = (c, rb) :: t /\ wf_context c /\
  EVERY (wf_context o FST) t /\ gas_stack_ok es ==>
  gas_stack_ok (add_frame_gas g es)
Proof
  rw[gas_stack_ok_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_MAP, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[unused_gas_def, listTheory.SUM, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[wf_context_def]
QED

Theorem add_frame_gas_wf_state:
  !g es. wf_state es ==> wf_state (add_frame_gas g es)
Proof
  rpt strip_tac >>
  Cases_on `es.contexts` >- fs[wf_state_def] >>
  PairCases_on `h` >>
  `gas_stack_ok (add_frame_gas g es)` by
    (irule gas_stack_ok_add_frame_gas >> fs[wf_state_def]) >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[wf_state_def, wf_context_def, all_accounts_def, stack_room_ok_def,
      outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
      add_frame_gas_fields, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[EVERY_MEM]
QED

Theorem call_state_rel_add_frame_gas:
  !tops bc am tx g es.
    call_state_rel tops bc am tx es ==>
    call_state_rel tops bc am tx (add_frame_gas g es)
Proof
  rw[call_state_rel_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  simp[add_frame_gas_wf_state, add_frame_gas_fields]
QED

Theorem add_frame_gas_calldata:
  !g es. (FST (HD (add_frame_gas g es).contexts)).msgParams.data =
         (FST (HD es.contexts)).msgParams.data
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

(* ===== The companion theorem ===== *)

(* vyper_call_correct's hypotheses.  The two that range over the call
   trace, and so over what the callees do with the gas they get, are
   stated at the new gas.  ~source_exempt is S3's: on the exempt inputs
   (malformed data to a dynamic abi_decode) the compiled code may read at
   any offset, so no gas is enough. *)
Theorem vyper_call_gas_sufficient:
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
      call_outcomes_ok am tx (MAP SND (call_trace (add_frame_gas g' es))) /\
      ~source_exempt tops
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            [] am tx)
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
  `valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
   call_outcomes_ok am tx vs.vs_outcomes /\
   ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    simp[] >>
  `terminates (run_context fuel unit.cu_context vs)` by
    (first_x_assum irule >> simp[]) >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_dload_offset_ok >> strip_tac >>
  `o1_run_state_ok vs` by
    (fs[o1_run_state_ok_def] >> simp[Abbr`vs`, entry_venom_state_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (first_x_assum irule >> simp[]) >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `prog = _` kall_tac >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`Inv`, `vs`] >> simp[]
QED
