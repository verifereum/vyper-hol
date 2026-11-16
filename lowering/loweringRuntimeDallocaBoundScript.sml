(* Runtime allocation bound from the strict source call horizon. *)
Theory loweringRuntimeDallocaBound
Ancestors
  loweringCallBudgetBounds loweringRuntimeBudgetShape

Theorem lower_vyper_runtime_unit_dalloca_bound:
!tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
    (!marks.
       source_storage_ok am tx vs.vs_outcomes
         (gas_explicit marks vs.vs_gas_readings) /\
       call_outcomes_storage_ok am tx vs.vs_outcomes
         (gas_explicit marks vs.vs_gas_readings)) /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64
    ==>
    !fn inst s.
      raw_reachable vs unit.cu_context fn inst s ==>
      s.vs_initial_fmp = vs.vs_initial_fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      (inst.inst_opcode = DALLOCA ==>
       !sz_op sz.
         inst.inst_operands = [sz_op] /\
         eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + ceil32 (w2n sz) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `~vs.vs_halted` by fs[vyperLoweringCorrectTheory.initial_venom_state_rel_def] >>
  drule_all loweringCallBudgetHistoryTheory.lower_budget_raw_history >>
  disch_then (qspecl_then [`ARB`, `0`, `{}`] mp_tac) >> strip_tac >>
  drule_all supported_runtime_budget_allocation_shape >> strip_tac >>
  `!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET` by
    metis_tac[supported_runtime_context_fmp_guards] >>
  `MEM p.bp_fn unit.cu_context.ctx_functions /\
   EVERY (\f. MEM f.cf_fn unit.cu_context.ctx_functions) p.bp_stack` by
    (gvs[] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  drule_all lower_budget_path_fmp_guards >> strip_tac >>
  `entered.vs_fmp = vs.vs_fmp /\
   entered.vs_initial_fmp = vs.vs_initial_fmp` by
    (qpat_x_assum `enters_block _ _ _` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> strip_tac >>
     qpat_x_assum `_ = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
     drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `!a. a < LENGTH h ==> ~lower_event_allocates (EL a h)` by
    (fs[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
     metis_tac[listTheory.EL_MEM]) >>
  mp_tac lower_budget_path_fmp_envelope >>
  disch_then drule >> disch_then (qspec_then `K 0` mp_tac) >>
  (impl_tac >-
    (gvs[] >> rpt conj_tac
     >- (rpt strip_tac >> metis_tac[])
     >- (rpt strip_tac >>
         qpat_x_assum `!n p i fuel t r. _ ==> i.inst_opcode <> SETFMP`
           drule_all >> simp[]) >>
     `FILTER (\a. lower_event_allocates (EL a h))
        (GENLIST I (LENGTH h)) = []` by
       simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
            listTheory.MEM_GENLIST] >>
     simp[wordsTheory.dimword_def] >> gvs[])) >>
  strip_tac >> gvs[] >> metis_tac[]
QED
