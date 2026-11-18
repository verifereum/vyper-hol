Theory callRawVariant
Ancestors
  e2eDefs e2eEntry vyperLoweringCorrect o1PassContract
  lowerDloadDefs stackPlanGen vyperCompiler venomState venomLayout
  vyperTypeContractSoundness words arithmetic list rich_list

Theorem raw_variant_outcomes:
  raw_variant fmp si so ==> si.vs_outcomes = so.vs_outcomes
Proof
  simp[raw_variant_def, gas_variant_def, venom_state_component_equality]
QED

Theorem raw_variant_call_ctx:
  raw_variant fmp si so ==> si.vs_call_ctx = so.vs_call_ctx
Proof
  simp[raw_variant_def, gas_variant_def, venom_state_component_equality]
QED

Theorem raw_variant_initial_venom_state_rel:
  raw_variant fmp si so /\ initial_venom_state_rel tops am tx so ==>
  initial_venom_state_rel tops am tx si
Proof
  simp[raw_variant_def, gas_variant_def, venom_state_component_equality,
       initial_venom_state_rel_def, venom_env_rel_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_fmp_choice:
  !tops rpolicy unit out cp prog prog' es fmp.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fmp = (n2w (MAX cp.cp_initial_fmp
                  (unit_alloca_budget unit.cu_context +
                   32 * ctx_dload_count unit.cu_context)) : bytes32) ==>
    w2n (opt_entry_state prog prog' cp es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan _ = SOME cplan` >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_static_headroom >> strip_tac >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `unit_alloca_budget unit.cu_context +
   32 * ctx_dload_count unit.cu_context < 2 ** 254` by
    fs[ctx_dload_count_def, FILTER_FLAT, LENGTH_FLAT, MAP_MAP_o,
       combinTheory.o_DEF] >>
  `MAX cplan.cp_initial_fmp
     (unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context) < dimword (:256)` by
    (fs[MAX_DEF, dimword_def, dimindex_256] >> decide_tac) >>
  gvs[opt_entry_state_def, entry_venom_state_def, w2n_n2w, MAX_DEF] >>
  decide_tac
QED

Theorem source_typing_ok_code_update:
  source_typing_ok tops am tx /\ LENGTH c < 2 ** 256 ==>
  source_typing_ok tops am (tx with code := c)
Proof
  rw[source_typing_ok_def] >>
  qexistsl_tac [`art`, `cenv`] >> fs[call_tx_well_typed_def]
QED
