Theory lowerDloadReserveAlloca
Ancestors
  lowerDloadNormalAlloca lowerDloadAllocaHeadroom lowerDloadDynamicReserve
  lowerDloadNormalData lowerDloadOwnership lowerDloadAllocation
  lowerDloadAllocationOwner lowerDloadFrameCertificate lowerDloadCoverageInvariant
  venomExecSemantics venomState ptrDiscipline finite_map pred_set list words

Theorem ld_alloc_account_future_bound:
  ld_alloc_account keys d A s t /\
  d + 32 * CARD A <= 32 * ctx_dload_count C /\
  s.vs_alloca_next + m + 32 * ctx_dload_count C < dimword(:256) ==>
  s.vs_alloca_next + m < dimword(:256) /\
  t.vs_alloca_next + m < dimword(:256)
Proof
  strip_tac >> drule ld_alloc_account_frontier >> strip_tac >> decide_tac
QED

Theorem ld_alloca_normal_data_backward_reserve:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit n] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  lo <= s.vs_alloca_next /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  wf_function fn /\ mem_inv dload_headroom_ok C vs0 /\
  raw_reachable vs0 C fn i s /\ active_inst fn i s /\
  callee_first names C.ctx_functions /\ ld_stack_origin vs0 C stk fn s0 /\
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)) /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' E' k' L' H'.
    step_inst fuelS CS i s = OK s' /\
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    E' = (if FLOOKUP L i.inst_id = NONE then
      E |+ ((0,k),(FST (THE (FLOOKUP s'.vs_allocas i.inst_id)),
                    FST (THE (FLOOKUP t'.vs_allocas i.inst_id)),w2n n)) else E) /\
    (!owner. owner IN live ==> FLOOKUP E' owner = FLOOKUP E owner) /\
    ld_normal_data CS fn V U lo E' L' H' AP BP
      (ld_step_prov AP AG L' i) (ld_step_prov BP BH H' i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live)
      keys d A suspended gstk f
Proof
  strip_tac >>
  drule_all ld_indexed_reserve_bound >> strip_tac >>
  `32 * SUM (MAP CARD ss) + 32 * CARD A <= 32 * ctx_dload_count C` by
    decide_tac >>
  `FLOOKUP L i.inst_id = NONE ==>
    s.vs_alloca_next + w2n n < dimword(:256) /\
    t.vs_alloca_next + w2n n < dimword(:256)` by
    (strip_tac >>
     drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
     `FLOOKUP s.vs_allocas i.inst_id = NONE` by
       metis_tac[ld_frame_embedding_source, ld_erase_lookup,
                 optionTheory.OPTION_MAP_EQ_NONE] >>
     drule_all ld_alloca_source_future_headroom >>
     disch_then (qspec_then `fuelS` strip_assume_tac) >>
     `s.vs_alloca_next + w2n n + 32 * ctx_dload_count C < dimword(:256)` by
       metis_tac[] >>
     drule_all ld_alloc_account_future_bound >> simp[]) >>
  irule ld_alloca_normal_data_backward_fresh_bounds >>
  goal_assum (drule_at Any) >>
  simp[ld_op_prov_def, op_taint_def, eval_operand_def] >> metis_tac[]
QED
