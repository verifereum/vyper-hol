Theory lowerDloadCoverageAlloca
Ancestors
  lowerDloadReserveAlloca lowerDloadOrdinaryNext lowerDloadControlPosition
  lowerDloadNormalData lowerDloadOwnership lowerDloadFrameCertificate
  lowerDloadCoverageInvariant lowerDloadAllocation venomInstProps
  o1ContractLowerDload lowerDloadDefs venomExecSemantics venomState
  ptrDiscipline finite_map pred_set list words lowerDloadSupplySegment venomInst

Theorem ld_configured_alloca_next_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys (32 * SUM (MAP CARD suspended)) A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit n] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  lo <= s.vs_alloca_next /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  wf_function fn /\ mem_inv dload_headroom_ok CS vs0 /\
  raw_reachable vs0 CS fn i s /\ active_inst fn i s /\
  callee_first names CS.ctx_functions /\
  ld_stack_origin vs0 CS (MAP ld_erase_frame astk) fn s0 /\
  ld_alloc_account keys (32 * SUM (MAP CARD suspended)) A s t /\
  CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)) /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) suspended (MAP ld_erase_frame astk) /\
  step_inst fuelT CT i t = OK t' /\
  lower_dload_function_supply fa fn = (gn,fb) /\
  lower_dload_block_supply a bb = (gb,b) /\
  lower_dload_insts_supply a pre = (p,a1) /\
  lower_dload_inst_supply a1 j = (next,a2) /\
  lower_dload_insts_supply a2 post = (tail,b) /\
  bb.bb_instructions = pre ++ i::j::post /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  s.vs_inst_idx = LENGTH pre /\ t.vs_inst_idx = LENGTH p ==>
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
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx)
      astk (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live)
      keys (32 * SUM (MAP CARD suspended)) A suspended gstk f /\
    ld_annotated_reachable vs0 CS astk k' L' AP
      (ld_step_prov AP AG L' i) (step_taint i s s' tn) fn j
      (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst gn (HD next) (t' with vs_inst_idx := SUC t.vs_inst_idx) /\
    lower_dload_insts_supply a (pre ++ [i]) = (p ++ [i],a1) /\
    (s' with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH (pre ++ [i]) /\
    (t' with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = LENGTH (p ++ [i])
Proof
  strip_tac >>
  `lower_dload_inst_supply a1 i = ([i],a1)` by
    (irule lower_dload_inst_supply_special >> simp[]) >>
  `next <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  `lower_dload_insts_supply a1 (i::j::post) = ([i] ++ next ++ tail,b)` by
    simp[lower_dload_insts_supply_def] >>
  `lower_dload_insts_supply a (pre ++ (i::j::post)) =
    (p ++ ([i] ++ next ++ tail),b)` by
    (irule lower_dload_insts_supply_append_forward >>
     goal_assum (drule_at Any) >> simp[]) >>
  `gb.bb_instructions = p ++ [i] ++ next ++ tail` by
    gvs[lower_dload_block_supply_def] >>
  drule_all ld_alloca_normal_data_backward_reserve >>
  disch_then (qspec_then `fuelS` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
   i.inst_opcode <> DALLOCA` by simp[is_terminator_def] >>
  `s'.vs_current_bb = s.vs_current_bb /\ t'.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `lower_dload_insts_supply a (pre ++ [i]) = (p ++ [i],a1) /\
   active_inst fn j (s' with vs_inst_idx := SUC (LENGTH pre)) /\
   active_inst gn (HD next) (t' with vs_inst_idx := LENGTH p + LENGTH [i])` by
    (irule lower_dload_configured_segment_next >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ld_erase L' = s'.vs_allocas` by
    (drule_at Any ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP ld_frame_data_embedding) >>
     simp[ld_frame_embedding_def]) >>
  `ld_annotated_reachable vs0 CS astk k' L' AP
     (ld_step_prov AP AG L' i) (step_taint i s s' tn) fn j
     (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_annotated_reachable_next >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`s'`,`E'`,`k'`,`L'`,`H'`] >>
  simp[ld_normal_data_index_update] >>
  qpat_x_assum `active_inst gn _ _` mp_tac >> simp[arithmeticTheory.ADD1]
QED
