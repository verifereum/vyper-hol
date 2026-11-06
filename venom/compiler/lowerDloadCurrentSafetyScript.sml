(* Safety at the current target instruction, including failing executions. *)
Theory lowerDloadCurrentSafety
Ancestors lowerDloadDescriptorObservation lowerDloadRangeFrontier
  lowerDloadOracleCallSafety lowerDloadSafetyAmbient lowerDloadSafetyRelation
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyWriteAssembly
  lowerDloadSafetyValues lowerDloadOracleCallAssembly lowerDloadRangeTransport
  unitMemInv unitTransformDefs memLocDefs ptrDiscipline codegenRel contextCodegenRel
  venomInst venomState finite_map pred_set list words arithmetic venomWf pair
  lowerDloadPublicTrace lowerDloadSafetyLocations lowerDloadSafetyKernel
  lowerDloadExpansionExit irSupply venomExecSemantics
  lowerDloadScratchTransport lowerDloadLiveAllocation

Theorem ld_sync_ordinary_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s ==>
  raw_mem_ok C fn inst t
Proof
  strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `inst.inst_opcode <> DRET` by metis_tac[fn_ptr_ok_def] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_access_ok, ld_sync_taint_ok] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `lo <= t.vs_alloca_next` by metis_tac[ld_sync_frontier_lower_bound] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t.vs_alloca_next` by
    (rpt strip_tac >> drule_all ld_alloc_target_frontier >>
     drule ld_sync_active >> simp[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  suspend "ranges"
QED

Resume ld_sync_ordinary_raw[ranges]:
  `!op y. MEM op inst.inst_operands /\ eval_operand op t = SOME y ==>
     ?x. eval_operand op s = SOME x` by
    (rpt strip_tac >>
     `?x. eval_operand op f.lf_src = SOME x` suffices_by metis_tac[] >>
     irule ld_write_operand_defined >> metis_tac[]) >>
  `!ops szop. (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
      ops.iao_max_size = SOME szop ==>
      eval_operand szop s = eval_operand szop t` by
    (rpt strip_tac >>
     `eval_operand szop f.lf_src = eval_operand szop f.lf_tgt`
       suffices_by metis_tac[] >>
     irule ld_descriptor_size_equal >> metis_tac[]) >>
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >> disj1_tac >>
  pure_rewrite_tac[inst_mem_below_frontier_def, EVERY_MEM] >>
  qx_gen_tac `r` >> PairCases_on `r` >> pure_rewrite_tac[UNCURRY] >>
  disch_tac >>
  `?getops ranges. ((getops = mem_read_ops /\ ranges = source_memory_read_ranges) \/
                   (getops = mem_write_ops /\ ranges = source_memory_write_ranges)) /\
      MEM (r0,r1) (ranges inst t)` by
    (gvs[MEM_APPEND] >> metis_tac[]) >>
  `?ops x y. getops inst = SOME ops /\ MEM ops.iao_ofst inst.inst_operands /\
      eval_operand ops.iao_ofst s = SOME x /\
      eval_operand ops.iao_ofst t = SOME y /\ r0 = w2n y /\
      MEM (w2n x,r1) (ranges inst s)` by
    (gvs[] >> drule_all ld_single_access_range_transport >>
     metis_tac[]) >>
  `?x. eval_operand ops.iao_ofst s = SOME x /\
      (op_prov f.lf_H ops.iao_ofst = NONE ==> x=y) /\
      (!a. op_prov f.lf_H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y)` by
    (`?x. eval_operand ops.iao_ofst f.lf_src = SOME x /\
      (op_prov f.lf_H ops.iao_ofst = NONE ==> x=y) /\
      (!a. op_prov f.lf_H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y)`
       suffices_by metis_tac[] >>
     irule ld_descriptor_offset_observation >> gvs[] >> metis_tac[]) >>
  gvs[] >> once_rewrite_tac[ADD_COMM] >> irule ld_classified_range_frontier >>
  metis_tac[]
QED
Finalise ld_sync_ordinary_raw

Theorem ld_sync_dloadbytes_prefix_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  ld_prefix C' fn' X p h t0 t ==>
  raw_mem_ok C' fn' (EL h X) t
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
  `h < 2` by (drule ld_prefix_bound >> simp[]) >>
  `t0.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  Cases_on `h=0` >-
    (gvs[ld_prefix_zero] >> simp[raw_mem_ok_def, inst_mem_ok_in_fn_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]) >>
  `h=1` by decide_tac >> gvs[] >>
  drule_at (Pat `ld_prefix _ _ _ _ _ _ _`) ld_dloadbytes_prefix_observations >>
  simp[] >> strip_tac >>
  suspend "copy"
QED

Resume ld_sync_dloadbytes_prefix_raw[copy]:
  `lo <= t0.vs_alloca_next` by metis_tac[ld_sync_frontier_lower_bound] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t0.vs_alloca_next` by
    (rpt strip_tac >> drule_all ld_alloc_target_frontier >>
     drule ld_sync_active >> simp[]) >>
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >> disj1_tac >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       AllCaseEqs()] >>
  Cases_on `eval_operand dest t0` >> simp[] >>
  Cases_on `eval_operand len t0` >> simp[] >>
  rename1 `eval_operand dest t0 = SOME dw'` >>
  rename1 `eval_operand len t0 = SOME nw` >>
  `fn_ptr_ok P fn /\ s.vs_labels = t0.vs_labels /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_ptr_ok, ld_sync_labels, ld_sync_taint_ok] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `?dw. eval_operand dest s = SOME dw /\ eval_operand off s = SOME ow /\
        eval_operand len s = SOME nw` by
    (drule ld_sync_active >> simp[] >> strip_tac >>
     `?dw. eval_operand dest f.lf_src = SOME dw /\
       eval_operand off f.lf_src = SOME ow /\
       eval_operand len f.lf_src = SOME nw` suffices_by metis_tac[] >>
     irule ld_dloadbytes_source_operands >> metis_tac[]) >>
  drule_all ld_sync_dloadbytes_destination_cases >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t0.vs_alloca_next` drule >>
  strip_tac >> disj2_tac >> decide_tac
QED
Finalise ld_sync_dloadbytes_prefix_raw

Theorem ld_sync_scratch_fresh_headroom:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ld_private f d ai /\ FLOOKUP t.vs_allocas ai = NONE ==>
  t.vs_alloca_next + 32 < dimword(:256)
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `EVERY (ld_maps A) (f::fs)` by metis_tac[ld_sync_maps] >>
  `d NOTIN f.lf_E` by
    (spose_not_then assume_tac >>
     `ld_maps A f` by gvs[] >>
     drule_all ld_maps_private >> simp[]) >>
  `set (MAP (\g. g.lf_fn) (f::fs)) SUBSET set C.ctx_functions` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ld_sync_def, SUBSET_DEF, MEM_MAP, EVERY_MEM] >> rpt strip_tac >>
     metis_tac[]) >>
  `ld_charge (f::fs) + 1 <= ctx_dload_count C` by
    (irule ld_configured_charge_fresh_bound >> metis_tac[]) >>
  `dload_headroom_ok C fn inst s` by
    (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  drule ld_sync_frontier >> strip_tac >>
  gvs[lowerDloadDefsTheory.dload_headroom_ok_def] >> decide_tac
QED

Theorem ld_sync_scratch_cached_bound:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  FLOOKUP s.vs_allocas ai = NONE /\ FLOOKUP t.vs_allocas ai = SOME (b,n) ==>
  n = 32 /\ b+32 <= t.vs_alloca_next
Proof
  strip_tac >> drule ld_sync_active >> simp[] >> strip_tac >>
  `n = 32` by metis_tac[ld_maps_target, optionTheory.NOT_SOME_NONE] >>
  gvs[ld_intervals_def] >> metis_tac[]
QED
