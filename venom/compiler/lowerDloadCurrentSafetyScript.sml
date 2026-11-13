(* Safety at the current target instruction, including failing executions. *)
Theory lowerDloadCurrentSafety
Ancestors lowerDloadDescriptorObservation lowerDloadRangeFrontier
  lowerDloadOracleCallSafety lowerDloadSafetyAmbient lowerDloadSafetyRelation
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyWriteAssembly
  lowerDloadSafetyValues lowerDloadOracleCallAssembly lowerDloadRangeTransport
  unitMemInv unitTransformDefs memLocDefs ptrDiscipline codegenRel contextCodegenRel
  pointerConfinedDefs
  venomInst venomState finite_map pred_set list words arithmetic venomWf pair
  lowerDloadPublicTrace lowerDloadSafetyLocations lowerDloadSafetyKernel
  lowerDloadExpansionExit irSupply venomExecSemantics
  lowerDloadScratchTransport lowerDloadLiveAllocation lowerDloadScratchSafety
  lowerDloadAllocationOrigins lowerDloadForwardingCoverage lowerDloadReturnAlignment
  stepWriteFootprintForward lowerDloadExpansionEndpoint
Libs lowerDloadOwnedTransitionPackageLib lowerDloadForwardingPackageLib

Theorem ld_sync_target_fmp[local]:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  o1_ctx_shape C /\ mem_inv raw_mem_ok C vs0 ==>
  w2n t.vs_initial_fmp <= w2n t.vs_fmp
Proof
  strip_tac >>
  `raw_mem_ok C fn inst s` by (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  `ld_nonghost tn s t` by fs[ld_sync_def] >>
  fs[ld_nonghost_def, raw_mem_ok_def] >> metis_tac[]
QED

Theorem ld_sync_dalloca_no_wrap[local]:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ mem_inv raw_mem_ok C vs0 ==>
  dalloca_no_wrap inst t
Proof
  strip_tac >> simp[dalloca_no_wrap_def] >> strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==>
     MEM v (fn_ir_vars fn) /\ v NOTIN fn_pv P fn` by
    (gen_tac >> strip_tac >> conj_tac >- metis_tac[ld_inst_input_ir] >>
     irule ld_ptr_use_scalar >> simp[] >> qexists_tac `inst` >>
     simp[mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (`eval_operands inst.inst_operands f.lf_src =
      eval_operands inst.inst_operands f.lf_tgt` suffices_by gvs[] >>
     irule ld_vars_numeric_operands_equal >> simp[] >> metis_tac[]) >>
  `raw_mem_ok C fn inst s` by (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  `ld_nonghost tn s t` by fs[ld_sync_def] >>
  `s.vs_fmp = t.vs_fmp` by fs[ld_nonghost_def] >>
  rpt strip_tac >>
  `eval_operand sz_op s = SOME sz` by gvs[eval_operands_def, AllCaseEqs()] >>
  fs[raw_mem_ok_def, dalloca_no_wrap_def] >> metis_tac[]
QED

Theorem ld_sync_ordinary_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ mem_inv raw_mem_ok C vs0 /\
  ~in_revert_forward fn s ==>
  raw_mem_ok C fn inst t /\ inst_mem_below_frontier inst t
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
    (rpt strip_tac >> drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >>
     drule ld_sync_active >> simp[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  `dalloca_no_wrap inst t /\ w2n t.vs_initial_fmp <= w2n t.vs_fmp` by
    metis_tac[ld_sync_dalloca_no_wrap, ld_sync_target_fmp] >>
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
  `inst_mem_below_frontier inst t` suffices_by
    simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >>
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
  gvs[] >>
  `r1 = 0 \/ w2n y + r1 <= f.lf_tgt.vs_alloca_next \/ y = x` by
    (irule ld_classified_range_frontier >>
     rpt conj_tac >> TRY (qexistsl_tac [`A`,`G`,`f.lf_H`,`dyn_floor C vs0`]) >>
     rpt conj_tac >> metis_tac[]) >>
  (* same address on both sides: the source's own raw check bounds it *)
  `y = x ==> r1 = 0 \/ w2n y + r1 <= f.lf_tgt.vs_alloca_next \/
     w2n f.lf_tgt.vs_initial_fmp <= w2n y /\ w2n y + r1 <= w2n f.lf_tgt.vs_fmp` by
    (strip_tac >>
     `raw_mem_ok C f.lf_fn inst f.lf_src` by
       (irule ld_sync_source_mem_inv >> metis_tac[]) >>
     `ld_nonghost tn f.lf_src f.lf_tgt` by fs[ld_sync_def] >>
     `f.lf_src.vs_alloca_next <= f.lf_tgt.vs_alloca_next` by
       (drule ld_sync_frontier >> simp[]) >>
     irule ld_source_range_frontier >>
     fs[raw_mem_ok_def, ld_nonghost_def] >> metis_tac[]) >>
  `r1 = 0 \/ w2n y + r1 <= f.lf_tgt.vs_alloca_next \/
   w2n f.lf_tgt.vs_initial_fmp <= w2n y /\ w2n y + r1 <= w2n f.lf_tgt.vs_fmp`
    suffices_by (rpt strip_tac >> FIRST [decide_tac, fs[] >> decide_tac]) >>
  metis_tac[]
QED
Finalise ld_sync_ordinary_raw

Theorem ld_dloadbytes_prefix_fmp[local]:
  X = [<|inst_id := ai; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [dest; Var z; len]; inst_outputs := []|>] /\
  ld_prefix C' fn' X p 1 t0 t1 ==>
  t1.vs_fmp = t0.vs_fmp /\ t1.vs_initial_fmp = t0.vs_initial_fmp
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  qpat_x_assum `step_inst 0 _ _ _ = OK w` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def]
QED

Theorem ld_sync_dloadbytes_prefix_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ mem_inv raw_mem_ok C vs0 /\
  ~in_revert_forward fn s /\
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
  `w2n t0.vs_initial_fmp <= w2n t0.vs_fmp` by metis_tac[ld_sync_target_fmp] >>
  Cases_on `h=0` >-
    (gvs[ld_prefix_zero] >> simp[raw_mem_ok_def, inst_mem_ok_in_fn_def,
       dalloca_no_wrap_def, inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]) >>
  `h=1` by decide_tac >> gvs[] >>
  drule_at (Pat `ld_prefix _ _ _ _ _ _ _`) ld_dloadbytes_prefix_observations >>
  simp[] >> strip_tac >>
  drule_at (Pat `ld_prefix _ _ _ _ _ _ _`) ld_dloadbytes_prefix_fmp >>
  simp[] >> strip_tac >>
  suspend "copy"
QED

Resume ld_sync_dloadbytes_prefix_raw[copy]:
  `lo <= t0.vs_alloca_next` by metis_tac[ld_sync_frontier_lower_bound] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t0.vs_alloca_next` by
    (rpt strip_tac >> drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >>
     drule ld_sync_active >> simp[]) >>
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def, dalloca_no_wrap_def] >> disj1_tac >>
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
  FIRST [
    qpat_x_assum `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t0.vs_alloca_next`
      drule >>
    strip_tac >> disj2_tac >> decide_tac,
    (* same address above the dynamic floor: the source's own raw check *)
    `raw_mem_ok C fn inst s` by (irule ld_sync_source_mem_inv >> metis_tac[]) >>
    drule ld_sync_active >> simp[] >> strip_tac >>
    `ld_nonghost tn f.lf_src f.lf_tgt` by fs[ld_sync_def] >>
    `f.lf_src.vs_alloca_next <= f.lf_tgt.vs_alloca_next` by
      (drule ld_sync_frontier >> simp[]) >>
    `MEM (w2n dw, w2n nw) (source_memory_write_ranges inst s)` by
      simp[source_memory_write_ranges_def, sized_source_write_range_def] >>
    `w2n nw = 0 \/ w2n dw + w2n nw <= t0.vs_alloca_next \/
     w2n t0.vs_initial_fmp <= w2n dw /\ w2n dw + w2n nw <= w2n t0.vs_fmp` by
      (irule ld_source_range_frontier >>
       fs[raw_mem_ok_def, ld_nonghost_def] >> metis_tac[]) >>
    FIRST [decide_tac, fs[] >> decide_tac, gvs[] >> decide_tac]]
QED
Finalise ld_sync_dloadbytes_prefix_raw

(* A fresh private site is one more DLOAD the stack has not charged yet. *)
Theorem ld_sync_fresh_charge:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ld_private f d ai /\ FLOOKUP t.vs_allocas ai = NONE ==>
  ld_charge (f::fs) + 1 <= ctx_dload_count C
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
  irule ld_configured_charge_fresh_bound >> metis_tac[]
QED

Theorem ld_sync_scratch_fresh_headroom:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ld_private f d ai /\ FLOOKUP t.vs_allocas ai = NONE ==>
  t.vs_alloca_next + 32 < dimword(:256)
Proof
  strip_tac >>
  drule_all ld_sync_fresh_charge >> strip_tac >>
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

(* The scratch site a DLOAD expansion uses: absent in the source, and either
   fresh with room for one more site or a cached 32-byte site below the
   target frontier. *)
Theorem ld_sync_dload_scratch_bounds:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ir_supply_covers_fn f.lf_supply fn /\ ld_private f d ai ==>
  t0.vs_alloca_next < dimword(:256) /\ FLOOKUP s.vs_allocas ai = NONE /\
  (FLOOKUP t0.vs_allocas ai = NONE ==> t0.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP t0.vs_allocas ai = SOME(b,n) ==>
     n = 32 /\ b + 32 <= t0.vs_alloca_next)
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `t0.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FLOOKUP s.vs_allocas ai = NONE` by
    (irule ld_sync_private_source_absent >>
     gvs[o1PassContractTheory.o1_run_state_ok_def, o1_initial_state_ok_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (strip_tac >> irule ld_sync_scratch_fresh_headroom >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> irule ld_sync_scratch_cached_bound >> metis_tac[]
QED

Theorem ld_sync_dload_prefix_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  mem_inv raw_mem_ok C vs0 /\ ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_prefix C' fn' X p h t0 t ==>
  raw_mem_ok C' fn' (EL h X) t
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule_all ld_dload_envelope_temporary >> strip_tac >>
  drule_all ld_sync_dload_scratch_bounds >> strip_tac >>
  `w2n t0.vs_initial_fmp <= w2n t0.vs_fmp` by metis_tac[ld_sync_target_fmp] >>
  irule lower_dload_expansion_prefix_raw >>
  goal_assum (drule_at (Pat `ld_prefix _ _ _ _ _ _ _`)) >>
  metis_tac[]
QED

Theorem ld_sync_prefix_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  mem_inv raw_mem_ok C vs0 /\ ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ir_supply_covers_fn f.lf_supply fn /\ fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t ==>
  raw_mem_ok C' fn' (EL h X) t
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  Cases_on `inst.inst_opcode = DLOAD` >-
    (`?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
       (fs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
     irule ld_sync_dload_prefix_raw >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES` >-
    (`?dest off len. inst.inst_operands = [dest;off;len]` by
       (fs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
     `~in_revert_forward fn s` by
       (drule_all ld_active_lookup >> strip_tac >>
        simp[in_revert_forward_def] >> strip_tac >>
        `get_instruction bb s.vs_inst_idx = SOME inst` by simp[get_instruction_def] >>
        drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
     irule ld_sync_dloadbytes_prefix_raw >> metis_tac[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  `h = 0` by (drule ld_prefix_bound >> simp[]) >>
  gvs[ld_prefix_zero] >>
  Cases_on `in_revert_forward fn s` >- suspend "forward" >>
  drule_all ld_sync_ordinary_raw >> strip_tac >>
  fs[raw_mem_ok_def, inst_mem_ok_in_fn_def]
QED

Resume ld_sync_prefix_raw[forward]:
  `t.vs_inst_idx = p` by metis_tac[ld_sync_envelope_position] >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[ld_sync_control] >>
  `EVERY inst_wf (fn_insts fn)` by
    (gvs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `f.lf_fn = fn` by (drule ld_sync_active >> simp[]) >>
  `in_revert_forward (ld_image f) t` by
    (irule ld_envelope_revert_forward >>
     gvs[ld_image_def] >>
     goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `SND (lower_dload_function_supply f.lf_supply f.lf_fn)` >>
     simp[]) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `dalloca_no_wrap inst t /\ w2n t.vs_initial_fmp <= w2n t.vs_fmp` by
    metis_tac[ld_sync_dalloca_no_wrap, ld_sync_target_fmp] >>
  gvs[raw_mem_ok_def, inst_mem_ok_in_fn_def, in_revert_forward_def]
QED
Finalise ld_sync_prefix_raw

Theorem ld_owned_current_raw:
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ mem_inv raw_mem_ok C vs0 /\
  (!fn. MEM fn C.ctx_functions ==> ir_supply_covers_fn (Sigma fn.fn_name) fn) ==>
  raw_mem_ok C' fn' ti t
Proof
  simp[] >> strip_tac >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o MATCH_MP ld_sync_head) >>
  qpat_x_assum `frames = _` SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs))` by
    (irule ld_frames_distinct >> metis_tac[]) >>
  gvs[] >> irule ld_sync_prefix_raw >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexists_tac `p` >> simp[]
QED

Theorem ld_owned_or_forward_current_raw:
  (^ld_owned lo P C C' vs0 Sigma names fn' ti t \/ ^ld_forward C' fn' ti t) /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ mem_inv raw_mem_ok C vs0 /\
  (!fn. MEM fn C.ctx_functions ==> ir_supply_covers_fn (Sigma fn.fn_name) fn) ==>
  raw_mem_ok C' fn' ti t
Proof
  strip_tac
  >- (drule_all ld_owned_current_raw >> simp[]) >>
  drule ld_forward_current_raw >> simp[]
QED
