(* Pointwise source safety for an ordinary LowerDload instruction. *)
Theory gasFocusLowerDloadOrdinarySafety
Ancestors lowerDloadDescriptorObservation lowerDloadRangeFrontier
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyValues
  lowerDloadSafetyWriteAssembly lowerDloadRangeTransport
  lowerDloadSafetyKernel lowerDloadSafetyAllocBounds lowerDloadOracleCallAssembly
  memLocDefs pointerConfinedDefs
  unitMemInv unitTransformDefs ptrDiscipline contextCodegenRel
  venomInst venomState finite_map pred_set list words arithmetic venomWf pair

Theorem ld_sync_dalloca_no_wrap_pointwise[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ taint_ok fn tn inst s /\ raw_mem_ok C fn inst s ==>
  dalloca_no_wrap inst t
Proof
  strip_tac >> simp[dalloca_no_wrap_def] >> strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
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
  `ld_nonghost tn s t` by fs[ld_sync_def] >>
  `s.vs_fmp = t.vs_fmp` by fs[ld_nonghost_def] >>
  rpt strip_tac >>
  `eval_operand sz_op s = SOME sz` by gvs[eval_operands_def, AllCaseEqs()] >>
  fs[raw_mem_ok_def, dalloca_no_wrap_def] >> metis_tac[]
QED

Theorem ld_sync_ordinary_raw_pointwise:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  mem_inv dload_headroom_ok C vs /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  raw_mem_ok C fn inst s /\ ~in_revert_forward fn s ==>
  raw_mem_ok C fn inst t /\ inst_mem_below_frontiers inst t
Proof
  strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `inst.inst_opcode <> DRET` by metis_tac[fn_ptr_ok_def] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t.vs_alloca_next` by
    (rpt strip_tac >> drule_all ld_alloc_frontiers >>
     drule ld_sync_active >> simp[]) >>
  `dalloca_no_wrap inst t` by metis_tac[ld_sync_dalloca_no_wrap_pointwise] >>
  `w2n t.vs_initial_fmp <= w2n t.vs_fmp` by
    (`ld_nonghost tn s t` by fs[ld_sync_def] >>
     fs[ld_nonghost_def, raw_mem_ok_def] >> metis_tac[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  suspend "ranges"
QED

Resume ld_sync_ordinary_raw_pointwise[ranges]:
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
  `inst_mem_below_frontiers inst t` suffices_by
    simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >>
  pure_rewrite_tac[inst_mem_below_frontiers_def, EVERY_MEM] >>
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
     (disch_then strip_assume_tac >> first_assum irule >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      first_x_assum irule >> asm_rewrite_tac[] >>
      qexists_tac `ops` >> asm_rewrite_tac[])) >>
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
    metis_tac[ld_classified_range_frontier] >>
  `y = x ==> r1 = 0 \/ w2n y + r1 <= f.lf_tgt.vs_alloca_next \/
     w2n f.lf_tgt.vs_initial_fmp <= w2n y /\ w2n y + r1 <= w2n f.lf_tgt.vs_fmp` by
    (strip_tac >>
     `ld_nonghost tn f.lf_src f.lf_tgt` by fs[ld_sync_def] >>
     `f.lf_src.vs_alloca_next <= f.lf_tgt.vs_alloca_next` by
       (drule ld_sync_frontier >> simp[]) >>
     irule ld_source_range_frontier >>
     fs[raw_mem_ok_def, ld_nonghost_def] >> metis_tac[]) >>
  `r1 = 0 \/ w2n y + r1 <= f.lf_tgt.vs_alloca_next \/
   w2n f.lf_tgt.vs_initial_fmp <= w2n y /\ w2n y + r1 <= w2n f.lf_tgt.vs_fmp`
    suffices_by (rpt strip_tac >> fs[] >> decide_tac) >>
  metis_tac[]
QED
Finalise ld_sync_ordinary_raw_pointwise
