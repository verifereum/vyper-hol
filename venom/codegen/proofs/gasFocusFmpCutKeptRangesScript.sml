(* Reflect an access at a kept fetch before using pointwise relocation. *)
Theory gasFocusFmpCutKeptRanges
Ancestors fmpStageCoverMemOperands[qualified]
  fmpStagePointRanges fmpStageOpBase fmpStageRel lowerDloadRangeTransport
  lowerDloadDescriptorObservation frameViewFacts o1PassContract unitShapeDefs
  ptrStaticDiscipline ptrDiscipline pointerConfinedDefs memLocDefs unitMemInv
  contextCodegenRel venomWf venomInst venomState words arithmetic
  finite_map pred_set list pair

Theorem kept_descriptor_nonretpc[local]:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  MEM (Var v) inst.inst_operands ==> ~retpc_var fn v
Proof
  strip_tac >>
  `MEM ops.iao_ofst inst.inst_operands /\
   ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
    metis_tac[ld_descriptor_offset_operand] >>
  fs[] >> metis_tac[ordinary_operand_not_retpc]
QED

Theorem kept_size_equal[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  (!v. MEM (Var v) inst.inst_operands ==> IS_SOME (lookup_var v s)) /\
  taint_ok fn tn inst s /\ s.vs_labels = t.vs_labels /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME szop ==> eval_operand szop s = eval_operand szop t
Proof
  strip_tac >> Cases_on `szop` >> simp[eval_operand_def] >>
  rename1 `ops.iao_max_size = SOME (Var v)` >>
  `MEM (Var v) inst.inst_operands` by
    (`(?w. Var v = Lit w) \/ MEM (Var v) inst.inst_operands` by
       metis_tac[ld_descriptor_size_operand] >> gvs[]) >>
  `~retpc_var fn v` by metis_tac[kept_descriptor_nonretpc] >>
  `op_taint tn (Var v) = {}` by metis_tac[ld_descriptor_size_clean] >>
  `v NOTIN pv` by metis_tac[fmpStageCoverMemOperandsTheory.fmp_static_descriptor_size_nonpointer] >>
  `op_prov G (Var v) = NONE` by
    (fs[op_prov_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `IS_SOME (lookup_var v s)` by simp[] >>
  Cases_on `lookup_var v s` >> gvs[] >>
  rename1 `lookup_var v s = SOME x` >>
  `?y. eval_operand (Var v) t = SOME y /\
       fmp_value_rel sm (op_prov G (Var v)) (op_taint tn (Var v)) x y` by
    (irule fmp_stage_operand_point >> goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[eval_operand_def] >> qexists_tac `inst` >> simp[]) >>
  fs[eval_operand_def] >> metis_tac[fmp_mem_value_clean]
QED

Theorem kept_descriptor_range[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
  taint_ok fn tn inst s /\ access_ok eom G fn inst s /\ ~in_revert_forward fn s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
  ((mem_read_ops inst = SOME ops /\
    MEM (w2n x,len) (source_memory_read_ranges inst s)) \/
   (mem_write_ops inst = SOME ops /\
    MEM (w2n x,len) (source_memory_write_ranges inst s))) ==>
  len = 0 \/ w2n y + len <= eom \/ fmp0 <= w2n y
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `(mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops)` by metis_tac[] >>
  `MEM ops.iao_ofst inst.inst_operands` by metis_tac[ld_descriptor_offset_operand] >>
  `!v. ops.iao_ofst = Var v ==> ~retpc_var fn v` by
    (rpt gen_tac >> disch_tac >> metis_tac[kept_descriptor_nonretpc]) >>
  `op_taint tn ops.iao_ofst = {}` by metis_tac[ld_descriptor_offset_clean] >>
  `len = 0 \/ (w2n x = w2n y /\ w2n x + len <= eom) \/
   (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
     j+len <= z /\ w2n x = b+j /\ w2n y = c+j)` by
    (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
     (`ops.iao_ofst = ops.iao_ofst` by simp[])
     >- (drule_all fmp_mem_read_operand_range_point >> simp[])
     >> drule_all fmp_mem_write_operand_range_point >> simp[]) >>
  pop_assum strip_assume_tac >> simp[] >>
  drule_all fmp_mem_sites_bounds >> simp[]
QED

Theorem focus_fmp_cut_kept_ranges:
  o1_fn_shape C fn /\ wf_function fn /\ make_ssa_input_ok fn /\
  active_inst fn inst s /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\
  (!v. MEM (Var v) inst.inst_operands ==> IS_SOME (lookup_var v s)) /\
  taint_ok fn tn inst s /\ access_ok eom G fn inst s /\ ~in_revert_forward fn s /\
  ~MEM inst.inst_opcode [DRET;PHI;INVOKE;DALLOCA;RETPC_PARAM] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  EVERY (\(off,len). len = 0 \/ off + len <= eom \/ w2n t.vs_initial_fmp <= off)
    (inst_mem_ranges inst t)
Proof
  strip_tac >> fs[] >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels /\ w2n t.vs_initial_fmp = fmp0` by
    fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!op y. MEM op inst.inst_operands /\ eval_operand op t = SOME y ==>
     ?x. eval_operand op s = SOME x` by
    (rpt strip_tac >> Cases_on `op` >> fs[eval_operand_def] >>
     res_tac >> Cases_on `lookup_var s' s` >> gvs[]) >>
  `!ops szop. (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
     ops.iao_max_size = SOME szop ==> eval_operand szop s = eval_operand szop t` by
    (rpt gen_tac >> disch_tac >> metis_tac[kept_size_equal]) >>
  drule_all ld_single_access_range_transport >> strip_tac >>
  simp[EVERY_MEM, FORALL_PROD] >>
  map_every qx_gen_tac [`off`, `len`] >> strip_tac >>
  `?ops x y. eval_operand ops.iao_ofst s = SOME x /\
     eval_operand ops.iao_ofst t = SOME y /\ off = w2n y /\
     ((mem_read_ops inst = SOME ops /\
       MEM (w2n x,len) (source_memory_read_ranges inst s)) \/
      (mem_write_ops inst = SOME ops /\
       MEM (w2n x,len) (source_memory_write_ranges inst s)))` by
    (fs[inst_mem_ranges_def] >> metis_tac[]) >>
  metis_tac[kept_descriptor_range]
QED
