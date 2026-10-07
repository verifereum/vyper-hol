(* TASK037: projections of the actual legacy concretize simulations.
 * Original premises, memory/liveness/displacement contracts and init witnesses
 * are retained in full; this does not certify the configured supply pass. *)
Theory concretizeOracleSim
Ancestors
  passOracleFields concretizeMemLocProofs concretizeMemLocDefs allocaRemapDefs
  pointerConfinedDefs passSharedDefs venomExecSemantics venomState venomInst
  venomWf stateEquiv passSimulationDefs
  list finite_map pred_set words

Theorem concretize_step_identity_oracle:
  !inst bb amap fn livesets init s1 s2.
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> MEMTOP /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> MCOPY /\
    inst.inst_opcode <> EXTCODECOPY /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (step_inst_base inst s1)
        (step_inst_base inst s2) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (step_inst_base inst s1)
        (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> drule_all concretize_step_inst_base_identity >>
  strip_tac >> qexists_tac `init'` >> ASM_REWRITE_TAC[] >>
  drule_all concretize_rel_lift_result_oracle >> simp[]
QED

Theorem concretize_step_alloca_oracle:
  !inst bb amap fn livesets init s1 s2 out addr alloc_size.
    inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit alloc_size] /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ssa_form fn /\
    fn_inst_ids_distinct fn /\
    alloca_inv s1 /\
    0 < w2n alloc_size /\
    s1.vs_alloca_next < dimword (:256) /\
    (FLOOKUP s1.vs_allocas inst.inst_id = NONE ==>
     s1.vs_alloca_next + w2n alloc_size < dimword (:256)) /\
    w2n addr + w2n alloc_size < dimword (:256) /\
    (!aid off sz addr'.
       FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr' ==>
       0 < sz /\ w2n addr' + sz < dimword (:256)) /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (step_inst_base inst s1)
        (step_inst_base (mk_assign_inst inst (Lit addr)) s2) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (step_inst_base inst s1)
        (step_inst_base (mk_assign_inst inst (Lit addr)) s2)
Proof
  rpt gen_tac >> strip_tac >> drule_all concretize_step_alloca_assign >>
  strip_tac >> qexists_tac `init'` >> ASM_REWRITE_TAC[] >>
  drule_all concretize_rel_lift_result_oracle >> simp[]
QED

Theorem concretize_exec_block_oracle:
  !bb amap fn livesets init fuel ctx s1 s2.
    fn_inst_wf fn /\ ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 inst0 s s' init0 init1.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
    EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions /\
    concretize_rel amap fn livesets init s1 s2 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx
           (clear_nops_block
              (block_map_transform (concretize_inst amap) bb)) s2) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx
           (clear_nops_block
              (block_map_transform (concretize_inst amap) bb)) s2)
Proof
  rpt gen_tac >> strip_tac >> drule_all concretize_exec_block_sim >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  strip_tac >> qexists_tac `init'` >> ASM_REWRITE_TAC[] >>
  drule_all concretize_rel_lift_result_oracle >> simp[]
QED

Theorem concretize_function_oracle:
  !amap fn livesets init fuel ctx s1 s2.
    venom_wf ctx /\ fn_inst_wf fn /\ ssa_form fn /\
    fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    (!bb s s' n.
       MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)) /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel ctx bb s s' init0 init1.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 bb inst0 s s' init0 init1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
                EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions)
      fn.fn_blocks /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function amap fn) s2) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  rpt gen_tac >> strip_tac >> drule_all concretize_function_correct_proof >>
  disch_then (qspec_then `fuel` mp_tac) >>
  strip_tac >> qexists_tac `init'` >> ASM_REWRITE_TAC[] >>
  drule_all concretize_rel_lift_result_oracle >> simp[]
QED
