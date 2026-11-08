(* Allocation-aware member setup at the supplied raw execution endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixMemberFloor
Ancestors
  ctorDeployMemoryRunPtrPrefixMemberSetup
  ctorDeployMemoryRunPtrPrefixAllocationFloor
  abiDecoderDynamicLoopSetup instIdxIndep venomState ptrDiscipline ptrSafeRun
  abiDecoderReentryPointer abiDecoderReentry abiDecoderContract
  compileEnv fragExec words venomMemDefs allocaFrontierBound allocaBudgetProps ctorAbiActualFrame

Theorem prefix_member_setup_pair_floor:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb+ao) : bytes32) s = n2w payload_off /\
           sb+payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?H qt child_dst.
    let prepared = t with vs_inst_idx := LENGTH middle.cs_current_insts in
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    eval_operand (FST ops) prepared = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) prepared = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var s prepared /\ inst_extends st middle /\
    prepared.vs_allocas = s.vs_allocas /\
    prepared.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt prepared) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all prefix_member_setup_pair >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := LENGTH middle.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by
    (match_mp_tac prefix_member_setup_run_continuation >>
     asm_rewrite_tac[] >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  drule_all prefix_member_setup_current_bb >> strip_tac >>
  drule prefix_member_setup_layout >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    gvs[abi_decoder_address_frame_def] >>
  `allocas_from lo (t with vs_inst_idx := LENGTH middle.cs_current_insts) /\
   lo <= (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists `s` >> simp[]) >>
  qexistsl [`H`,`qt`,`child_dst`] >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def,
     allocas_from_def] >> metis_tac[]
QED

Theorem prefix_prepared_alloca_invariants:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx func site s /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next ==>
  alloca_inv t /\ alloca_frontier_inv ctx func site t /\
  ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next
Proof
  strip_tac >>
  full_simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
  metis_tac[]
QED
