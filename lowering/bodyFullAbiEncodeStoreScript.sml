(* Horizon-independent clean word stores for AbiEncode staging. *)
Theory bodyFullAbiEncodeStore
Ancestors
  fragGasOriginPtrLoop exprPtrUnwrapCopyEdges wordLoadStorePtr
  assignBasePtrLiteralGhost robustCopyTransportPtr bodyPtrDefs
  allocationPtr localPtrsProps ghostPcTransportPtr instIdxIndep
  instMemFrontier ptrSafeRun ptrDiscipline venomInst venomState
  venomExecSemantics venomInstProofs valueEncodingProps valueEncodingProofs
  compileEnv loweringStateRelDefs exprSimProps abiAllocationHistory arithmetic finite_map pred_set

Theorem abi_encode_mstore_origin_path:
  !s ctx func bb id dst value a w D lo explicit PG G tn.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst;value] []) /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    inst_mem_below_frontier (mk_inst id MSTORE [Var dst;value] []) s /\
    inst_dload_in_section (mk_inst id MSTORE [Var dst;value] []) s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx),
       G, step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst 0 ctx (mk_inst id MSTORE [Var dst;value] []) s =
     OK (mstore (w2n a) w s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
         exec_write2_def, eval_operand_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  `ghost_step 0 ctx PG G tn (mk_inst id MSTORE [Var dst;value] []) s =
    (G, step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)` by
    (fs[Once ghost_step_def, mk_inst_def]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn (mk_inst id MSTORE [Var dst;value] []) s` by
    (simp[Once ptr_safe_step_def, mk_inst_def] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mstore_tainted) >> simp[]) >>
  irule step_origin_ptr_path >>
  fs[mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_mstore_local_robust_at[local]:
  !func D lo d ce cx es G tn s id dst value a w name entry p sz v mem.
    local_ptrs_rel func ce es.scopes s /\ ghost_inv_at D lo d ce cx es G tn s /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint (w2n a) 32 b sz) /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME v /\
    mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n v) mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `lookup_var dst s = SOME a`
    (mp_then Any mp_tac mstore_ghost_frame) >> simp[] >>
  disch_then (qspecl_then [`ARB`, `G`, `tn`] mp_tac) >>
  disch_then (qspecl_then [`id`, `value`, `w`] mp_tac) >> simp[] >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `local_region ce es.scopes s name (w2n v) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) w s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}`,
    `{i | w2n a <= i /\ i < w2n a+32}`] >>
  simp[] >> conj_tac
  >- (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  gvs[]
QED

Theorem abi_encode_mstore_frame_at:
  !func D lo d ce cx es G tn s id dst value a w origin G0 tn0 s0.
    local_ptrs_rel func ce es.scopes s /\ ghost_inv_at D lo d ce cx es G tn s /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ lo <= w2n a /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint (w2n a) 32 b sz) ==>
    ghost_inv_at D lo d ce cx es G
      (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
      ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G
      (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn) /\
    ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_allocas = s.vs_allocas /\
    ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==>
      abi_alloca_history code ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `G`, `id`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ghost_inv_at D lo d ce cx es G tn' t` >>
  `tn'.t_imm = tn.t_imm` by
    simp[Abbr `tn'`, step_taint_def, mk_inst_def, set_var_taint_def,
         store_taint_def, adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def] >>
  `!x. op_taint tn' (Var x) = op_taint tn (Var x)` by simp[op_taint_def] >>
  `!x. lookup_var x t = lookup_var x s` by simp[Abbr `t`, mstore_def, lookup_var_def] >>
  `!p sz. ptr_covers G tn p s sz ==> ptr_covers G tn' p t sz` by
    simp[ptr_covers_def] >>
  conj_tac >- suspend "inv" >>
  conj_tac >- (gvs[ghost_kept_at_def] >> metis_tac[IN_DIFF]) >>
  simp[Abbr `t`, mstore_def, abi_alloca_history_def]
QED

Resume abi_encode_mstore_frame_at[inv]:
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w'` by metis_tac[] >>
      `mem_agree_outside tn'.t_mem (mstore (w2n a) w s).vs_memory mem` by
        gvs[Abbr `t`] >>
      irule abi_encode_mstore_local_robust_at >>
      goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
      fs[Abbr `tn'`] >>
      goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
      goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def, Abbr `t`, mstore_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def, Abbr `t`, mstore_def] >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- metis_tac[] >>
  gvs[Abbr `t`, mstore_def, allocas_from_def] >> metis_tac[]
QED

Resume abi_encode_mstore_frame_at[immutable]:
  rpt strip_tac >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[Abbr `t`] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  gvs[] >> metis_tac[IN_DIFF]
QED

Finalise abi_encode_mstore_frame_at
