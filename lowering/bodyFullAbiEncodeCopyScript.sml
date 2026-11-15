(* A single staging copy: origin execution and caller exterior resources. *)
Theory bodyFullAbiEncodeCopy
Ancestors
  bodyPtrDefs bodyFullAbiEncodeStore typedCopyPtr assignTuplePtrCopyEndpoint
  ptrSafetyTransport fragGasOriginPtrLoop fragExecPtr robustCopyTransportPtr
  localPtrsProps ghostPcTransportPtr instMemFrontier ptrSafeRun ptrDiscipline
  venomInst venomState venomExecSemantics venomInstProofs valueEncodingProps
  valueEncodingProofs compileEnv loweringStateRelDefs exprSimProps
  abiAllocationHistory arithmetic finite_map pred_set

Theorem abi_encode_mcopy_origin_path:
  !s ctx func bb id dst src count_op a b n D lo explicit PG G tn.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MCOPY [Var dst;Var src;count_op] []) /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
    allocas_from lo s /\
    inst_mem_below_frontier (mk_inst id MCOPY [Var dst;Var src;count_op] []) s /\
    inst_dload_in_section (mk_inst id MCOPY [Var dst;Var src;count_op] []) s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (mcopy (w2n b) (w2n a) (w2n n) s with vs_inst_idx := SUC s.vs_inst_idx),
       G, step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
         (mcopy (w2n b) (w2n a) (w2n n) s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst 0 ctx (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
     OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
         eval_operand_def] >>
  `step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  `ghost_step 0 ctx PG G tn (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
    (G, step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)` by
    fs[Once ghost_step_def, mk_inst_def] >>
  `ptr_safe_step D lo 0 ctx func PG G tn (mk_inst id MCOPY [Var dst;Var src;count_op] []) s` by
    (simp[Once ptr_safe_step_def, mk_inst_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >> simp[] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_operand) >> simp[] >> metis_tac[]) >>
  irule step_origin_ptr_path >> fs[mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_mcopy_local_robust_at[local]:
  !func D lo d ce cx es G tn s id dst src count_op a b n name entry p sz v mem.
    local_ptrs_rel func ce es.scopes s /\ ghost_inv_at D lo d ce cx es G tn s /\
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    (!name off sz. local_region ce es.scopes s name off sz ==>
      regions_disjoint (w2n b) (w2n n) off sz) /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME v /\
    mem_agree_outside
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem
      (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n v) mem
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `local_region ce es.scopes s name (w2n v) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mcopy (w2n b) (w2n a) (w2n n) s).vs_memory`,
    `tn.t_mem`,
    `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem`,
    `{i | w2n b <= i /\ i < w2n b + w2n n}`] >>
  simp[] >> conj_tac
  >- (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `eval_operand dst s = SOME b`
        (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
      disch_then (fn th => qpat_assum `eval_operand src s = SOME a`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `eval_operand count_op s = SOME n`
        (mp_then Any mp_tac th)) >>
      disch_then (qspecl_then [`ARB`, `G`, `tn`, `id`] strip_assume_tac) >>
      rpt strip_tac >> gvs[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >>
  qpat_x_assum `!name off sz. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encode_mcopy_frame_at:
  !func D lo d ce cx es G tn s id dst src count_op a b n
    origin G0 tn0 s0 tv v.
    local_ptrs_rel func ce es.scopes s /\ ghost_inv_at D lo d ce cx es G tn s /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\ lo <= w2n b /\
    (!name off sz. local_region ce es.scopes s name off sz ==>
      regions_disjoint (w2n b) (w2n n) off sz) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n b) (w2n n) off sz) /\
    (!name off sz. local_region ce es.scopes s0 name off sz ==>
      regions_disjoint (w2n b) (w2n n) off sz) /\
    val_wf tv v /\ val_footprint tv v <= w2n n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n a) mem) ==>
    ghost_inv_at D lo d ce cx es G
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
      (mcopy (w2n b) (w2n a) (w2n n) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn) /\
    (!mem. mem_agree_outside
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem
      (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory mem ==>
      val_in_memory tv v (w2n b) mem) /\
    (mcopy (w2n b) (w2n a) (w2n n) s).vs_allocas = s.vs_allocas /\
    (mcopy (w2n b) (w2n a) (w2n n) s).vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==>
      abi_alloca_history code (mcopy (w2n b) (w2n a) (w2n n) s with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `eval_operand dst s = SOME b`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand src s = SOME a`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand count_op s = SOME n`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`ARB`, `G`, `tn`, `id`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ghost_inv_at D lo d ce cx es G tf t` >>
  `tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!x. op_taint tf (Var x) = op_taint tn (Var x)` by simp[op_taint_def] >>
  `!x. lookup_var x t = lookup_var x s` by
    simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  `!p sz. ptr_covers G tn p s sz ==> ptr_covers G tf p t sz` by
    simp[ptr_covers_def, Abbr `t`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac >- suspend "inv" >>
  conj_tac >- suspend "kept" >>
  conj_tac
  >- (simp[NoAsms, Abbr `tf`] >> metis_tac[mcopy_staged_robust_ptr]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, abi_alloca_history_def]
QED

Resume abi_encode_mcopy_frame_at[inv]:
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `mem_agree_outside tf.t_mem
        (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory mem` by gvs[Abbr `t`] >>
      irule abi_encode_mcopy_local_robust_at >>
      goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
      fs[Abbr `tf`] >>
      goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
      goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def, Abbr `t`, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- gvs[stor_taint_ok_at_def, Abbr `t`, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- metis_tac[] >>
  gvs[Abbr `t`, mcopy_def, write_memory_with_expansion_def, allocas_from_def] >> metis_tac[]
QED

Resume abi_encode_mcopy_frame_at[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  rewrite_tac[ghost_kept_at_def] >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `regions_disjoint (w2n b) (w2n n) off sz` by metis_tac[] >>
      `i NOTIN {j | w2n b <= j /\ j < w2n b + w2n n}` by
        (gvs[regions_disjoint_def] >> decide_tac) >>
      `i IN tn.t_mem` by (gvs[] >> metis_tac[LESS_EQ_ADD]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `regions_disjoint (w2n b) (w2n n) b' sz` by metis_tac[] >>
      `i NOTIN {j | w2n b <= j /\ j < w2n b + w2n n}` by
        (gvs[regions_disjoint_def] >> decide_tac) >>
      `i IN tn.t_mem` by (gvs[] >> metis_tac[LESS_EQ_ADD]) >>
      qpat_x_assum `!n b sz i. _` irule >> metis_tac[]) >>
  rpt strip_tac >>
  `i IN tn.t_mem` by (gvs[] >> metis_tac[LESS_EQ_ADD, LESS_LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Resume abi_encode_mcopy_frame_at[immutable]:
  rpt strip_tac >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[Abbr `t`] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  gvs[] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, LESS_LESS_EQ_TRANS]
QED

Finalise abi_encode_mcopy_frame_at
