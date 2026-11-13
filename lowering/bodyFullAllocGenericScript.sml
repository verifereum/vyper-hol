(* The generic joint lemmas on the horizon base: the ALLOCA origin edge, the
   ghost and kept frames of one compile_alloc_buffer step, and the origin
   path of a bytestring copy. *)
Theory bodyFullAllocGeneric
Ancestors
  bodyPtrIfExpAllocOrdered bodyPtrIfExpAllocSource bodyPtrIfExpAllocCompiler
  bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  bodyPtrIfExpBytesPost bodyPtrIfExpBytesSemantic bodyPtrIfExpBytesCounted
  bodyPtrIfExpAllocLocals allocationPtr
  bodyCopyMemory bodyPtrDefs bodyPtrPrecompileBuiltinsAllocationFrame
  fragGasSeqPtr fragGasOriginPtr fragExecPtr ptrSafetyTransport
  instMemFrontier unitTransformDefs memSafeRun ptrSafeRun ptrDiscipline
  loweringPosts compileEnv loweringHalt exprLoweringProps stmtFragPtr
  contextCodegenRel codegenRel
  venomInst venomState venomExecSemantics venomInstProofs finite_map

Theorem ifexp_alloca_origin_ptr_edge:
  !s ctx lo fn bb id n p u D explicit PG G tn.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [p]) /\
    step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u,
       step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)
Proof
  rpt strip_tac >>
  irule (SRULE [instruction_accessors, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id ALLOCA [Lit n] [p]`]
      straight_line_origin_ptr_edge)) >> simp[] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def,
       mk_inst_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem alloca_step_local_robust_at[local]:
  !fn cenv cx es s d G tn name entry p sz w n id out u.
    state_rel H fn cenv cx es s /\ ghost_inv_at D lo d cenv cx es G tn s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
      u.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all local_ptr_footprint_below_frontier >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def] >> strip_tac >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[]) >>
  rpt strip_tac >> irule alloca_step_robust_below_frontier >>
  conj_tac >- simp[] >>
  qexistsl_tac [`id`, `n`, `out`, `s`, `u`, `tn`] >> simp[]
QED

Theorem alloca_step_ghost_inv_separated_at[local]:
  !H D lo ctx fn cenv cx es s d G tn PG id n out u.
    stmt_state_rel H ctx fn cenv cx es s /\ ghost_inv_at D lo d cenv cx es G tn s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    not_local_ptr cenv es.scopes out /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    (!p. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var p) ==> p <> out) ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >>
  `state_rel H fn cenv cx es s` by gvs[stmt_state_rel_def] >>
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[not_local_ptr_def] >>
      first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >> conj_tac
      >- (irule alloca_step_old_ptr_covers >> simp[] >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      drule_all alloca_step_lookup_preserved >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      drule_all alloca_step_local_robust_at >> simp[]) >>
  conj_tac
  >- (irule alloca_step_return_buf_ptr >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[step_taint_other_output, mk_inst_def] >> metis_tac[]) >>
  conj_tac
  >- (drule_all alloca_runtime_frames >> strip_tac >>
      gvs[stor_taint_ok_at_def, alloca_ghost_frames]) >>
  conj_tac
  >- (drule_all alloca_runtime_frames >> strip_tac >>
      rpt strip_tac >>
      `i < s.vs_alloca_next` by decide_tac >>
      drule_all alloca_step_taint_below_frontier >> strip_tac >>
      metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `x <> out` by metis_tac[] >>
    simp[alloca_ghost_frames] >> metis_tac[]) >>
  `step_inst 0 ctx (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule_all step_inst_allocas_from >> simp[]
QED

Theorem compile_alloc_buffer_ghost_frame_at:
  !H D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
      stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
      buf.buf_operand = Var out /\ n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_inv_at D lo d cenv cx es
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
  irule alloca_step_ghost_inv_separated_at >> simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem compile_alloc_buffer_kept_frame_at:
  !H lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
      vv_post (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx e es sa sb s0 es' tv vv s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      lo <= s.vs_alloca_next /\
      local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      sa.cs_next_var <= sb.cs_next_var /\
      compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
      n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  rpt strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G tn` by
    (gvs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  simp[ghost_kept_at_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule_all alloca_step_taint_below_frontier >>
  gvs[ghost_kept_at_def] >> metis_tac[]
QED

Theorem inst_seq_ptr_lower_bound_transport[local]:
  !code s G tn Gf tnf.
    inst_seq_ptr D lo0 ctx fn PG G tn code s Gf tnf /\
    lo0 <= lo /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    EVERY (\i. i.inst_opcode <> INVOKE) code ==>
    inst_seq_ptr D lo ctx fn PG G tn code s Gf tnf
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule ptr_inst_ok_lower_bound_transport >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all step_inst_allocas_from >> strip_tac >>
  first_x_assum irule >>
  gvs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

(* Statement moved to the bytestring arm's premise form (!D inside the
   endpoint; the witnesses don't depend on the dead mask).  The proof below
   is the earlier one, for an outer !D: it needs that change. *)
Theorem compile_store_bytestring_origin_ptr_path:
  !lo explicit ctx fn PG sa sb src dst G tn s a b len n bb.
      compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
      not_fresh_at sa src /\ not_fresh_at sa dst /\
      lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
      n = 32 + 32 * ((len+31) DIV 32) /\
      len+31 < dimword(:256) /\ n < dimword(:256) /\
      mload (w2n a) s = n2w len /\
      ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
      ?Gf tnf sf.
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
        run_inst_seq (emitted_insts sa sb) s = OK sf /\
        tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
        sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
        sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
        tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
        tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
          {w2n b+i | i < n /\ w2n a+i IN tn.t_mem} /\
        (!p. not_fresh_at sa p ==>
          lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_bytestring_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  drule compile_store_bytestring_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sa sb)` by
    gvs[listTheory.EVERY_MEM] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (irule inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[listTheory.EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
     gvs[listTheory.EVERY_MEM]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED
