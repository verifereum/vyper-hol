(* Joint count validation, count store and scratch-index initialization. *)
Theory decoderArrayInitPtr
Ancestors abiDecoderGuards abiDecoderArrayInitExec decoderArraySetupPtr decoderIndexInitPtr
  decoderNavigationPtr calldataClampPtr typedCopyPtr bodyPtrDefs
  compileEnv emitHelper venomInst venomExecSemantics venomState words list
  rich_list arithmetic finite_map ptrDiscipline ptrSafeRun venomInstProofs codegenRel contextCodegenRel
  emitHelperProps exprLoweringProps fragExec decoderGhostFramePtr
  abiDecoderContract entryDispatchPtr instIdxIndep

Theorem calldata_count_guard_layout[local]:
  abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,st') ==>
  cnt = Var ("%" ++ toString st.cs_next_var) /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_next_var = st.cs_next_var + 3 /\
  st'.cs_next_id = st.cs_next_id + 4 /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) GT
       [cnt; Lit (n2w maxn)] ["%" ++ toString (st.cs_next_var + 1)];
     mk_inst (st.cs_next_id + 2) ISZERO
       [Var ("%" ++ toString (st.cs_next_var + 1))]
       ["%" ++ toString (st.cs_next_var + 2)];
     mk_inst (st.cs_next_id + 3) ASSERT
       [Var ("%" ++ toString (st.cs_next_var + 2))] []]
Proof
  simp[abi_decode_count_guard_def, emit_op_def, emit_void_def,
    emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem emit_count_comparison_endpoint_ptr[local]:
  !src bound sa out sb s t a G tn cx ctx PG R.
  emit_op GT [src; Lit bound] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id GT [src; Lit bound] [out]` >>
  `t = update_var out (bool_to_word (w2n a > w2n bound)) s` by
    (gvs[run_inst_seq_def, Abbr `inst`, Abbr `out`, step_inst_base_def,
      mk_inst_def, exec_pure2_def] >> Cases_on `src` >> gvs[eval_operand_def]) >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
      exec_pure2_def] >> Cases_on `src` >> gvs[eval_operand_def]) >>
  `!fuel fn. ~ctx_has_dalloca ctx ==>
    ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s` by
    (rpt strip_tac >>
     `op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, Abbr `inst`, mk_inst_def, step_inst_non_invoke,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       update_var_def] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  qexistsl_tac [`H`,`u`] >> conj_tac
  >- (irule ptr_fragment_step >>
      simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
      rpt strip_tac >>
      qexists_tac `update_var out (bool_to_word (w2n a > w2n bound)) s` >>
      simp[Abbr `H`, Abbr `u`] >> gvs[update_var_def, mk_inst_def, Abbr `out`]) >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    lookup_var_def,
    op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem clamp_scalar_frag_ptr[local]:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst id opc ops outs] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = step_prov PG G (mk_inst id opc ops outs) t /\
      z = step_taint (mk_inst id opc ops outs) s t tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R
Proof
  strip_tac >>
  `?vars. t = s with vs_vars := vars` by
    metis_tac[clamp_scalar_state_frame] >>
  `opc <> INVOKE /\ ~is_terminator opc` by fs[MEM, is_terminator_def] >>
  irule ptr_fragment_step >> simp[mk_inst_def] >>
  rpt strip_tac >> qexists_tac `t` >>
  simp[GSYM mk_inst_def] >> rpt strip_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `ptr_safe_step (cx_dead cx) 0 fuel ctx fn PG G tn
     (mk_inst id opc ops outs) s` by
    (irule clamp_scalar_step_safe >> simp[step_inst_non_invoke, mk_inst_def] >>
     fs[MEM]) >>
  gvs[ptr_safe_step_def, mk_inst_def]
QED

Theorem emit_clamp_scalar_endpoint_ptr[local]:
  emit_op opc ops sa = (out,sb) /\
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops
     ["%" ++ toString sa.cs_next_var]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT]` by fs[MEM] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc ops
    ["%" ++ toString sa.cs_next_var]` >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`] >>
  `EVERY (\op. op_taint tn op = {}) ops` by gvs[EVERY_MEM] >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> irule clamp_scalar_frag_ptr >> gvs[]) >>
  `(!x. not_fresh_at sa x ==> x <> "%" ++ toString sa.cs_next_var)` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `inst`] >>
  qpat_x_assum `step_inst_base _ _ = _` (assume_tac o SRULE []) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  drule_all clamp_scalar_state_frame >> strip_tac >>
  drule_all clamp_scalar_taint_frame >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[] >> gen_tac >> disch_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by (simp[] >> metis_tac[]) >>
  conj_tac >- (metis_tac[clamp_scalar_lookup_frame, MEM]) >>
  qpat_x_assum `x <> _` (assume_tac o SRULE []) >>
  simp[mk_inst_def] >> simp[step_prov_other_output, step_taint_other_output]
QED

Theorem emit_assert_endpoint_ptr[local]:
  emit_void ASSERT [op] sa = ((),sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = G /\ z = tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\ t = s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id ASSERT [op] []) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `t = s` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >> metis_tac[]) >>
  simp[] >>
  `frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = step_prov PG G (mk_inst sa.cs_next_id ASSERT [op] []) t /\
      z = step_taint (mk_inst sa.cs_next_id ASSERT [op] []) s t tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R` by
    (irule clamp_scalar_frag_ptr >> simp[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` mp_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
    mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def,
    taint_component_equality, pred_setTheory.EXTENSION,
    written_taint_def, FDOM_DRESTRICT, DRESTRICT_UNIV, FLOOKUP_DEF,
    SF CONJ_ss]
QED

Theorem emit_count_load_endpoint_ptr[local]:
  !src sa out sb s t a G tn cx ctx PG R.
  emit_op CALLDATALOAD [src] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H /\ z = u /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id CALLDATALOAD [src] [out]` >>
  `t = update_var out (abi_decode_load CALLDATALOAD a s) s` by
    gvs[run_inst_seq_def, Abbr `out`, step_inst_base_def, mk_inst_def,
      exec_read1_def, abi_decode_load_def, abi_decode_source_def] >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  qexistsl_tac [`H`, `u`] >> conj_tac >-
    (irule ptr_fragment_step >> simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     rpt strip_tac >> qexists_tac `update_var out (abi_decode_load CALLDATALOAD a s) s` >>
     simp[Abbr `H`, Abbr `u`, Abbr `out`, mk_inst_def,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def] >>
     rpt strip_tac >>
     irule (cj 1 (SRULE [ptr_safe_step_def, mk_inst_def] ptr_safe_dispatch_scalar_step)) >>
     simp[allocas_from_def] >>
     qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (abi_decode_load CALLDATALOAD a s) s` >>
     simp[mk_inst_def, step_inst_non_invoke,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def]) >>
  conj_tac >-
    (simp[Abbr `u`, Abbr `inst`, Abbr `out`] >>
     irule dispatch_scalar_output_clean >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, lookup_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED


