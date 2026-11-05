(* Pointer destination navigation, including stale output registers. *)
Theory decoderNavigationPtr
Ancestors typedCopyPtr bodyPtrDefs fragExecPtr words venomState finite_map
  ptrDiscipline venomInst arithmetic abiEncoder abiDecoderContract
  decoderGhostFramePtr calldataDecodePtr entryDispatchPtr emitHelperProps
  exprLoweringProps venomExecSemantics pred_set ptrSafeRun codegenRel
  compileEnv emitHelper abiDecoderReentry calldataDynOwned instIdxIndep fragExec list

Theorem emitted_ptr_offset_frag_ptr:
  !cx ctx PG sa sb id root out off s a G tn total n R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id ADD [Var root; Lit (n2w off)] [out]] /\
    lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
    off + n <= total /\ w2n a + off < dimword(:256) ==>
    ?Gf tnf sf.
      sf = ((update_var out (a + n2w off) s) with
        vs_inst_idx := SUC s.vs_inst_idx) /\
      lookup_var out sf = SOME (n2w (w2n a + off)) /\
      ptr_covers Gf tnf out sf n /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = s.vs_memory /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. q <> out ==>
        lookup_var q sf = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst id ADD [Var root; Lit (n2w off)] [out]) t` >>
  qabbrev_tac `tf = step_taint
    (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s t tn` >>
  qexistsl_tac [`gf`, `tf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >>
  conj_tac >-
    simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      GSYM word_add_n2w, ADD_COMM, WORD_ADD_COMM] >>
  conj_tac >-
    ( `op_taint tf (Var out) = {}` by
        simp[Abbr `tf`, Abbr `t`, copy_len_binop_ghost_frame] >>
      gvs[ptr_covers_def] >>
      `off < dimword(:256)` by decide_tac >>
      simp[Abbr `gf`, Abbr `t`, step_prov_def, set_prov_def, out_prov_def,
        first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
        lookup_var_def, update_var_def, w2n_add_2, w2n_n2w, LESS_MOD] >>
      decide_tac) >>
  conj_tac >-
    (irule copy_len_binop_frag_ptr >> simp[mk_inst_def] >>
     simp[Abbr `gf`, Abbr `tf`, Abbr `t`, eval_operand_def, mk_inst_def,
       op_taint_def] >> gvs[ptr_covers_def, op_taint_def]) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `t`, copy_len_binop_ghost_frame,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* Exact scalar successors, independent of stale output-register contents. *)
Theorem scalar_add_frag_ptr:
  !cx ctx PG sa sb id left right out s a b G tn R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id ADD [left;right] [out]] /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    op_prov G left = NONE /\ op_prov G right = NONE ==>
    ?H u.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\
          v = (update_var out (a+b) s with vs_inst_idx := SUC s.vs_inst_idx)) R /\
      op_taint u (Var out) = {} /\ op_prov H (Var out) = NONE /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!q. q <> out ==> FLOOKUP H q = FLOOKUP G q /\
        op_taint u (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `t = update_var out (a+b) s` >>
  qabbrev_tac `H = step_prov PG G (mk_inst id ADD [left;right] [out]) t` >>
  qabbrev_tac `u = step_taint (mk_inst id ADD [left;right] [out]) s t tn` >>
  qexistsl_tac [`H`, `u`] >> conj_tac >-
    (irule copy_len_binop_frag_ptr >> simp[Abbr `H`, Abbr `u`, Abbr `t`] >>
     metis_tac[]) >>
  simp[Abbr `u`, Abbr `t`, copy_len_binop_ghost_frame] >>
  simp[Abbr `H`, step_prov_def, out_prov_def,
    first_prov_def, set_prov_def, mk_inst_def, op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem calldata_load_frag_ptr:
  !cx ctx PG sa sb id src out s a G tn R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id CALLDATALOAD [src] [out]] /\
    eval_operand src s = SOME a /\ op_taint tn src = {} ==>
    ?H u.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\
          v = (update_var out (abi_decode_load CALLDATALOAD a s) s with
                 vs_inst_idx := SUC s.vs_inst_idx)) R /\
      op_taint u (Var out) = {} /\ op_prov H (Var out) = NONE /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!q. q <> out ==> FLOOKUP H q = FLOOKUP G q /\
        op_taint u (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = mk_inst id CALLDATALOAD [src] [out]` >>
  qabbrev_tac `t = update_var out (abi_decode_load CALLDATALOAD a s) s` >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  qexistsl_tac [`H`, `u`] >> conj_tac >-
    (irule ptr_fragment_step >> simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     rpt strip_tac >> gvs[] >> qexists_tac `t` >>
     simp[Abbr `t`, Abbr `H`, Abbr `u`, mk_inst_def,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def] >>
     rpt strip_tac >>
     irule (cj 1 (SRULE [ptr_safe_step_def, mk_inst_def] ptr_safe_dispatch_scalar_step)) >>
     simp[allocas_from_def] >>
     qexists_tac `update_var out (abi_decode_load CALLDATALOAD a s) s` >>
     simp[mk_inst_def, step_inst_non_invoke,
       step_inst_base_def, exec_read1_def, abi_decode_load_def,
       abi_decode_source_def, update_var_def]) >>
  conj_tac >-
    (simp[Abbr `u`, Abbr `inst`] >> irule dispatch_scalar_output_clean >> simp[]) >>
  conj_tac >-
    simp[Abbr `H`, Abbr `inst`, op_prov_def, step_prov_def,
      out_prov_def, set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  `!q. q <> out ==> FLOOKUP H q = FLOOKUP G q /\
    op_taint u (Var q) = op_taint tn (Var q)` by
    (rpt strip_tac >> simp[Abbr `H`, Abbr `u`, Abbr `inst`,
       step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  simp[] >>
  simp[Abbr `u`, Abbr `inst`, step_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    store_taint_def, imm_taint_def, adopt_reset_def, Abbr `t`, update_var_def,
    mk_inst_def, EXTENSION, FLOOKUP_DEF, source_memory_write_ranges_def,
    range_bytes_def, SF CONJ_ss]
QED


Theorem emit_scalar_add_endpoint_ptr:
  !left right sa out sb s t a b G tn cx ctx PG R.
    emit_op ADD [left;right] sa = (out,sb) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    op_prov G left = NONE /\ op_prov G right = NONE /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `x = "%" ++ toString sa.cs_next_var` >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `t = update_var x (a+b) s` by
    gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  `!q. not_fresh_at sa q ==> q <> x` by
    (simp[not_fresh_at_def, Abbr `x`] >> metis_tac[LESS_EQ_REFL]) >>
  drule_all scalar_add_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] mp_tac) >> strip_tac >>
  qexistsl_tac [`H`, `u`] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem emit_calldata_load_endpoint_ptr:
  !src sa out sb s t a G tn cx ctx PG R.
    emit_op CALLDATALOAD [src] sa = (out,sb) /\
    eval_operand src s = SOME a /\ op_taint tn src = {} /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `x = "%" ++ toString sa.cs_next_var` >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `t = update_var x (abi_decode_load CALLDATALOAD a s) s` by
    gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
      abi_decode_load_def, abi_decode_source_def] >>
  `!q. not_fresh_at sa q ==> q <> x` by
    (simp[not_fresh_at_def, Abbr `x`] >> metis_tac[LESS_EQ_REFL]) >>
  drule_all calldata_load_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `G`, `R`] mp_tac) >> strip_tac >>
  qexistsl_tac [`H`, `u`] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem emit_op_length[local]:
  emit_op opc ops sa = (out,sb) ==> LENGTH (emitted_insts sa sb) = 1
Proof
  strip_tac >> drule emitted_insts_emit_op >> simp[]
QED

Theorem emit_op_run_index[local]:
  emit_op opc ops sa = (out,sb) /\ ~is_terminator opc /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule step_inst_base_preserves_inst_idx >> simp[mk_inst_def]
QED

Theorem emit_op_run_pc[local]:
  emit_op opc ops sa = (out,sb) /\ ~is_terminator opc ==>
  run_inst_seq (emitted_insts sa sb) (s with vs_inst_idx := n) =
  exec_result_map (\v. v with vs_inst_idx := n)
    (run_inst_seq (emitted_insts sa sb) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  irule run_inst_seq_inst_idx >> simp[mk_inst_def]
QED

Theorem calldata_ep_source_frag_ptr:
  !src dyn ao sa ep sb s t p G tn cx ctx PG R.
    compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) sa = (ep,sb) /\
    eval_operand src s = SOME p /\
    (!q. src = Var q ==> not_fresh_at sa q) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\ ~s.vs_halted /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?H u. op_taint u ep = {} /\ op_prov H ep = NONE /\
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\
          v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> Cases_on `dyn`
  >- suspend "dynamic"
  >> simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao) /\
   op_taint tn (Lit (n2w ao)) = {} /\ op_prov G (Lit (n2w ao)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all emit_scalar_add_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] mp_tac) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`H`,`u`] >> gvs[ADD1]
QED

Resume calldata_ep_source_frag_ptr[dynamic]:
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] sa = (head,c1)` >>
  rename1 `emit_op CALLDATALOAD [head] c1 = (off,c2)` >>
  pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao) /\
   op_taint tn (Lit (n2w ao)) = {} /\ op_prov G (Lit (n2w ao)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  drule_all emit_scalar_add_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] mp_tac) >> strip_tac >>
  rename1 `op_taint u1 head = {}` >>
  rename1 `op_prov H1 head = NONE` >>
  `eval_operand head (s1 with vs_inst_idx := SUC s.vs_inst_idx) = SOME (p + n2w ao)` by simp[] >>
  drule_all (Q.INST [`s` |-> `s1 with vs_inst_idx := SUC s.vs_inst_idx`] calldata_read_repeat) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK s2` >>
  qpat_x_assum `s2 = update_var _ _ _` kall_tac >>
  drule_all emit_calldata_load_endpoint_ptr >>
  disch_then (qspecl_then [`H1`,`cx`,`ctx`,`PG`,`R`] mp_tac) >> strip_tac >>
  rename1 `op_taint u2 off = {}` >> rename1 `op_prov H2 off = NONE` >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 cs'` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!q. not_fresh_at sa q ==> not_fresh_at c1 q` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `abi_decoder_operand_live sa.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var src` by
    (Cases_on `src` >> gvs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand src s2 = SOME p` by (fs[] >> metis_tac[]) >>
  `op_taint u2 src = {} /\ op_prov H2 src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `eval_operand src (s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) = SOME p /\
   eval_operand off (s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
     eval_operand off s2` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`opc` |-> `ADD`,
    `s` |-> `s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)`] calldata_binary_repeat)) >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts c2 cs') _ = OK s3` >>
  qpat_assum `emit_op ADD [src;off] c2 = _`
    (mp_then Any mp_tac emit_scalar_add_endpoint_ptr) >>
  disch_then (qspecl_then [`s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)`,
    `s3`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`H2`,`u2`,`cx`,`ctx`,`PG`,`R`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `op_taint u3 actual_ptr = {}` >> rename1 `op_prov H3 actual_ptr = NONE` >>
  fs[] >>
  `frag_exec_ptr cx ctx PG sa c2
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H2 /\ z = u2 /\ v = (s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx))) R` by
    (irule frag_exec_ptr_seq >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `frag_exec_ptr cx ctx PG sa cs'
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H3 /\ z = u3 /\ v = (s3 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))) R` by
    (irule frag_exec_ptr_seq >> goal_assum (drule_at Any) >> metis_tac[cs_extends_trans]) >>
  suspend "align"

QED

Resume calldata_ep_source_frag_ptr[align]:
  `s1.vs_inst_idx = s.vs_inst_idx` by
    (irule emit_op_run_index >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[is_terminator_def]) >>
  `s1 with vs_inst_idx := s.vs_inst_idx = s1` by simp[venom_state_component_equality] >>
  `run_inst_seq (emitted_insts c1 c2) s1 = OK (s2 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `emit_op CALLDATALOAD _ c1 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`, `s.vs_inst_idx`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `run_inst_seq (emitted_insts c2 cs') (s2 with vs_inst_idx := s.vs_inst_idx) =
    OK (s3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `emit_op ADD [src;off] c2 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)`, `s.vs_inst_idx`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `cs'.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 cs' /\
   emitted_insts c1 cs' = emitted_insts c1 c2 ++ emitted_insts c2 cs'` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  `run_inst_seq (emitted_insts c1 cs') s1 = OK (s3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `run_inst_seq (emitted_insts c1 c2) s1 = _`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts c2 cs'` mp_tac) >> simp[]) >>
  `t = (s3 with vs_inst_idx := s.vs_inst_idx)` by
    (`emitted_insts sa cs' = emitted_insts sa c1 ++ emitted_insts c1 cs'` by
       (qspecl_then [`sa`,`c1`,`cs'`] mp_tac emitted_insts_append >>
        metis_tac[inst_extends_def, APPEND_ASSOC]) >>
     qpat_assum `run_inst_seq (emitted_insts sa c1) s = _`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts c1 cs'` mp_tac) >> fs[]) >>
  `LENGTH (emitted_insts sa cs') = 3` by
    (`emitted_insts sa cs' = emitted_insts sa c1 ++ emitted_insts c1 cs'` by
       (qspecl_then [`sa`,`c1`,`cs'`] mp_tac emitted_insts_append >>
        metis_tac[inst_extends_def, APPEND_ASSOC]) >>
     `LENGTH (emitted_insts sa c1) = 1 /\
      LENGTH (emitted_insts c1 c2) = 1 /\
      LENGTH (emitted_insts c2 cs') = 1` by metis_tac[emit_op_length] >> simp[]) >>
  qexistsl_tac [`H3`,`u3`] >> simp[] >>
  conj_tac >- (fs[ADD1] >> metis_tac[]) >>
  rpt strip_tac >> fs[lookup_var_def] >>
  `not_fresh_at c1 q /\ not_fresh_at c2 q` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >> metis_tac[]
QED

Finalise calldata_ep_source_frag_ptr
