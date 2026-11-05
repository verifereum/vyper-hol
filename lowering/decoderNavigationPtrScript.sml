(* Pointer destination navigation, including stale output registers. *)
Theory decoderNavigationPtr
Ancestors typedCopyPtr bodyPtrDefs fragExecPtr words venomState finite_map
  ptrDiscipline venomInst arithmetic abiEncoder abiDecoderContract
  decoderGhostFramePtr calldataDecodePtr entryDispatchPtr emitHelperProps
  exprLoweringProps venomExecSemantics pred_set ptrSafeRun codegenRel
  compileEnv emitHelper abiDecoderReentry

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
