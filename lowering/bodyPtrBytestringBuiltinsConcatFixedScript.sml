(* Fixed Concat arm: scalar loads and increments must not acquire provenance. *)
Theory bodyPtrBytestringBuiltinsConcatFixed
Ancestors
  bodyPtrBytestringBuiltinsConcatFrame bodyPtrBytestringBuiltinsAllocation
  typedCopyPtr fragGasSeqPtr fragGasPathPtr
  concatMemory fragExecPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words
  emitHelper compileEnv exprLoweringProps abiEncoderReentryLeaves
  valueEncodingProps valueEncodingProofs venomMemProps byte list rich_list
Libs monadsyntax

Theorem concat_offset_load_ghost:
  !PG G tn s id src tmp a.
    eval_operand src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    op_prov (step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s)) (Var tmp) = NONE /\
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  drule_all mload_ghost_clean >> simp[]
QED

Theorem concat_offset_add_ghost:
  !PG G tn s id left right tmp w.
    op_prov G left = NONE /\ op_prov G right = NONE ==>
    op_prov (step_prov PG G (mk_inst id ADD [left; right] [tmp])
      (update_var tmp w s)) (Var tmp) = NONE /\
    op_taint (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_arith_none >> simp[mk_inst_def]) >>
  simp[copy_len_binop_ghost_frame]
QED

Theorem concat_offset_load_counted_edge:
  !D ctx fn PG G tn s bb id src tmp a.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [tmp]) /\
    lookup_var src s = SOME a /\ ptr_covers G tn src s 32 ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      (OK ((update_var tmp (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_mload >> simp[]
QED

Theorem concat_word_store_counted_edge:
  !D ctx fn PG G tn s bb id dst value a w.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ptr_covers G tn dst s 32 ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
      (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_mstore >> simp[]
QED

Theorem concat_offset_load_register_frame:
  !PG G tn s id src tmp a q.
    q <> tmp ==>
    lookup_var q (update_var tmp (mload (w2n a) s) s) = lookup_var q s /\
    FLOOKUP (step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s)) q = FLOOKUP G q /\
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var q) = op_taint tn (Var q)
Proof
  rpt strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def, op_taint_def]
QED

Theorem concat_word_store_preserves_covers:
  !PG G tn s id dst value a w p n.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ptr_covers G tn p s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
      p ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]
QED

Theorem concat_add_preserves_covers:
  !PG G tn s id left right tmp w p n.
    p <> tmp /\ ptr_covers G tn p s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [left; right] [tmp])
        (update_var tmp w s))
      (step_taint (mk_inst id ADD [left; right] [tmp]) s
        (update_var tmp w s) tn)
      p ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac >>
  gvs[ptr_covers_def, copy_len_binop_ghost_frame,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* The first two actual edges, retaining the loaded scalar as well as the
   full-word destination capability. No erased execution is lifted here. *)
Theorem concat_fixed_address_counted:
  !D ctx fn PG G tn s bb id root off tmp dst a b k cap width.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var off] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) /\
    lookup_var off s = SOME b /\ lookup_var root s = SOME a /\
    ptr_covers G tn off s 32 /\ ptr_covers G tn root s cap /\
    mload (w2n b) s = n2w k /\
    (!i. w2n b <= i /\ i < w2n b + 32 ==> i NOTIN tn.t_mem) /\
    k + width <= cap /\ w2n a + k < dimword(:256) /\
    root <> tmp /\ tmp <> dst ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      lookup_var dst t = SOME (a + n2w k) /\
      lookup_var tmp t = SOME (n2w k) /\
      op_prov Gf (Var tmp) = NONE /\ op_taint tnf (Var tmp) = {} /\
      ptr_covers Gf tnf dst t width /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
      t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
      t.vs_inst_idx = s.vs_inst_idx + 2 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. q <> tmp /\ q <> dst ==>
        lookup_var q t = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var tmp (n2w k) s` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst id MLOAD [Var off] [tmp]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var off] [tmp]) s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var dst (a + n2w k) s1` >>
  qabbrev_tac `g2 = step_prov PG g1
    (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) v` >>
  qabbrev_tac `tn2 = step_taint
    (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) s1 v tn1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (unabbrev_all_tac >> drule_all concat_offset_load_counted_edge >> simp[]) >>
  `op_prov g1 (Var tmp) = NONE /\ op_taint tn1 (Var tmp) = {} /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans`
    by suspend "load_ghost" >>
  `ptr_covers g1 tn1 root s1 cap /\ lookup_var root s1 = SOME a`
    by suspend "root" >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)`
    by suspend "add_edge" >>
  qexistsl_tac [`g2`, `tn2`, `s2`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_fixed_address_counted[load_ghost]:
  `eval_operand (Var off) s = SOME b` by simp[eval_operand_def] >>
  drule_all concat_offset_load_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `id`, `tmp`] mp_tac) >>
  simp[Abbr `g1`, Abbr `tn1`, Abbr `u`]
QED

Resume concat_fixed_address_counted[root]:
  conj_tac
  >- (simp[Abbr `s1`, Abbr `g1`, Abbr `tn1`, Abbr `u`] >>
      qpat_assum `mload _ _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      irule mload_preserves_ptr_covers >> simp[]) >>
  simp[Abbr `s1`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Resume concat_fixed_address_counted[add_edge]:
  simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `v`] >>
  irule pointer_offset_counted_edge >>
  gvs[Abbr `s1`, Abbr `u`, ptr_covers_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_fixed_address_counted[path]:
  `~s2.vs_halted` by
    simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD]
QED

Resume concat_fixed_address_counted[endpoint]:
  `ptr_covers g2 tn2 dst s2 width` by
    (qunabbrev_tac `g2` >> qunabbrev_tac `tn2` >>
     qunabbrev_tac `s2` >> qunabbrev_tac `v` >>
     `eval_operand (Var tmp) s1 = SOME (n2w k)` by
       simp[Abbr `s1`, Abbr `u`, eval_operand_def,
            lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     irule pointer_offset_covers >> simp[] >>
     qexists_tac `cap` >> simp[]) >>
  simp[Abbr `s2`, Abbr `v`, Abbr `tn2`, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `s1`, Abbr `u`] >>
  conj_tac
  >- (simp[Abbr `g2`, op_prov_def, copy_len_binop_ghost_frame] >>
      gvs[op_prov_def]) >>
  rpt strip_tac >>
  simp[Abbr `g2`, copy_len_binop_ghost_frame, Abbr `g1`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >>
  simp[Abbr `tn1`, step_taint_def, set_var_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE, imm_taint_def, adopt_reset_def]
QED

Finalise concat_fixed_address_counted

(* The remaining three edges. The offset is a scalar even though the data
   destination is a pointer; the full store width is always 32 bytes. *)
Theorem concat_fixed_store_counted:
  !D ctx fn PG G tn s bb id dst off offset next value a b w k m.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [Var offset; Lit (n2w m)] [next]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MSTORE [Var off; Var next] []) /\
    lookup_var dst s = SOME a /\ lookup_var off s = SOME b /\
    lookup_var offset s = SOME (n2w k) /\ eval_operand value s = SOME w /\
    ptr_covers G tn dst s 32 /\ ptr_covers G tn off s 32 /\
    op_taint tn value = {} /\ op_taint tn (Var offset) = {} /\
    op_prov G (Var offset) = NONE /\ off <> next /\ dst <> next ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      t.vs_memory =
        (mstore (w2n b) (n2w k + n2w m) (mstore (w2n a) w s)).vs_memory /\
      lookup_var next t = SOME (n2w k + n2w m) /\
      op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
      ptr_covers Gf tnf dst t 32 /\ ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
      t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
      t.vs_inst_idx = s.vs_inst_idx+3 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem DIFF
        ({i | w2n a <= i /\ i < w2n a + 32} UNION
         {i | w2n b <= i /\ i < w2n b + 32}) /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. q <> next ==>
        lookup_var q t = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst id MSTORE [Var dst; value] []) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MSTORE [Var dst; value] []) s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var next (n2w k + n2w m) s1` >>
  qabbrev_tac `g2 = step_prov PG g1
    (mk_inst (id+1) ADD [Var offset; Lit (n2w m)] [next]) v` >>
  qabbrev_tac `tn2 = step_taint
    (mk_inst (id+1) ADD [Var offset; Lit (n2w m)] [next]) s1 v tn1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `z = mstore (w2n b) (n2w k + n2w m) s2` >>
  qabbrev_tac `g3 = step_prov PG g2 (mk_inst (id+2) MSTORE [Var off; Var next] []) z` >>
  qabbrev_tac `tn3 = step_taint (mk_inst (id+2) MSTORE [Var off; Var next] []) s2 z tn2` >>
  qabbrev_tac `s3 = z with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (unabbrev_all_tac >> irule concat_word_store_counted_edge >> simp[]) >>
  `g1 = G /\ tn1.t_var = tn.t_var /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   tn1.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`
    by suspend "first_frame" >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)`
    by suspend "increment" >>
  `ptr_covers g2 tn2 off s2 32 /\ ptr_covers g2 tn2 dst s2 32`
    by suspend "covers" >>
  `gas_path_ptr_edge D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)`
    by suspend "last_store" >>
  qexistsl_tac [`g3`, `tn3`, `s3`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_fixed_store_counted[first_frame]:
  simp[Abbr `g1`, Abbr `tn1`, Abbr `u`, mstore_ghost_frame,
       step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV,
       step_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def]
QED

Resume concat_fixed_store_counted[increment]:
  simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `v`] >>
  irule pointer_offset_counted_edge >>
  gvs[Abbr `s1`, Abbr `u`, mstore_def, op_taint_def,
      lookup_var_def, eval_operand_def] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_fixed_store_counted[covers]:
  `ptr_covers g1 tn1 off s1 32 /\ ptr_covers g1 tn1 dst s1 32` by
    (conj_tac >>
     qunabbrev_tac `g1` >> qunabbrev_tac `tn1` >>
     qunabbrev_tac `s1` >> qunabbrev_tac `u` >>
     irule concat_word_store_preserves_covers >> simp[]) >>
  conj_tac >>
  qunabbrev_tac `g2` >> qunabbrev_tac `tn2` >>
  qunabbrev_tac `s2` >> qunabbrev_tac `v` >>
  irule concat_add_preserves_covers >> simp[]
QED

Resume concat_fixed_store_counted[last_store]:
  simp[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `z`] >>
  irule concat_word_store_counted_edge >>
  gvs[Abbr `tn2`, Abbr `v`, copy_len_binop_ghost_frame,
      Abbr `s2`, Abbr `s1`, Abbr `u`, mstore_def,
      update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
      arithmeticTheory.ADD1]
QED

Resume concat_fixed_store_counted[path]:
  `~s3.vs_halted` by
    simp[Abbr `s3`, Abbr `z`, Abbr `s2`, Abbr `v`,
         Abbr `s1`, Abbr `u`, mstore_def, update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD]
QED

Resume concat_fixed_store_counted[endpoint]:
  `lookup_var off s2 = SOME b /\
   eval_operand (Var next) s2 = SOME (n2w k + n2w m)` by
    (simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, mstore_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, eval_operand_def] >>
     qpat_x_assum `lookup_var off s = _` mp_tac >> simp[lookup_var_def]) >>
  `op_prov g2 (Var next) = NONE /\ op_taint tn2 (Var next) = {} /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (simp[Abbr `g2`, Abbr `tn2`, Abbr `v`, copy_len_binop_ghost_frame,
           step_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def,
           mk_inst_def] >>
     irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_arith_none >> simp[mk_inst_def, op_prov_def] >>
     qpat_x_assum `op_prov G (Var offset) = _` mp_tac >> simp[op_prov_def]) >>
  `g3 = g2 /\ tn3.t_var = tn2.t_var /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
   tn3.t_mem = tn2.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32}` by
    simp[Abbr `g3`, Abbr `tn3`, Abbr `z`, mstore_ghost_frame,
         step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV,
       step_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def] >>
  `ptr_covers g3 tn3 dst s3 32 /\ ptr_covers g3 tn3 off s3 32` by
    (gvs[ptr_covers_def, op_taint_def, Abbr `s3`, Abbr `z`,
         mstore_def, lookup_var_def]) >>
  conj_tac >-
    simp[NoAsms, Abbr `s3`, Abbr `z`, Abbr `s2`, Abbr `v`, Abbr `s1`,
         mstore_def, update_var_def] >>
  `op_taint tn3 (Var next) = {}` by
    (simp[op_taint_def] >>
     qpat_x_assum `op_taint tn2 (Var next) = _` mp_tac >> simp[op_taint_def]) >>
  simp[Abbr `s3`, Abbr `z`, mstore_def, lookup_var_def,
       pred_setTheory.DIFF_UNION] >>
  simp[Abbr `s2`, Abbr `v`, update_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `s1`, Abbr `u`, mstore_def] >>
  rpt strip_tac >>
  simp[Abbr `g2`, Abbr `tn2`, copy_len_binop_ghost_frame,
       op_taint_def, lookup_var_def, update_var_def] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Finalise concat_fixed_store_counted

Theorem compile_concat_fixed_layout:
  !data_ptr off_ptr value m sa sb.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; value];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_next_var = sa.cs_next_var + 3 /\
    sb.cs_next_id = sa.cs_next_id + 5 /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [off_ptr]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) ADD
         [data_ptr; Var (STRING #"%" (toString sa.cs_next_var))]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+2) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var+1))); value] [];
       mk_inst (sa.cs_next_id+3) ADD
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w m)]
         [STRING #"%" (toString (sa.cs_next_var+2))];
       mk_inst (sa.cs_next_id+4) MSTORE
         [off_ptr; Var (STRING #"%" (toString (sa.cs_next_var+2)))] []]
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

(* Same-endpoint composition of the two checked instruction subpaths. *)
Theorem concat_fixed_arm_counted:
  !D ctx fn PG G tn s bb id root off tmp dst next value a b w k m cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var off] [tmp]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MSTORE [Var dst; value] []) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var tmp; Lit (n2w m)] [next]) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (id+4) MSTORE [Var off; Var next] []) /\
    lookup_var off s = SOME b /\ lookup_var root s = SOME a /\
    ptr_covers G tn off s 32 /\ ptr_covers G tn root s cap /\
    mload (w2n b) s = n2w k /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
    k+32 <= cap /\ w2n a+k < dimword(:256) /\
    root <> tmp /\ tmp <> dst /\ off <> tmp /\ off <> dst /\
    off <> next /\ dst <> next /\
    (!q. value = Var q ==> q <> tmp /\ q <> dst) /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      t.vs_memory = (mstore (w2n b) (n2w k+n2w m)
        (mstore (w2n (a+n2w k)) w s)).vs_memory /\
      lookup_var next t = SOME (n2w k+n2w m) /\
      op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
      ptr_covers Gf tnf dst t 32 /\ ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
      t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
      t.vs_inst_idx = s.vs_inst_idx+5 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem DIFF
        ({i | w2n (a+n2w k) <= i /\ i < w2n (a+n2w k)+32} UNION
         {i | w2n b <= i /\ i < w2n b+32}) /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. q <> tmp /\ q <> dst /\ q <> next ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SRULE [arithmeticTheory.ADD1] concat_fixed_address_counted) >>
  disch_then (qspecl_then [`D`, `PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1`
      (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var off s1 = SOME b /\ ptr_covers G1 tn1 off s1 32`
    by suspend "off_frame" >>
  `eval_operand value s1 = SOME w /\ op_taint tn1 value = {}`
    by suspend "value_frame" >>
  `?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 Gf tnf (OK t) /\
      t.vs_memory = (mstore (w2n b) (n2w k+n2w m)
        (mstore (w2n (a+n2w k)) w s1)).vs_memory /\
      lookup_var next t = SOME (n2w k+n2w m) /\
      op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
      ptr_covers Gf tnf dst t 32 /\ ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s1.vs_allocas /\
      t.vs_accounts = s1.vs_accounts /\ t.vs_transient = s1.vs_transient /\
      t.vs_call_ctx = s1.vs_call_ctx /\ t.vs_tx_ctx = s1.vs_tx_ctx /\
      t.vs_block_ctx = s1.vs_block_ctx /\ t.vs_logs = s1.vs_logs /\
      t.vs_outcomes = s1.vs_outcomes /\ t.vs_requests = s1.vs_requests /\
      t.vs_pending_deletions = s1.vs_pending_deletions /\
      t.vs_immutables = s1.vs_immutables /\ t.vs_data_section = s1.vs_data_section /\
      t.vs_alloca_next = s1.vs_alloca_next /\ t.vs_fmp = s1.vs_fmp /\ t.vs_labels = s1.vs_labels /\
      t.vs_inst_idx = s1.vs_inst_idx+3 /\
      t.vs_current_bb = s1.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn1.t_mem DIFF
        ({i | w2n (a+n2w k) <= i /\ i < w2n (a+n2w k)+32} UNION
         {i | w2n b <= i /\ i < w2n b+32}) /\
      tnf.t_imm = tn1.t_imm /\ tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
      (!q. q <> next ==> lookup_var q t = lookup_var q s1 /\
        FLOOKUP Gf q = FLOOKUP G1 q /\
        op_taint tnf (Var q) = op_taint tn1 (Var q))`
    by suspend "suffix" >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_fixed_arm_counted[off_frame]:
  `lookup_var off s1 = lookup_var off s /\
   FLOOKUP G1 off = FLOOKUP G off /\
   op_taint tn1 (Var off) = op_taint tn (Var off)` by
    (first_x_assum (qspec_then `off` mp_tac) >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def, op_prov_def]
QED

Resume concat_fixed_arm_counted[value_frame]:
  Cases_on `value` >> gvs[eval_operand_def, op_taint_def] >>
  first_x_assum (qspec_then `s'` mp_tac) >>
  gvs[op_taint_def]
QED

Resume concat_fixed_arm_counted[suffix]:
  irule concat_fixed_store_counted >>
  simp[arithmeticTheory.ADD1] >>
  qexistsl_tac [`id+2`, `tmp`, `value`] >> simp[]
QED

Resume concat_fixed_arm_counted[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED

Resume concat_fixed_arm_counted[endpoint]:
  conj_tac >-
    (asm_rewrite_tac[] >>
     irule abi_encoder_store_memory >>
     irule abi_encoder_store_memory >> simp[]) >>
  simp[] >> metis_tac[]
QED

Finalise concat_fixed_arm_counted

(* The semantic two-write boundary, independent of instruction/register layout.
   The final offset write may overlap padding, but not the logical prefix. *)
Theorem concat_fixed_store_prefix:
  !D k bs ob x s.
    LENGTH bs <= 32 /\ (D+(k+LENGTH bs) <= ob \/ ob+32 <= D) ==>
    mem_bytes_at D (k+LENGTH bs)
      (mstore ob x (mstore (D+k)
        (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) s)).vs_memory =
    mem_bytes_at D k s.vs_memory ++ bs
Proof
  rpt strip_tac >>
  qabbrev_tac `wd = word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32` >>
  qabbrev_tac `mm = (mstore (D+k) wd s).vs_memory` >>
  `mem_bytes_at D (k+LENGTH bs) (mstore ob x (mstore (D+k) wd s)).vs_memory =
   mem_bytes_at D (k+LENGTH bs) mm` by
    (qunabbrev_tac `mm` >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >> rewrite_tac[mem_bytes_at_split_padded] >>
  `mem_bytes_at D k mm = mem_bytes_at D k s.vs_memory` by
    (qunabbrev_tac `mm` >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  `mem_bytes_at (D+k) (LENGTH bs+(32-LENGTH bs)) mm = word_to_bytes wd T` by
    (`LENGTH bs+(32-LENGTH bs) = 32` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[Abbr `mm`, mem_bytes_at_mstore_same]) >>
  pop_assum mp_tac >> rewrite_tac[mem_bytes_at_split_padded] >> strip_tac >>
  `mem_bytes_at (D+k) (LENGTH bs) mm = TAKE (LENGTH bs) (word_to_bytes wd T)` by
    (pop_assum (SUBST1_TAC o SYM) >>
     simp[rich_listTheory.TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]) >>
  pop_assum SUBST1_TAC >>
  simp[Abbr `wd`, word_of_bytes_be_pad_right, GSYM byteTheory.word_to_bytes_be_def,
       TAKE_word_to_bytes_be_word_of_bytes_be]
QED

Theorem concat_fixed_store_offset:
  !t s ob x d w.
    t.vs_memory = (mstore ob x (mstore d w s)).vs_memory ==>
    mload ob t = x
Proof
  rpt strip_tac >>
  `mload ob t = mload ob (mstore ob x (mstore d w s))` by simp[mload_def] >>
  gvs[mload_mstore_same]
QED

Theorem concat_fixed_store_memory_frame:
  !s t d ob w x.
    t.vs_memory = (mstore ob x (mstore d w s)).vs_memory ==>
    mem_agree_outside
      ({i | d <= i /\ i < d+32} UNION {i | ob <= i /\ i < ob+32})
      t.vs_memory s.vs_memory
Proof
  rpt strip_tac >> simp[mem_agree_outside_def] >> rpt strip_tac >>
  `mem_agree_outside {i | ob <= i /\ i < ob+32}
    (mstore ob x (mstore d w s)).vs_memory (mstore d w s).vs_memory` by
    simp[mstore_memory_frame] >>
  `mem_agree_outside {i | d <= i /\ i < d+32}
    (mstore d w s).vs_memory s.vs_memory` by simp[mstore_memory_frame] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem concat_fixed_taint_frame:
  !tn tnf d ob.
    tnf.t_mem = tn.t_mem DIFF
      ({i | d <= i /\ i < d+32} UNION {i | ob <= i /\ i < ob+32}) ==>
    (!i. (d <= i /\ i < d+32) \/ (ob <= i /\ i < ob+32) ==>
      i NOTIN tnf.t_mem) /\
    (!i. ~((d <= i /\ i < d+32) \/ (ob <= i /\ i < ob+32)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p n. (!i. p <= i /\ i < p+n ==> i NOTIN tn.t_mem) ==>
      !i. p <= i /\ i < p+n ==> i NOTIN tnf.t_mem)
Proof
  simp[] >> rpt strip_tac >> gvs[]
QED

(* Consumer boundary: full-word access is required even for an empty payload.
   Only the logical prefix, rather than padding, must avoid the offset cell. *)
Theorem concat_fixed_arm_ptr:
  !D ctx fn PG G tn s bb id root off tmp dst next value a b bs k cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var off] [tmp]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MSTORE [Var dst; value] []) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var tmp; Lit (n2w (LENGTH bs))] [next]) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (id+4) MSTORE [Var off; Var next] []) /\
    lookup_var off s = SOME b /\ lookup_var root s = SOME a /\
    ptr_covers G tn off s 32 /\ ptr_covers G tn root s cap /\
    mload (w2n b) s = n2w k /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
    (!i. w2n a <= i /\ i < w2n a+k ==> i NOTIN tn.t_mem) /\
    k+32 <= cap /\ w2n a+k < dimword(:256) /\ LENGTH bs <= 32 /\
    (w2n a+(k+LENGTH bs) <= w2n b \/ w2n b+32 <= w2n a) /\
    root <> tmp /\ root <> dst /\ root <> next /\ tmp <> dst /\
    off <> tmp /\ off <> dst /\ off <> next /\ dst <> next /\
    (!q. value = Var q ==> q <> tmp /\ q <> dst) /\
    eval_operand value s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
    op_taint tn value = {} ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      mem_bytes_at (w2n a) (k+LENGTH bs) t.vs_memory =
        mem_bytes_at (w2n a) k s.vs_memory ++ bs /\
      mload (w2n b) t = n2w (k+LENGTH bs) /\
      ptr_covers Gf tnf root t cap /\ ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s.vs_allocas /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
      t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
      t.vs_inst_idx = s.vs_inst_idx+5 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      (!i. w2n a <= i /\ i < w2n a+k+LENGTH bs ==> i NOTIN tnf.t_mem) /\
      (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
      tnf.t_mem = tn.t_mem DIFF
        ({i | w2n a+k <= i /\ i < w2n a+k+32} UNION
         {i | w2n b <= i /\ i < w2n b+32}) /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      mem_agree_outside
        ({i | w2n a+k <= i /\ i < w2n a+k+32} UNION
         {i | w2n b <= i /\ i < w2n b+32}) t.vs_memory s.vs_memory /\
      (!q. q <> tmp /\ q <> dst /\ q <> next ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> (
  drule_all concat_fixed_arm_counted >>
  disch_then (qspecl_then [`D`, `PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf`
      (qx_choose_then `t` strip_assume_tac)))) >>
  `w2n (a+n2w k) = w2n a+k` by
    (`k < dimword(:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "prefix" >>
  conj_tac >- suspend "offset" >>
  conj_tac >- suspend "root" >>
  simp[] >> suspend "frames")
QED

Resume concat_fixed_arm_ptr[prefix]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  (asm_rewrite_tac[] >> irule concat_fixed_store_prefix >> simp[])
QED

Resume concat_fixed_arm_ptr[offset]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  (rewrite_tac[GSYM word_add_n2w] >> irule concat_fixed_store_offset >>
   goal_assum (drule_at Any))
QED

Resume concat_fixed_arm_ptr[root]:
  markerLib.RESUME_TAC >> rpt strip_tac >> (
  `lookup_var root t = lookup_var root s /\
   FLOOKUP Gf root = FLOOKUP G root /\
   op_taint tnf (Var root) = op_taint tn (Var root)` by
    (first_x_assum (qspec_then `root` mp_tac) >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def, op_prov_def])
QED

Resume concat_fixed_arm_ptr[frames]:
  markerLib.RESUME_TAC >> (
  conj_tac >-
    (rpt strip_tac >> Cases_on `i < w2n a+k` >> simp[] >>
     first_x_assum irule >> simp[]) >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  irule concat_fixed_store_memory_frame >>
  qexistsl_tac [`word_of_bytes_be (PAD_RIGHT 0w 32 bs)`,
    `n2w k+n2w (LENGTH bs)`] >> simp[])
QED

Finalise concat_fixed_arm_ptr
