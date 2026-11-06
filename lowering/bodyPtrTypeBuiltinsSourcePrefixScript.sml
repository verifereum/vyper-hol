Theory bodyPtrTypeBuiltinsSourcePrefix
Ancestors
  bodyPtrTypeBuiltinsLoad typedCopyPtr typedCopyLoopHeaderPtr fragGasSeqPtr
  fragGasPathPtr ghostPcTransportPtr emitHelperProps ptrDiscipline ptrSafeRun bodyPtrDefs
  venomExecSemantics venomInstProofs venomInst venomState finite_map

Theorem add_counted_path:
  !D ctx fn PG G tn s bb id left right out a b.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id ADD [left;right] [out])
        (update_var out (a+b) s))
      (step_taint (mk_inst id ADD [left;right] [out]) s
        (update_var out (a+b) s) tn)
      (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s))
    (step_taint (mk_inst id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[mk_inst_def] >> irule (SRULE [mk_inst_def]
       (Q.INST [`i` |-> `mk_inst id ADD [left;right] [out]`]
         straight_line_ptr_edge)) >>
     simp[GSYM mk_inst_def, ptr_inst_ok_copy_len_binop, step_ADD,
          is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  pure_rewrite_tac [arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> simp[gas_path_ptr_rules, update_var_def]
QED

Theorem add_counted_ambient:
  !D ctx fn PG G tn s bb id left right out a b.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      G' = step_prov PG G (mk_inst id ADD [left;right] [out])
        (update_var out (a+b) s) /\
      tn' = step_taint (mk_inst id ADD [left;right] [out]) s
        (update_var out (a+b) s) tn /\
      t = ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
      lookup_var out t = SOME (a+b) /\ op_taint tn' (Var out) = {} /\
      t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
      (!p. p <> out ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  drule_all add_counted_path >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id ADD [left;right] [out])
    (update_var out (a+b) s)`,
    `step_taint (mk_inst id ADD [left;right] [out]) s
    (update_var out (a+b) s) tn`,
    `(update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       copy_len_binop_ghost_frame] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def]
QED

Theorem bytestring_source_prefix_counted:
  !D ctx fn PG G tn s bb id1 id2 src len data a capacity.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id1 MLOAD [Var src] [len]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ADD [Var src; Lit 32w] [data]) /\
    ALL_DISTINCT [src;len;data] /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      lookup_var len t = SOME (mload (w2n a) s) /\
      op_taint tn' (Var len) = {} /\ lookup_var data t = SOME (a+32w) /\
      t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC (SUC s.vs_inst_idx) /\
      t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
      (!p. p <> len /\ p <> data ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p)) /\
      (!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
        ptr_covers G' tn' data t n)
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all mload_counted_clean_ambient >>
  disch_then (qspecl_then [`D`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1`
      (qx_choose_then `s1` strip_assume_tac)))) >>
  qpat_x_assum `s1 = update_var _ _ _ with vs_inst_idx := _` kall_tac >>
  `~s1.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `lookup_var src s1 = SOME a /\ op_taint tn1 (Var src) = {} /\
   ptr_covers G1 tn1 src s1 capacity` by
    (gvs[listTheory.ALL_DISTINCT, ptr_covers_def] >> metis_tac[]) >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst id2 ADD [Var src; Lit 32w] [data]) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_operand (Var src) s1 = SOME a /\
   eval_operand (Lit 32w) s1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all add_counted_ambient >>
  disch_then (qspecl_then [`D`,`PG`,`G1`]
    (qx_choose_then `G2` (qx_choose_then `tn2`
      (qx_choose_then `s2` strip_assume_tac)))) >>
  `!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
    ptr_covers G2 tn2 data s2 n` by
    (rpt strip_tac >>
     qpat_x_assum `G2 = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `tn2 = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `s2 = (update_var _ _ _) with vs_inst_idx := _`
       (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac [ptr_covers_inst_idx] >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def] >> conj_tac
     >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[]) >>
     qexists_tac `capacity` >> simp[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`G2`,`tn2`,`s2`] >>
  conj_tac >-
    (qpat_assum `gas_path_ptr _ _ _ _ _ _ _ s _ _ _ (OK s1)`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     simp[] >> disch_then drule >> simp[]) >>
  qpat_x_assum `G2 = _` kall_tac >>
  qpat_x_assum `tn2 = _` kall_tac >> qpat_x_assum `s2 = _` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[] >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `s1 = s with <| vs_vars := _; vs_inst_idx := _ |>`
    (fn th => once_rewrite_tac[th]) >> simp[update_var_def]
QED
