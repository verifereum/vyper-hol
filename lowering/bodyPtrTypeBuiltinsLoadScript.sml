Theory bodyPtrTypeBuiltinsLoad
Ancestors
  typedCopyPtr fragGasSeqPtr ghostPcTransportPtr emitHelperProps
  venomExecSemantics venomInstProofs venomInst venomState finite_map
  ptrDiscipline ptrSafeRun fragGasPathPtr

Theorem mload_ambient_frame:
  !PG G tn s id src out a p.
    p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn) (Var p) =
      op_taint tn (Var p)
Proof
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem mload_counted_path:
  !D ctx fn PG G tn s bb id src out a.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MLOAD [Var src] [out])
        (update_var out (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [out]) s
        (update_var out (mload (w2n a) s) s) tn)
      (OK ((update_var out (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
    (OK ((update_var out (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[mk_inst_def] >> irule (SRULE [mk_inst_def]
       (Q.INST [`i` |-> `mk_inst id MLOAD [Var src] [out]`]
         straight_line_ptr_edge)) >>
     simp[GSYM mk_inst_def, ptr_inst_ok_mload, step_MLOAD, eval_operand_def,
          is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  pure_rewrite_tac [arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> simp[gas_path_ptr_rules, update_var_def]
QED

Theorem mload_counted_clean_ambient:
  !D ctx fn PG G tn s bb id src out a.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      t = (update_var out (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx /\
      lookup_var out t = SOME (mload (w2n a) s) /\
      op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
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
  drule_all mload_counted_path >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id MLOAD [Var src] [out])
    (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [out]) s
    (update_var out (mload (w2n a) s) s) tn`,
    `(update_var out (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[] >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       mload_ambient_frame, op_prov_def, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def]
QED
