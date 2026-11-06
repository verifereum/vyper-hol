Theory bodyPtrTypeBuiltinsSourceCompile
Ancestors
  bodyPtrTypeBuiltinsSourceFrame builtinBytes emitHelperProps compileEnv exprLoweringProps
  ASCIInumbers rich_list

Theorem compile_bytestring_src_shape_fresh:
  !src sb len_op data_op sc.
    compile_bytestring_src (Var src) sb = ((len_op,data_op),sc) /\
    not_fresh_at sb src ==>
    ?len data.
      len_op = Var len /\ data_op = Var data /\
      emitted_insts sb sc =
        [mk_inst sb.cs_next_id MLOAD [Var src] [len];
         mk_inst (sb.cs_next_id+1) ADD [Var src; Lit 32w] [data]] /\
      ALL_DISTINCT [src;len;data] /\
      ~not_fresh_at sb len /\ ~not_fresh_at sb data /\
      not_fresh_at sc src /\ not_fresh_at sc len /\ not_fresh_at sc data /\
      sc.cs_next_var = sb.cs_next_var + 2 /\
      LENGTH sc.cs_current_insts = LENGTH sb.cs_current_insts + 2 /\
      sc.cs_current_bb = sb.cs_current_bb
Proof
  rpt gen_tac >>
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  imp_res_tac emit_op_extends >>
  gvs[same_blocks_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_bytestring_src_counted_frame:
  !D ctx fn PG G tn s bb src a capacity d cenv cx es es0 sa G0 tn0 s0
   sb sc len_op data_op.
    compile_bytestring_src (Var src) sb = ((len_op,data_op),sc) /\
    not_fresh_at sb src /\ sa.cs_next_var <= sb.cs_next_var /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!j. j < LENGTH (emitted_insts sb sc) ==>
      get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts sb sc))) /\
    lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 32 <= capacity /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ghost_inv d cenv cx es G tn s /\
    ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at sb p) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) ==>
    ?len data G' tn' t.
      len_op = Var len /\ data_op = Var data /\ ALL_DISTINCT [src;len;data] /\
      not_fresh_at sc src /\ not_fresh_at sc len /\ not_fresh_at sc data /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      lookup_var len t = SOME (mload (w2n a) s) /\
      op_taint tn' (Var len) = {} /\ op_prov G' (Var len) = NONE /\
      lookup_var data t = SOME (a+32w) /\
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
        ptr_covers G' tn' data t n) /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_bytestring_src_shape_fresh >>
  disch_then (qx_choose_then `len` (qx_choose_then `data` strip_assume_tac)) >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sb.cs_next_id MLOAD [Var src] [len]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sb.cs_next_id+1) ADD [Var src; Lit 32w] [data])` by
    (qpat_x_assum `!j. j < LENGTH (emitted_insts sb sc) ==> _` mp_tac >> simp[] >>
     disch_then (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
     simp[arithmeticTheory.ADD1]) >>
  `~not_fresh_at sa len /\ ~not_fresh_at sa data` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `(!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       p <> len /\ p <> data) /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> len /\ p <> data) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> len /\ p <> data)` by
    metis_tac[] >>
  drule_all bytestring_source_prefix_ghost_frame >>
  disch_then (qspecl_then [`D`,`PG`]
    (qx_choose_then `G'` (qx_choose_then `tn'` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`len`,`data`,`G'`,`tn'`,`t`] >> simp[]
QED
