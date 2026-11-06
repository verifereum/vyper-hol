(* Counted scratch index initialization, including reused allocation sites. *)
Theory extRetAbiArrayInitPtr
Ancestors
  extRetBulkCopyCountedPtr extRetCountedPtr abiDecoderIndexInit
  extRetBytesCopyCountedPtr allocaFootprint fragExecPtr
  abiBuiltinAllocation allocationPtr robustCopyTransportPtr abiEncoderInputFrame
  fragGasSeqPtr fragGasPathPtr fragExec emitHelperProps exprLoweringProps compileEnv emitHelper context
  ptrDiscipline ptrSafeRun bodyPtrDefs venomState venomInst venomExecSemantics
  codegenRel venomMemProps valueEncodingProps valueEncodingProofs words finite_map pred_set arithmetic

Theorem emit_alloca_index_ambient_counted_ptr:
  emit_op ALLOCA [Lit 32w] sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
        fresh_id_def, emit_def] >>
  `!v. not_fresh_at sa v ==> v <> ip` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
          fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
     gvs[not_fresh_at_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]` >>
  qabbrev_tac `u = update_var ip (n2w addr)
    (abi_builtin_allocate_state sa.cs_next_id 32 s)` >>
  qabbrev_tac `Gf = step_prov PG G inst u` >>
  qabbrev_tac `tnf = step_taint inst s u tn` >>
  `step_inst_base inst s = OK u` by
    (simp[Abbr `inst`, Abbr `u`] >> irule step_alloca_site >>
     simp[wordsTheory.dimword_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `tnf` >> qunabbrev_tac `Gf` >>
     irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_alloca) >> simp[]) >>
  `ptr_covers Gf tnf ip (u with vs_inst_idx := SUC s.vs_inst_idx) 32` by
    (simp[ptr_covers_def, Abbr `Gf`, Abbr `tnf`, Abbr `inst`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
          op_taint_def, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, LESS_MOD] >> `addr < dimword(:256)` by decide_tac >>
     simp[LESS_MOD] >> metis_tac[]) >>
  simp[Abbr `u`, abi_builtin_allocate_state_def, update_var_def,
       lookup_var_def, arithmeticTheory.ADD1] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >>
  (gvs[Abbr `Gf`, Abbr `tnf`, Abbr `inst`, step_prov_def, set_prov_def,
      out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
      mk_inst_def, imm_taint_def, store_taint_def, adopt_reset_def, op_taint_def,
      abi_builtin_allocate_state_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> rpt disch_tac >>
  reverse conj_tac >-
    (rpt strip_tac >> `v <> ip` by metis_tac[] >> simp[]) >>
  qpat_x_assum `FLOOKUP s.vs_allocas _ = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
       range_bytes_def, written_taint_def, FLOOKUP_UPDATE,
       source_memory_write_ranges_def, eval_operand_def, FLOOKUP_DEF,
       FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> (eq_tac >-
    (strip_tac >> gvs[] >> decide_tac) >> simp[]))
QED


Theorem emit_alloca_index_counted_ptr:
  emit_op ALLOCA [Lit 32w] sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >> metis_tac[]
QED

Theorem abi_decode_index_init_counted_ptr:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ALLOCA _ sa = (Var ip,sc)` >>
  `cs_extends sa sc` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sc sb` by
    metis_tac[cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Lit 0w) sf = SOME 0w /\ op_taint tnf (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `ptr_covers Gf tnf' ip sf' 32` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  simp[w2n_n2w, LESS_MOD] >>
  conj_tac >-
    (`mload addr sf' = mload addr (mstore addr 0w sf)` by
       simp[mload_def] >> simp[mload_mstore_same]) >>
  conj_tac >-
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     `mem_bytes_at i 1 (mstore addr 0w sf).vs_memory =
      mem_bytes_at i 1 sf.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >>
     simp[]) >>
  rpt strip_tac >> simp[IN_DIFF] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem abi_decode_index_init_source_counted_ptr:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\ ptr_covers G tn src s cap /\
  (w2n a+cap <= addr \/ addr+32 <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input info ty v (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf cap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input info ty v (w2n a) cap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_index_init_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n a) cap sf.vs_memory = mem_bytes_at (w2n a) cap s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (w2n a+x) 1 sf.vs_memory = mem_bytes_at (w2n a+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  `!i. i < cap ==> (w2n a+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input info ty v (w2n a) cap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED
