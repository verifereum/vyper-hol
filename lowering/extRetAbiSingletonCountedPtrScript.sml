(* Counted phases of singleton dynamic ABI encoding. *)
Theory extRetAbiSingletonCountedPtr
Ancestors
  extRetAbiArrayInitPtr extRetAbiBytesCountedPtr extRetAbiWrappedSourcePtr
  abiEncoderComplexCode abiEncoderMemberCode abiEncoderChildCode abiBuiltinAllocation
  extRetBulkCopyCountedPtr extRetCountedPtr extRetBytesCopyCountedPtr
  fragGasPathPtr fragGasSeqPtr fragExec emitHelperProps exprLoweringProps
  context compileEnv emitHelper exprLowering ptrDiscipline bodyPtrDefs venomState venomExecSemantics
  venomMemProps
  valueEncodingProps valueEncodingProofs words finite_map pred_set arithmetic

Theorem abi_encode_singleton_prefix_counted_ptr:
  abi_encode_complex_prefix [(ei,32,cap,T)] sa = (Var ip,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 32w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_complex_prefix _ _ = _` mp_tac >>
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `fn_has_code sa sb fn` >>
  rename1 `emit_op ALLOCA _ sa = (Var ip,sc)` >>
  `cs_extends sa sc` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sc sb` by
    metis_tac[cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all emit_alloca_index_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Lit 32w) sf = SOME 32w /\ op_taint tnf (Lit 32w) = {}` by
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
    (`mload addr sf' = mload addr (mstore addr 32w sf)` by simp[mload_def] >>
     simp[mload_mstore_same]) >>
  conj_tac >-
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     `mem_bytes_at i 1 (mstore addr 32w sf).vs_memory = mem_bytes_at i 1 sf.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >> simp[]) >>
  rpt strip_tac >> simp[IN_DIFF] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

(* The head address and the clean cursor read preceding the child call. *)
Theorem abi_singleton_head_cursor_counted_ptr:
  emit_op ADD [Var dst; Lit 0w] sa = (Var head,sb) /\
  emit_op MLOAD [Var ip] sb = (Var off,sc) /\
  fn_has_code sa sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  lookup_var dst s = SOME (n2w b) /\ b < dimword(:256) /\
  ptr_covers G tn dst s cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var head sf = SOME (n2w b) /\ ptr_covers Gf tnf head sf cap /\
    lookup_var off sf = SOME (mload cursor s) /\
    op_taint tnf (Var off) = {} /\ op_prov Gf (Var off) = NONE /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule fn_has_code_split >> simp[]) >>
  `sb.cs_next_var = sa.cs_next_var+1 /\ not_fresh_at sb head /\
   (!v. not_fresh_at sa v ==> not_fresh_at sb v)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
  `0 + cap <= cap /\ w2n (n2w b : bytes32) + 0 < dimword(:256)` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all (emit_bulk_offset_counted_ptr |> SPEC_ALL |>
    Q.INST [`off` |-> `0`, `n` |-> `cap`, `extent` |-> `cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var ip sf = SOME (n2w cursor) /\ ptr_covers Gf tnf ip sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!i. w2n (n2w cursor : bytes32) <= i /\
       i < w2n (n2w cursor : bytes32)+32 ==> i NOTIN tnf.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD, mload_def] >>
  gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem abi_singleton_child_prefix_counted_ptr:
  abi_encode_child_prefix (Var dst) 0 (Var ip) sa =
    ((Var head,Var off,Var child),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+32 < dimword(:256) /\
  ptr_covers G tn dst s (32+cap) /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = 32w /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var head sf = SOME (n2w b) /\ ptr_covers Gf tnf head sf (32+cap) /\
    lookup_var off sf = SOME 32w /\ op_taint tnf (Var off) = {} /\
    lookup_var child sf = SOME (n2w (b+32)) /\ ptr_covers Gf tnf child sf cap /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> rename1 `fn_has_code sa sb fn` >>
  rename1 `emit_op ADD [Var dst; Lit 0w] sa = (Var head,sc)` >>
  rename1 `emit_op MLOAD [Var ip] sc = (Var off,sd)` >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sd fn /\ fn_has_code sd sb fn /\ fn_has_code sa sd fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `not_fresh_at sd head /\ not_fresh_at sd off /\
   (!v. not_fresh_at sa v ==> not_fresh_at sd v)` by
    (qpat_x_assum `emit_op ADD [Var dst; Lit 0w] _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `b < dimword(:256)` by decide_tac >>
  drule_all abi_singleton_head_cursor_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME (n2w b) /\ ptr_covers Gf tnf dst sf (32+cap) /\
   lookup_var off sf = SOME (n2w 32) /\
   w2n (n2w b : bytes32)+32 < dimword(:256) /\ 32+cap <= 32+cap` by
    (gvs[ptr_covers_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all (abi_bytes_lastptr_counted_ptr |> SPEC_ALL |>
    Q.INST [`off` |-> `32`, `n` |-> `cap`, `extent` |-> `32+cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >> gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem abi_singleton_child_suffix_counted_ptr:
  abi_encode_child_suffix (Var head) (Var ip) (Var off) (Var len) sa =
    (Var len,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa head /\ not_fresh_at sa ip /\
  lookup_var head s = SOME (n2w b) /\ b < dimword(:256) /\
  ptr_covers G tn head s 32 /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\
  lookup_var off s = SOME 32w /\ op_taint tn (Var off) = {} /\
  lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore cursor (n2w (32+n)) (mstore b 32w s)).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF
      {i | cursor <= i /\ i < cursor+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_suffix _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> rename1 `fn_has_code sa sb fn` >>
  rename1 `emit_void MSTORE [Var head; Var off] sa = ((),sc)` >>
  rename1 `emit_op ADD [Var off; Var len] sc = (next,sd)` >>
  `?nextvar. next = Var nextvar` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!v. not_fresh_at sa v ==> not_fresh_at sc v` by
    (qpat_x_assum `emit_void MSTORE _ sa = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
          emit_def, comp_return_def, not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand (Var off) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var off) sf = SOME 32w /\
   eval_operand (Var len) sf = SOME (n2w n) /\
   op_taint tnf (Var off) = {} /\ op_taint tnf (Var len) = {}` by
    simp[eval_operand_def] >>
  drule_all (emit_copy_len_binop_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var ip sf' = SOME (n2w cursor) /\ ptr_covers Gf tnf' ip sf' 32 /\
   eval_operand (Var nextvar) sf' = SOME (n2w (32+n)) /\
   op_taint tnf' (Var nextvar) = {}` by
    (gvs[ptr_covers_def, eval_operand_def, GSYM word_add_n2w] >> metis_tac[]) >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf''`, `sf''`] >>
  conj_tac >- suspend "path" >>
  simp[w2n_n2w, LESS_MOD] >>
  `sf'.vs_memory = (mstore b 32w s).vs_memory` by simp[w2n_n2w, LESS_MOD] >>
  qpat_x_assum `sf'.vs_memory = sf.vs_memory` kall_tac >>
  qpat_x_assum `sf.vs_memory = _` kall_tac >>
  qabbrev_tac `inner = mstore b 32w s` >>
  pure_rewrite_tac[mstore_def, write_memory_with_expansion_def, LET_THM] >>
  BETA_TAC >> pure_rewrite_tac[venom_state_accfupds] >>
  qpat_x_assum `sf'.vs_memory = _` (fn th => pure_rewrite_tac[th]) >> REFL_TAC
QED

Resume abi_singleton_child_suffix_counted_ptr[path]:
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`G`, `sf`, `tnf`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf`, `sf'`, `tnf'`] >> simp[]
QED

Finalise abi_singleton_child_suffix_counted_ptr
