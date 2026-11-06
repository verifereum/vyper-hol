Theory extRetAbiChildBoundaryPtr
Ancestors extRetAbiSingletonCountedPtr extRetAbiBytesCountedPtr
  extRetBulkCopyCountedPtr extRetBytesCopyCountedPtr abiEncoderChildCode
  fragGasPathPtr fragExec emitHelperProps exprLoweringProps
  context compileEnv emitHelper ptrDiscipline bodyPtrDefs venomState venomExecSemantics
  valueEncoding venomMemProps words finite_map pred_set arithmetic

Theorem abi_child_prefix_ambient_counted_ptr:
  abi_encode_child_prefix (Var dst) h (Var ip) sa =
    ((Var head,Var off,Var child),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= cap /\ k <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var head sf = SOME (n2w (b+h)) /\ ptr_covers Gf tnf head sf 32 /\
    lookup_var off sf = SOME (n2w k) /\ op_taint tnf (Var off) = {} /\
    lookup_var child sf = SOME (n2w (b+k)) /\ ptr_covers Gf tnf child sf (cap-k) /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
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
  rename1 `emit_op ADD [Var dst; Lit (n2w h)] sa = (Var head,sc)` >>
  rename1 `emit_op MLOAD [Var ip] sc = (Var off,sd)` >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `not_fresh_at sc head /\ not_fresh_at sd head /\ not_fresh_at sd off /\
   (!v. not_fresh_at sa v ==> not_fresh_at sc v /\ not_fresh_at sd v)` by
    (qpat_x_assum `emit_op ADD [Var dst; Lit _] _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `b < dimword(:256) /\ w2n (n2w b : bytes32)+h < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_all (emit_bulk_offset_ambient_counted_ptr |> SPEC_ALL |>
    Q.INST [`off` |-> `h`, `n` |-> `32`, `extent` |-> `cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var ip sf = SOME (n2w cursor) /\ ptr_covers Gf tnf ip sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!i. w2n (n2w cursor : bytes32) <= i /\
       i < w2n (n2w cursor : bytes32)+32 ==> i NOTIN tnf.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME (n2w b) /\ ptr_covers Gf' tnf' dst sf' cap /\
   lookup_var off sf' = SOME (n2w k) /\
   w2n (n2w b : bytes32)+k < dimword(:256) /\ k+(cap-k) <= cap` by
    (gvs[ptr_covers_def, w2n_n2w, LESS_MOD, mload_def] >>
     metis_tac[]) >>
  drule_all (abi_bytes_lastptr_ambient_counted_ptr |> SPEC_ALL |>
    Q.INST [`off` |-> `k`, `n` |-> `cap-k`, `extent` |-> `cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >> gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem abi_child_suffix_ambient_counted_ptr:
  abi_encode_child_suffix (Var head) (Var ip) (Var off) (Var len) sa =
    (Var len,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa head /\ not_fresh_at sa ip /\
  lookup_var head s = SOME (n2w b) /\ b < dimword(:256) /\
  ptr_covers G tn head s 32 /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\
  lookup_var off s = SOME (n2w k) /\ op_taint tn (Var off) = {} /\
  lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
  k+n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore cursor (n2w (k+n)) (mstore b (n2w k) s)).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF
      {i | cursor <= i /\ i < cursor+32} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
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
  `eval_operand (Var off) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var off) sf = SOME (n2w k) /\
   eval_operand (Var len) sf = SOME (n2w n) /\
   op_taint tnf (Var off) = {} /\ op_taint tnf (Var len) = {}` by
    simp[eval_operand_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var ip sf' = SOME (n2w cursor) /\ ptr_covers Gf tnf' ip sf' 32 /\
   eval_operand (Var nextvar) sf' = SOME (n2w (k+n)) /\
   op_taint tnf' (Var nextvar) = {}` by
    (gvs[ptr_covers_def, eval_operand_def, GSYM word_add_n2w] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf'`, `tnf'`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >>
  `sf'.vs_memory = (mstore b (n2w k) s).vs_memory` by simp[w2n_n2w, LESS_MOD] >>
  qpat_x_assum `sf'.vs_memory = sf.vs_memory` kall_tac >>
  qpat_x_assum `sf.vs_memory = _` kall_tac >>
  qabbrev_tac `inner = mstore b (n2w k) s` >>
  pure_rewrite_tac[mstore_def, write_memory_with_expansion_def, LET_THM] >>
  BETA_TAC >> pure_rewrite_tac[venom_state_accfupds] >>
  qpat_x_assum `sf'.vs_memory = _` (fn th => pure_rewrite_tac[th]) >> REFL_TAC
QED

(* The cursor store is last, so even head/cursor disjointness is unnecessary. *)
Theorem abi_child_suffix_cursor_clean:
  sf.vs_memory = (mstore cursor (n2w (k+n)) (mstore b (n2w k) s)).vs_memory /\
  tnf.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF
    {i | cursor <= i /\ i < cursor+32} ==>
  mload cursor sf = n2w (k+n) /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> reverse conj_tac >- simp[] >>
  qspec_then `cursor` mp_tac mload_mstore_same >>
  disch_then (qspecl_then [`n2w (k+n)`, `mstore b (n2w k) s`] mp_tac) >>
  simp[mload_def]
QED
