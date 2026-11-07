Theory extRetAbiChildComposePtr
Ancestors abiEncoderChildContext extRetAbiChildBoundaryPtr extRetAbiBytesCountedPtr
  extRetBulkCopyCountedPtr extRetBytesCopyCountedPtr abiEncoderChildCode
  fragGasPathPtr fragExec emitHelperProps exprLoweringProps
  context compileEnv emitHelper ptrDiscipline bodyPtrDefs venomState venomExecSemantics
  valueEncoding venomMemProps words finite_map pred_set arithmetic
  venomInst venomInstProofs ptrSafeRun fragExecPtr typedCopyPtr contextCodegenRel

Theorem child_mstore_exact_counted_ptr[local]:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore (w2n a) w s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sf = ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst;value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MSTORE [Var dst;value] []` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `step_prov PG G inst t = G /\ tnf.t_var = tn.t_var /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (simp[Abbr `inst`, Abbr `t`, Abbr `tnf`] >>
     irule mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t) tnf
       (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     qunabbrev_tac `tnf` >> irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >> simp[]) >>
  simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
       Abbr `tnf`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def,
       lookup_var_def, op_taint_def]
QED

(* The recursive encoder may return a literal rather than a variable. *)
Theorem abi_child_suffix_operand_counted_ptr:
  abi_encode_child_suffix (Var head) (Var ip) (Var off) len sa = (len,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa head /\ not_fresh_at sa ip /\
  lookup_var head s = SOME (n2w b) /\ b < dimword(:256) /\
  ptr_covers G tn head s 32 /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\
  lookup_var off s = SOME (n2w k) /\ op_taint tn (Var off) = {} /\
  eval_operand len s = SOME (n2w n) /\ op_taint tn len = {} /\
  k+n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore cursor (n2w (k+n)) (mstore b (n2w k) s)).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF
      {i | cursor <= i /\ i < cursor+32} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_fmp = s.vs_fmp /\
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
  rename1 `emit_op ADD [Var off; len] sc = (next,sd)` >>
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
  drule_all child_mstore_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var off) sf = SOME (n2w k) /\
   eval_operand len sf = SOME (n2w n) /\
   op_taint tnf (Var off) = {} /\ op_taint tnf len = {}` by
    (Cases_on `len` >> gvs[eval_operand_def, op_taint_def,
       mstore_def, write_memory_with_expansion_def]) >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var ip sf' = SOME (n2w cursor) /\ ptr_covers Gf tnf' ip sf' 32 /\
   eval_operand (Var nextvar) sf' = SOME (n2w (k+n)) /\
   op_taint tnf' (Var nextvar) = {}` by
    (gvs[ptr_covers_def, eval_operand_def, GSYM word_add_n2w] >> metis_tac[]) >>
  drule_all child_mstore_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `sf = _ with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `sf'' = _ with vs_inst_idx := _` kall_tac >>
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

(* writes includes recursive scratch writes as well as the encoded destination.
   The callback is deliberately explicit: this rule supplies no recursive
   execution or scratch allocation theorem. *)
Theorem abi_dynamic_child_compose_counted_ptr:
  compile_abi_encode_child (Var dst) src ei T h (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= cap /\ k <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  h+32 <= k /\ k+n < dimword(:256) /\
  (cursor+32 <= b+k \/ b+k+n <= cursor) /\
  (!head off child sc len sd Gp tnp sp.
    abi_encode_child_prefix (Var dst) h (Var ip) sa =
      ((Var head,Var off,Var child),sc) /\
    compile_abi_encode_to_buf (Var child) src ei sc = (len,sd) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gp tnp (OK sp) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+h)) /\ ptr_covers Gp tnp head sp 32 /\
    lookup_var off sp = SOME (n2w k) /\ op_taint tnp (Var off) = {} /\
    lookup_var child sp = SOME (n2w (b+k)) /\ ptr_covers Gp tnp child sp (cap-k) /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    tnp.t_imm = tn.t_imm /\ sp.vs_accounts = s.vs_accounts /\
    sp.vs_transient = s.vs_transient /\ sp.vs_call_ctx = s.vs_call_ctx /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sp = lookup_var v s /\ FLOOKUP Gp v = FLOOKUP G v /\
      op_taint tnp (Var v) = op_taint tn (Var v)) ==>
    ?Gm tnm sm.
      gas_path_ptr D 0 ctx fn PG Gp tnp sp cost Gm tnm (OK sm) /\
      sm.vs_current_bb = sd.cs_current_bb /\
      sm.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sm.vs_halted /\
      lookup_var head sm = SOME (n2w (b+h)) /\ ptr_covers Gm tnm head sm 32 /\
      lookup_var ip sm = SOME (n2w cursor) /\ ptr_covers Gm tnm ip sm 32 /\
      lookup_var off sm = SOME (n2w k) /\ op_taint tnm (Var off) = {} /\
      eval_operand len sm = SOME (n2w n) /\ op_taint tnm len = {} /\
      (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnm.t_mem) /\
      mem_agree_outside writes sm.vs_memory sp.vs_memory /\
      (!i. i NOTIN writes ==> (i IN tnm.t_mem <=> i IN tnp.t_mem)) /\
      tnm.t_imm = tnp.t_imm /\ sm.vs_accounts = sp.vs_accounts /\
      sm.vs_transient = sp.vs_transient /\ sm.vs_call_ctx = sp.vs_call_ctx /\
      tnm.t_stor = tnp.t_stor /\ tnm.t_trans = tnp.t_trans /\
      (!v. not_fresh_at sa v ==>
        lookup_var v sm = lookup_var v sp /\ FLOOKUP Gm v = FLOOKUP Gp v /\
        op_taint tnm (Var v) = op_taint tnp (Var v))) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside (writes UNION {i | b+h <= i /\ i < b+h+32} UNION
      {i | cursor <= i /\ i < cursor+32}) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN (writes UNION {i | b+h <= i /\ i < b+h+32} UNION
      {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `?head off child. ops = (Var head,Var off,Var child) /\
    not_fresh_at prepared head /\ not_fresh_at prepared off /\
    not_fresh_at prepared child` by
    (qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
     simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def]) >> gnvs[] >>
  `h+32 <= cap /\ cursor < dimword(:256)` by decide_tac >>
  drule_all abi_child_prefix_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `!Gp tnp sp. _` (qspecl_then [`Gf`, `tnf`, `sf`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `not_fresh_at child_end head /\ not_fresh_at child_end ip /\
   (!v. not_fresh_at sa v ==> not_fresh_at child_end v) /\
   b+h < dimword(:256)` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  drule abi_encode_child_suffix_shape >> strip_tac >> gnvs[] >>
  `not_fresh_at child_end ip /\ lookup_var ip sm = SOME (n2w cursor) /\
   cursor < dimword(:256) /\ b+h < dimword(:256)` by
    (simp[] >> decide_tac) >>
  `?Gz tnz sz.
    gas_path_ptr D 0 ctx fn PG Gm tnm sm 0 Gz tnz (OK sz) /\
    sz.vs_current_bb = sb.cs_current_bb /\
    sz.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sz.vs_halted /\
    sz.vs_memory = (mstore cursor (n2w (k+n)) (mstore (b+h) (n2w k) sm)).vs_memory /\
    tnz.t_mem = (tnm.t_mem DIFF {i | b+h <= i /\ i < b+h+32}) DIFF
      {i | cursor <= i /\ i < cursor+32} /\
    sz.vs_allocas = sm.vs_allocas /\ sz.vs_alloca_next = sm.vs_alloca_next /\ sz.vs_fmp = sm.vs_fmp /\
    tnz.t_imm = tnm.t_imm /\ sz.vs_accounts = sm.vs_accounts /\
    sz.vs_transient = sm.vs_transient /\ sz.vs_call_ctx = sm.vs_call_ctx /\
    tnz.t_stor = tnm.t_stor /\ tnz.t_trans = tnm.t_trans /\
    (!v. not_fresh_at child_end v ==>
      lookup_var v sz = lookup_var v sm /\ FLOOKUP Gz v = FLOOKUP Gm v /\
      op_taint tnz (Var v) = op_taint tnm (Var v))` by
    (irule abi_child_suffix_operand_counted_ptr >>
     simp[] >> qexistsl_tac [`head`, `ip`, `child_len`, `off`] >> simp[]) >>
  `mload cursor sz = n2w (k+n) /\
   (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnz.t_mem)` by
    (irule abi_child_suffix_cursor_clean >> simp[] >>
     qexistsl_tac [`b+h`, `sm`, `tnm`] >> simp[]) >>
  qexistsl_tac [`Gz`, `tnz`, `sz`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gm`, `sm`, `tnm`] >> simp[]) >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> gvs[]
  >>~- ([`mem_agree_outside _ _ _`],
    qspecl_then [`sm`, `b+h`, `n2w k`] mp_tac mstore_memory_frame >>
     qspecl_then [`mstore (b+h) (n2w k) sm`, `cursor`, `n2w (k+n)`]
       mp_tac mstore_memory_frame >>
     gvs[mem_agree_outside_def] >> rpt strip_tac >> simp[]) >>
  FAIL_TAC "remaining frames"
QED
