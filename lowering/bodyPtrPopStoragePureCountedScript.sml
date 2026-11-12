Theory bodyPtrPopStoragePureCounted
Ancestors
  bodyPtrPopStoragePureOutcome exprSimPopNestedBase fragGasSeqPtr fragGasPathPtr
  exprLoweringProps venomInst venomState list rich_list fragExec
  compileEnv ptrDiscipline context words pred_set finite_map

Theorem pop_storage_direct_counted:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_seq_ptr D 0 ctx func PG G tn
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s Gf tnf /\
  run_inst_seq (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sa.cs_current_insts ++ code` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    (Cases_on `tr` >> simp[Abbr `code`, nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem pop_storage_positive_counted:
  compile_dynarray_pop hdr 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (q,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  (!x. hdr = Var x ==> not_fresh_at sa x) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ 0 < len /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?u Gf tnf xs.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK u) /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_current_bb = sb.cs_current_bb /\
    u = ((if tr then tstore slot (n2w (len-1)) s
         else sstore slot (n2w (len-1)) s) with vs_vars := u.vs_vars)
         with vs_inst_idx := LENGTH sb.cs_current_insts /\
    eval_operand q u = SOME (slot + n2w (1 + (len-1) * esz)) /\
    op_prov Gf q = NONE /\ op_taint tnf q = {} /\
    EVERY (\x. ~not_fresh_at sa x) xs /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x) /\ lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `(if tr then tload slot s else sload slot s) <> 0w` by
    (strip_tac >> gvs[]) >>
  drule_all pop_storage_emitted_transfer_nonempty >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule nested_pop_suffix_shape >> strip_tac >> gvs[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (gvs[EVERY_MEM] >> metis_tac[MEM]) >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (fs[emitted_insts_def, DROP_LENGTH_APPEND] >>
     drule_all pop_storage_direct_counted >> simp[]) >>
  qexistsl [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tnf`,
    `xs ++ [x0;x1;x2;x3;x4;x5;x6]`] >>
  suspend "fields"
QED

Resume pop_storage_positive_counted[fields]:
  simp[EVERY_APPEND, MEM_APPEND, eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  conj_tac
  >- (qpat_x_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      Cases_on `tr` >> fs[n2w_sub]) >>
  conj_tac
  >- (`1 <= w2n (if tr then tload slot s else sload slot s)` by decide_tac >>
      fs[n2w_sub, lookup_var_def] >>
      simp[n2w_sub, GSYM word_add_n2w, GSYM word_mul_n2w,
           AC WORD_ADD_ASSOC WORD_ADD_COMM, WORD_MULT_COMM]) >>
  rpt strip_tac >> gvs[lookup_var_def]
QED

Finalise pop_storage_positive_counted
