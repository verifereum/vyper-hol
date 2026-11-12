(* Successful unsigned bounds checking on one counted execution. *)
Theory bodyPtrSubscriptBoundsRun
Ancestors
  bodyPtrSubscriptReadOnly bodyPtrSubscriptNumeric bodyPtrSubscriptBounds
  emitHelperProps exprLoweringProps freshWrites fragExec fragGasPathPtr
  emitHelper compileEnv ptrDiscipline bodyPtrDefs venomState venomInst
  venomExecSemantics finite_map words loweringPosts

Theorem iszero_counted_read_only:
  emit_op ISZERO [arg] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\ op_prov G arg = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (bool_to_word (a = 0w)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >> irule numeric_counted_read_only >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gen_tac >> irule numeric_iszero_step >> simp[]
QED

Theorem binary_counted_read_only:
  (opc = SUB /\ f = word_sub \/ opc = MUL /\ f = word_mul \/
   opc = OR /\ f = word_or \/
   opc = LT /\ f = (\a b. bool_to_word (w2n a < w2n b))) /\
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `!dst. step_inst_base (mk_inst sa.cs_next_id opc [left;right] [dst]) s =
         OK (update_var dst (f a b) s)` by
    (gen_tac >> irule numeric_binary_step >> simp[]) >>
  irule numeric_counted_read_only >>
  `MEM opc [ISZERO; SUB; MUL; LT; OR]` by metis_tac[listTheory.MEM] >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem lt_iszero_counted_read_only:
  emit_op LT [idx;len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\ w2n a < w2n b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME 0w /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspecl_then [`LT`, `[idx;len]`, `sa`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`ISZERO`, `[Var lt]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all (binary_counted_read_only |>
    Q.INST [`opc` |-> `LT`, `f` |-> `(\a b. bool_to_word (w2n a < w2n b))`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[bool_to_word_def] >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand (Var lt) s1 = SOME 1w` by simp[eval_operand_def] >>
  drule_all iszero_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[bool_to_word_def] >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm p` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem or_iszero_assert_counted_read_only:
  emit_op OR [Lit 0w;arg] sa = (Var invalid,sm) /\
  emit_op ISZERO [Var invalid] sm = (Var valid,sn) /\
  emit_void ASSERT [Var valid] sn = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME 0w /\ op_taint tn arg = {} /\ op_prov G arg = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspecl_then [`OR`, `[Lit 0w;arg]`, `sa`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ISZERO`, `[Var invalid]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sn sb` by
    (qspecl_then [`ASSERT`, `[Var valid]`, `sn`] mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[ci_mono_def, cs_extends_trans, fn_has_code_split] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   op_prov G (Lit 0w) = NONE` by simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (binary_counted_read_only |>
    Q.INST [`opc` |-> `OR`, `f` |-> `word_or`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand (Var invalid) s1 = SOME 0w` by simp[eval_operand_def, WORD_OR_CLAUSES] >>
  drule_all iszero_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[bool_to_word_def] >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  `eval_operand (Var valid) s2 = SOME 1w` by simp[eval_operand_def] >>
  `1w <> (0w:bytes32)` by simp[] >> drule_all assert_counted_read_only >>
  disch_then (qspecl_then [`PG`, `G2`, `D`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`G3`, `tn3`, `s3`] strip_assume_tac) >>
  qexistsl_tac [`G3`, `tn3`, `s3`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
      qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm p /\ not_fresh_at sn p` by
        metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >> metis_tac[]
QED

Theorem unsigned_bounds_counted_read_only:
  emit_op LT [idx;len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var not_oob,sn) /\
  emit_op OR [Lit 0w;Var not_oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\ w2n a < w2n b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa sn /\ cs_extends sn sb` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all lt_iszero_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand (Var not_oob) s1 = SOME 0w` by simp[eval_operand_def] >>
  drule_all or_iszero_assert_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn p` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sn` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED
