Theory bodyPtrPopLengthGuard
Ancestors
  bodyPtrAttributeAdd bodyPtrPopScalarTransfer typedCopyLoopHeaderPtr
  exprSendPtr exprSimPtrProps emitHelperProps emitHelper compileEnv fragExec
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  codegenRel contextCodegenRel finite_map pred_set words list fragGasPathPtr stmtFragPtr

(* The guard's unary operation drops provenance even for stale temporaries. *)
Theorem pop_iszero_check:
  eval_operand a s = SOME w /\ op_taint tn a = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [a] [out]) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ISZERO [a] [out]) s =
     OK (update_var out (bool_to_word (w = 0w)) s)` by
    (irule step_ISZERO >> simp[]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >> metis_tac[]
QED

Theorem pop_emit_iszero_path:
  emit_op ISZERO [a] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} ==>
  ?out. op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out (bool_to_word (w = 0w)) s) with
             vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!x. not_fresh_at sa x ==> x <> out)
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[] >>
  reverse conj_tac >- (gvs[not_fresh_at_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id ISZERO [a] [out]) s =
      OK (update_var out (bool_to_word (w = 0w)) s)` by
    (gen_tac >> irule step_ISZERO >> simp[]) >>
  `!out. ptr_inst_ok D 0 0 ctx fn G tn
      (mk_inst sa.cs_next_id ISZERO [a] [out]) s` by
    (gen_tac >> irule pop_iszero_check >> metis_tac[]) >>
  `ISZERO <> INVOKE /\ ISZERO <> GAS /\ ~is_terminator ISZERO` by
    simp[is_terminator_def] >>
  drule_all attribute_emit_op_path_ptr >>
  simp[typed_copy_loop_arith_ghost, update_var_def,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def]
QED

Theorem pop_emit_sub_path:
  emit_op SUB [a;b] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE ==>
  ?out. op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out (x-y) s) with
             vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!v. not_fresh_at sa v ==> v <> out)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[] >>
  reverse conj_tac >- (gvs[not_fresh_at_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id SUB [a;b] [out]) s =
      OK (update_var out (x-y) s) /\
    ptr_inst_ok D 0 0 ctx fn G tn
      (mk_inst sa.cs_next_id SUB [a;b] [out]) s` by
    (gen_tac >> irule pop_scalar_binary_step >> metis_tac[]) >>
  `!out. step_prov PG G (mk_inst sa.cs_next_id SUB [a;b] [out])
      (update_var out (x-y) s) = DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst sa.cs_next_id SUB [a;b] [out]) s
      (update_var out (x-y) s) tn = tn with t_var := tn.t_var |+ (out,{})` by
    (gen_tac >> irule pop_scalar_binary_ghost >> simp[]) >>
  fs[FORALL_AND_THM] >>
  `SUB <> INVOKE /\ SUB <> GAS /\ ~is_terminator SUB` by
    simp[is_terminator_def] >>
  drule_all attribute_emit_op_path_ptr >>
  disch_then (qspec_then `PG` mp_tac) >> simp[]
QED

Theorem pop_emit_assert_instruction:
  emit_void ASSERT [a] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id ASSERT [a] [])
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem pop_emit_assert_ok_path:
  emit_void ASSERT [a] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ w <> 0w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all pop_emit_assert_instruction >> strip_tac >>
  irule assert_ok_path_ptr >> metis_tac[]
QED

Theorem pop_emit_assert_fail_path:
  emit_void ASSERT [a] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME 0w /\ op_taint tn a = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >> drule_all pop_emit_assert_instruction >> strip_tac >>
  irule assert_fail_path_ptr >> metis_tac[]
QED

Theorem pop_double_iszero_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand valid t = SOME (bool_to_word (w <> 0w)) /\
    op_taint tn' valid = {} /\ op_prov G' valid = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  drule_all pop_emit_iszero_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qabbrev_tac `u = (update_var out (bool_to_word (w = 0w)) s) with
                    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (out,{})` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_bb = sb.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   LENGTH sc.cs_current_insts = SUC (LENGTH sb.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?out2. valid = Var out2 /\ out2 = STRING #"%" (toString sb.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G1 tn1 u 0
      (DRESTRICT G1 (COMPL {out2})) (tn1 with t_var := tn1.t_var |+ (out2,{}))
      (OK ((update_var out2 (bool_to_word (bool_to_word (w = 0w) = 0w)) u) with
        vs_inst_idx := SUC u.vs_inst_idx)) /\
    (!v. not_fresh_at sb v ==> v <> out2)` by
    (irule pop_emit_iszero_path >>
     simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`nz`, `sc`] >>
     simp[Abbr `tn1`, update_var_def, eval_operand_def,
          lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac
    [`(update_var out2 (bool_to_word (bool_to_word (w = 0w) = 0w)) u) with
        vs_inst_idx := SUC u.vs_inst_idx`,
     `DRESTRICT G1 (COMPL {out2})`, `tn1 with t_var := tn1.t_var |+ (out2,{})`] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[Abbr `u`, Abbr `G1`, Abbr `tn1`, update_var_def, eval_operand_def,
       lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, bool_to_word_def] >>
  rpt strip_tac >>
  `v <> out /\ v <> out2` by
    (metis_tac[not_fresh_at_mono]) >> gvs[]
QED

Theorem pop_nonempty_guard_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ w <> 0w ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_double_iszero_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sd.cs_current_bb = sc.cs_current_bb /\
   LENGTH sd.cs_current_insts = SUC (LENGTH sc.cs_current_insts)` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn'
     (OK (t with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule pop_emit_assert_ok_path >> simp[] >>
     qexistsl_tac [`valid`, `sc`, `sd`, `1w`] >> simp[bool_to_word_def]) >>
  qexistsl_tac [`t with vs_inst_idx := SUC t.vs_inst_idx`, `G'`, `tn'`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Theorem pop_empty_guard_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME 0w /\ op_taint tn a = {} ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >> drule_all pop_double_iszero_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn'
    (Abort Revert_abort (revert_state (set_returndata [] t)))` by
    (irule pop_emit_assert_fail_path >> simp[] >>
     qexistsl_tac [`valid`, `sc`, `sd`] >> simp[bool_to_word_def]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem pop_length_guard_code:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [a; Lit 1w] sd = (new_len,se) /\ fn_has_code sa se fn ==>
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\
  sa.cs_next_var <= sd.cs_next_var
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\
   cs_extends sc sd /\ cs_extends sd se /\
   sa.cs_next_var <= sd.cs_next_var` by
    (gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, cs_extends_def] >> simp[]) >>
  `cs_extends sb se /\ cs_extends sc se` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem pop_length_guard_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [a; Lit 1w] sd = (new_len,se) /\ fn_has_code sa se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ op_prov G a = NONE /\
  (!v. a = Var v ==> not_fresh_at sa v) /\ w <> 0w ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand new_len t = SOME (w-1w) /\
    op_taint tn' new_len = {} /\ op_prov G' new_len = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_length_guard_code >> strip_tac >>
  drule_all pop_nonempty_guard_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand a t = SOME w /\ op_taint tn' a = {} /\ op_prov G' a = NONE` by
    (Cases_on `a` >> gvs[eval_operand_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  `?out. new_len = Var out /\ out = STRING #"%" (toString sd.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G' tn' t 0
      (DRESTRICT G' (COMPL {out})) (tn' with t_var := tn'.t_var |+ (out,{}))
      (OK ((update_var out (w-1w) t) with vs_inst_idx := SUC t.vs_inst_idx)) /\
    (!v. not_fresh_at sd v ==> v <> out)` by
    (irule pop_emit_sub_path >> simp[] >>
     qexistsl_tac [`a`, `Lit 1w`, `se`] >> simp[eval_operand_def, op_taint_def, op_prov_def]) >>
  `se.cs_current_bb = sd.cs_current_bb /\
   LENGTH se.cs_current_insts = SUC (LENGTH sd.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qexistsl_tac [`(update_var out (w-1w) t) with vs_inst_idx := SUC t.vs_inst_idx`,
    `DRESTRICT G' (COMPL {out})`, `tn' with t_var := tn'.t_var |+ (out,{})`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `v <> out` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!v. not_fresh_at sa v ==> _ /\ _ /\ _`
    (qspec_then `v` mp_tac) >>
  gvs[lookup_var_def, op_taint_def]
QED

Theorem pop_length_guard_empty_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [a; Lit 1w] sd = (new_len,se) /\ fn_has_code sa se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME 0w /\ op_taint tn a = {} ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >> drule_all pop_length_guard_code >> strip_tac >>
  irule pop_empty_guard_path >> metis_tac[]
QED

Theorem pop_length_guard_ghost:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [a; Lit 1w] sd = (new_len,se) /\ fn_has_code sa se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ op_prov G a = NONE /\
  (!v. a = Var v ==> not_fresh_at sa v) /\ w <> 0w /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand new_len t = SOME (w-1w) /\
    op_taint tn' new_len = {} /\ op_prov G' new_len = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_all pop_length_guard_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >> conj_tac
  >- (irule ghost_inv_fresh_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[]) >>
  irule attribute_ghost_kept_frame >> metis_tac[]
QED
