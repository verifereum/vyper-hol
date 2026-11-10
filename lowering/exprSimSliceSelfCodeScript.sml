(*
 * Expression simulation: slice(self.code, start, length).
 *
 * Source evaluation reads cx.txn.code (via evaluate_code_source on
 * self.code after evaluating start, length, and self), while the lowering
 * allocates the output buffer with compile_slice_out_buf and copies from
 * vs_code with CODESIZE and CODECOPY (compile_slice_code).  accounts_rel
 * ties vs_code to cx.txn.code across runtime and deployment execution.
 *)

Theory exprSimSliceSelfCode
Ancestors
  exprSimHypsDefs exprLowering vyperAST
  exprSimSliceExtcodeTyped exprSimSliceExtcodeContinue exprSimSliceExtcodeEntry
  exprSimSliceExtcodeContext exprSimSliceExtcode
  exprSimSliceOrdinaryContinue exprSimSliceOrdinaryContext
  exprSimSliceCapacityRead exprSimSliceOrdinaryFrame
  exprSimSliceBounds exprSimSliceData exprSimSliceSource exprSimSliceCompose
  exprSimCalldataSlice exprSimSource exprSimHyps exprSimProps exprSimWordArgs
  exprSimDefs loweringPosts gasOutcome gasSummary gasSummaryCompose
  fragGasSeq fragGasSeqAbort fragGasMode fragExec
  builtinBytes emitHelper emitHelperProps freshWrites allocLimits
  valueTypingMemoryProps compileEnv context exprLoweringProps exprBopLowering
  venomExecSemantics venomInst venomState vyperTypeInvariants vyperTypeSystem
  vyperTypeCallGraph vyperContext vyperInterpreter vyperState vyperValue
  valueEncoding words arithmetic list rich_list pair finite_map

(* The operand judgments of slice(x.code, start, length), in its evaluation
   order: start and length first, then, when they evaluate, x. *)
Definition slice_extcode_case_def:
  slice_extcode_case nocalls ctx func cenv cx args <=>
    !ct a start len.
      args = [Builtin ct (Acc Code) [a]; start; len] ==>
      exprs_case nocalls ctx func cenv cx [start; len] /\
      ((?s vs t. eval_exprs cx [start; len] s = (INL vs, t)) ==>
       expr_sim_case nocalls ctx func cenv cx a /\
       expr_vv_case nocalls ctx func cenv cx a)
End

Theorem is_self_code_thm[local]:
  is_self_code src <=>
  ?ct st. src = Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]
Proof
  EQ_TAC
  >- (qid_spec_tac `src` >> recInduct is_self_code_ind >>
      simp[is_self_code_def]) >>
  strip_tac >> gvs[is_self_code_def]
QED

Theorem eval_self_addr_exprs[local]:
  eval_exprs cx [Builtin st (Env SelfAddr) []] =
    return [AddressV cx.txn.target]
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[FUN_EQ_THM, eval_exprs_cons_action, Once evaluate_def,
       builtin_args_length_ok_def, code_slice_source_def,
       precompile_call_success_def, precompile_builtin_def,
       vyperContextTheory.evaluate_builtin_def,
       type_check_def, assert_def, get_accounts_def,
       lift_sum_def, read_result_def, bind_def, ignore_bind_def, return_def]
QED

Theorem slice_self_code_actions[local]:
  eval_expr cx
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) =
  do sv <- bind (eval_expr cx start) (read_result cx);
     lv <- bind (eval_expr cx len) (read_result cx);
     acc <- get_accounts;
     v <- lift_sum (evaluate_slice (BytesV cx.txn.code) sv lv n);
     return (Value v)
  od
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  rewrite_tac[slice_eval_extcode] >>
  simp[eval_self_addr_exprs, eval_exprs_cons_action,
       vyperContextTheory.is_self_addr_def,
       vyperContextTheory.evaluate_code_source_def,
       bind_return, bind_assoc] >>
  simp[FUN_EQ_THM, get_accounts_def, lift_sum_def, bind_def, return_def,
       vyperContextTheory.evaluate_builtin_def]
QED

Theorem slice_code_decompose[local]:
  compile_slice_code start len sz st2 = (r, sb) ==>
  ?out dst s3 sc sd se src_len.
    r = out /\
    compile_slice_out_buf sz st2 = ((out, dst), s3) /\
    emit_op CODESIZE [] s3 = (src_len, sc) /\
    compile_assert_slice_bounds start len src_len sc = ((), sd) /\
    emit_void CODECOPY [dst; start; len] sd = ((), se) /\
    emit_void MSTORE [out; len] se = ((), sb)
Proof
  simp[compile_slice_code_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_code_tail_control[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) ==>
  ci_mono sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_assert_slice_bounds_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[ci_mono_def, cs_extends_def, same_blocks_def,
       emitted_insts_def, DROP_APPEND1, IS_PREFIX_APPEND]
QED

Theorem slice_code_tail_shape[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) ==>
  emitted_insts sa sb =
    emitted_insts sa sc ++ emitted_insts sc sd ++ emitted_insts sd sb
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule slice_bounds_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_void >>
  `sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by simp[] >>
  `se.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd se` by simp[] >>
  `sb.cs_current_insts = se.cs_current_insts ++ emitted_insts se sb` by simp[] >>
  `emitted_insts sd sb = emitted_insts sd se ++ emitted_insts se sb` by
    (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb` by
    (qpat_x_assum `sb.cs_current_insts = se.cs_current_insts ++ emitted_insts se sb`
      (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `se.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd se`
      (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `emitted_insts sd sb = _` (fn th => pure_rewrite_tac[th]) >>
     simp[APPEND_ASSOC]) >>
  `emitted_insts sc sb = emitted_insts sc sd ++ emitted_insts sd sb` by
    (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` by
    (qpat_x_assum `sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb`
      (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `sd.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sd`
      (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `emitted_insts sc sb = _` (fn th => pure_rewrite_tac[th]) >>
     simp[APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  simp[APPEND_ASSOC]
QED

Theorem slice_code_zero_code[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> drule_all slice_code_tail_shape >>
  disch_then (fn th => rewrite_tac[th]) >>
  drule (cj 5 slice_bounds_shape) >> strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
  simp[emitted_insts_def, DROP_APPEND1, DROP_APPEND2,
       mk_inst_def, is_terminator_def]
QED

Theorem slice_code_copy_store_run[local]:
  emit_void CODECOPY [dst; start; len] sa = ((), sm) /\
  emit_void MSTORE [out; len] sm = ((), sb) /\
  eval_operand dst s = SOME d /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  w2n b + w2n n <= LENGTH s.vs_code ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n p) n
      (write_memory_with_expansion (w2n d)
        (TAKE (w2n n) (DROP (w2n b) s.vs_code)) s))
Proof
  strip_tac >>
  `TAKE (w2n n) (DROP (w2n b) s.vs_code ++ REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n b) s.vs_code)` by
    (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
  qpat_x_assum `emit_void CODECOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       write_memory_with_expansion_def] >>
  Cases_on `out` >> Cases_on `len` >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem slice_codesize_run[local]:
  emit_op CODESIZE [] sa = (sz, sb) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand sz t = SOME (n2w (LENGTH s.vs_code)) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def,
       eval_operand_def, lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
                       not_fresh_at_def]
QED

Theorem slice_codesize_fresh[local]:
  emit_op CODESIZE [] sa = (sz, sc) ==>
  (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
  (!x. sz = Var x ==> not_fresh_at sc x)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  fs[not_fresh_at_def] >> metis_tac[DECIDE ``a < b ==> a < b + 1``]
QED

Theorem slice_code_prefix_run[local]:
  emit_op CODESIZE [] sa = (sz, sc) /\
  compile_assert_slice_bounds start len sz sc = ((), sd) /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  (!x. MEM (Var x) [start; len] ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) ==>
  if LENGTH s.vs_code < w2n b + w2n n then
    ?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sd) s = Abort Revert_abort u
  else ?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sd) s = OK u /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
          eval_operand op u = eval_operand op s)
Proof
  strip_tac >>
  drule slice_codesize_run >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  drule slice_codesize_fresh >> strip_tac >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
        eval_operand op t = eval_operand op s` by
    (Cases >> simp[eval_operand_def] >>
     qpat_x_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand start t = SOME b /\ eval_operand len t = SOME n` by
    metis_tac[MEM] >>
  `!x. start = Var x ==> not_fresh_at sc x` by metis_tac[MEM] >>
  `!x. len = Var x ==> not_fresh_at sc x` by metis_tac[MEM] >>
  `(((b:bytes32) + (n:bytes32) <+ b \/
     n2w (LENGTH s.vs_code) <+ b + n) <=>
    LENGTH s.vs_code < w2n b + w2n n)` by
    (mp_tac (Q.SPECL [`dimword (:256)`, `w2n (b:bytes32)`, `w2n (n:bytes32)`,
       `LENGTH s.vs_code`] slice_bounds_mod) >>
     simp[WORD_LO, word_add_def, w2n_n2w, w2n_lt] >> decide_tac) >>
  drule_all slice_bounds_run_frame >>
  qpat_x_assum `(_ \/ _) <=> _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `LENGTH s.vs_code < w2n b + w2n n` >>
  simp[] >> strip_tac >>
  qpat_assum `run_inst_seq (emitted_insts sa sc) s = OK t`
    (mp_then Any (fn th => once_rewrite_tac[th]) run_inst_seq_append)
  >- metis_tac[] >>
  qexists_tac `t'` >> simp[] >>
  `t' = s with vs_vars := t'.vs_vars` by
    (qpat_x_assum `t' = t with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t' = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sc x` by metis_tac[] >>
     fs[lookup_var_def]) >>
  simp[] >> Cases >> simp[eval_operand_def] >>
  qpat_x_assum `t' = s with vs_vars := _`
    (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem slice_code_tail_run[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. MEM (Var x) [start; len; out; dst] ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) ==>
  if LENGTH s.vs_code < w2n b + w2n n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory =
        (mstore (w2n p) n
          (write_memory_with_expansion (w2n d)
            (TAKE (w2n n) (DROP (w2n b) s.vs_code)) s)).vs_memory /\
      (t with <| vs_memory := s.vs_memory; vs_vars := s.vs_vars |>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      eval_operand out t = SOME p
Proof
  strip_tac >> drule_all slice_code_tail_shape >> strip_tac >>
  `!x. MEM (Var x) [start; len] ==> not_fresh_at sa x` by
    (fs[MEM] >> metis_tac[]) >>
  drule_all slice_code_prefix_run >>
  qpat_x_assum `emitted_insts sa sb = _`
    (fn th => pure_rewrite_tac[th, APPEND_ASSOC]) >>
  Cases_on `LENGTH s.vs_code < w2n b + w2n n`
  >- (simp[] >> strip_tac >>
      qspecl_then [`emitted_insts sa sc ++ emitted_insts sc sd`,
        `emitted_insts sd sb`, `s`] mp_tac run_inst_seq_append_err >>
      simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  `!op. MEM op [start; len; out; dst] ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[MEM]) >>
  `u.vs_code = s.vs_code` by
    (qpat_x_assum `u = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand start u = SOME b /\ eval_operand len u = SOME n /\
   eval_operand out u = SOME p /\ eval_operand dst u = SOME d` by
    metis_tac[MEM] >>
  `w2n b + w2n n <= LENGTH u.vs_code` by simp[] >>
  drule_all slice_code_copy_store_run >> strip_tac >>
  qpat_assum `run_inst_seq (_ ++ _) s = OK u`
    (mp_then Any (fn th => once_rewrite_tac[th]) run_inst_seq_append) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sd sb) u = OK v` >>
  qexists_tac `v` >> simp[] >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `u = s with vs_vars := _` kall_tac >>
      ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
        [Abbr `v`, mstore_def, write_memory_with_expansion_def]) >>
  conj_tac
  >- (ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
        [Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
      qpat_x_assum `u = s with vs_vars := _`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- simp[Abbr `v`, mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  qpat_x_assum `eval_operand out u = SOME p` mp_tac >>
  qpat_x_assum `u = s with vs_vars := _` kall_tac >>
  Cases_on `out` >>
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
    [Abbr `v`, mstore_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

Theorem slice_code_tail_frame[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p + 32w) /\
  (!x. MEM (Var x) [start; len; out; dst] ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) /\
  w2n b + w2n n <= LENGTH s.vs_code /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p, cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off, sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sbase s t /\
    eval_operand out t = SOME p /\
    FLOOKUP t.vs_allocas aid = SOME (w2n p, cap) /\
    t.vs_memory = (mstore (w2n p) n (write_memory_with_expansion (w2n p + 32)
      (TAKE (w2n n) (DROP (w2n b) s.vs_code)) s)).vs_memory /\
    (!nm off sz. local_region cenv es.scopes t nm off sz ==>
      regions_disjoint (w2n p) cap off sz)
Proof
  strip_tac >> drule_all slice_code_tail_run >> simp[] >> strip_tac >>
  `w2n (p + 32w) = w2n p + 32` by
    (simp[word_add_def, w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `t.vs_memory = w.vs_memory` >>
  `LENGTH (TAKE (w2n n) (DROP (w2n b) s.vs_code)) = w2n n` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es w /\ wb_frame cenv es es sbase s w` by
    (simp[Abbr `w`] >>
     qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ bytes s` >>
     `n = n2w (LENGTH bytes)` by simp[Abbr `bytes`] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule (SIMP_RULE std_ss [LET_THM] slice_allocated_bytes_write_frame) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`inst`, `cap`] >> simp[] >> metis_tac[]) >>
  `w.vs_vars = s.vs_vars /\ w.vs_allocas = s.vs_allocas` by
    ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
      [Abbr `w`, mstore_def, write_memory_with_expansion_def] >>
  `t = w with vs_vars := t.vs_vars` by
    (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     ASM_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
       [Abbr `w`, mstore_def, write_memory_with_expansion_def,
        venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = w with vs_vars := _` SUBST1_TAC >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >> fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `wb_frame cenv es es sbase s t` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> qexists_tac `sa` >> simp[] >>
     conj_tac >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
     qpat_assum `t = w with vs_vars := _` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (w2n p, cap)` by
    (qpat_assum `t = w with vs_vars := _` SUBST1_TAC >> simp[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (qpat_x_assum `t.vs_memory = w.vs_memory` (fn th => pure_rewrite_tac[th]) >>
      simp[Abbr `w`]) >>
  rpt strip_tac >>
  `local_region cenv es.scopes s nm off sz` by
    (irule exprSimPropsTheory.local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `es.scopes`, `t`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem slice_code_tail_vv_post[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds start len src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start; len] sd = ((), se) /\
  emit_void MSTORE [out; len] se = ((), sb) /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p + 32w) /\
  (!x. MEM (Var x) [start; len; out; dst] ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) /\
  w2n b + w2n n <= LENGTH s.vs_code /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p, cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off, sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic max_len)) /\ w2n n <= max_len /\
  aid < sb.cs_next_id ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    !k. vv_post ctx func cenv cx e es sbase sb s es
      (Value (BytesV (TAKE (w2n n) (DROP (w2n b) s.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr out LocMemory)) (t with vs_inst_idx := k)
Proof
  strip_tac >> drule_all slice_code_tail_frame >> strip_tac >>
  `LENGTH (TAKE (w2n n) (DROP (w2n b) s.vs_code)) = w2n n` by
    (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `val_in_memory (BaseTV (BytesT (Dynamic max_len)))
      (BytesV (TAKE (w2n n) (DROP (w2n b) s.vs_code))) (w2n p) t.vs_memory` by
    (qpat_x_assum `t.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     metis_tac[exprSimCalldataSliceTheory.bytes_buffer_write_encoding, n2w_w2n]) >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >> gen_tac >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.vv_at_def, mk_ptr_def,
       stmt_state_rel_inst_idx,
       evaluate_type_def, is_word_type_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      qspec_then `max_len` mp_tac exprSimPropsTheory.le_word_size_mul >> decide_tac) >>
  disj1_tac >> qexistsl_tac [`aid`, `w2n p`, `cap`] >>
  simp[loweringPostsTheory.val_footprint_def] >>
  fs[regions_disjoint_def]
QED

Theorem slice_code_tail_outcome[local]:
  emit_op CODESIZE [] sa = (src_len, sc) /\
  compile_assert_slice_bounds sop lop src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; sop; lop] sd = ((), se) /\
  emit_void MSTORE [out; lop] se = ((), sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p + 32w) /\
  (!x. MEM (Var x) [sop; lop; out; dst] ==> not_fresh_at sa x) /\
  LENGTH cx.txn.code < dimword (:256) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\
  aid < sa.cs_next_id /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p, cap) /\
  w2n p + cap < dimword (:256) /\ 32 + n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off, sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] ==>
  gas_outcome F tops (ctx, func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice (BytesV cx.txn.code) (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es, s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sbase sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `s.vs_code = cx.txn.code` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `LENGTH s.vs_code < dimword (:256)` by simp[] >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
      (emitted_insts sa sb)` by
    (drule_all slice_code_zero_code >> simp[]) >>
  Cases_on `i + k <= LENGTH cx.txn.code`
  >- (`w2n (n2w i : bytes32) + w2n (n2w k : bytes32) <= LENGTH s.vs_code` by simp[] >>
      `32 + w2n (n2w k : bytes32) <= cap /\ w2n (n2w k : bytes32) <= n` by simp[] >>
      drule_all slice_code_tail_vv_post >> strip_tac >>
      `EVERY (\inst. inst.inst_opcode <> INVOKE /\
          ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
      `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
        (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
      `ci_mono sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
       sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
        (drule_all slice_code_tail_control >> simp[]) >>
      `t.vs_current_bb = sb.cs_current_bb /\
       LENGTH (emitted_insts sa sb) + s.vs_inst_idx = LENGTH sb.cs_current_insts` by
        (drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
      drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >> strip_tac >>
      qpat_x_assum `!ctx'. gas_path _ _ _ _ _` (qspec_then `ctx` assume_tac) >>
      `es with gas_obs := [] = es` by
        (qpat_x_assum `es.gas_obs = []` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
      rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `[]` >> disj1_tac >>
      rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
      qexistsl_tac [`INL (Value (BytesV (TAKE k (DROP i cx.txn.code))))`, `es`,
        `OK (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)`] >>
      simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
           vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
           exprSimSliceSourceTheory.slice_bytes_nat] >>
      conj_tac
      >- (qpat_x_assum `gas_path _ _ _ _ _` mp_tac >> simp[]) >>
      qpat_x_assum `!idx. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH s.vs_code < w2n (n2w i : bytes32) + w2n (n2w k : bytes32)` by simp[] >>
  drule_all slice_code_tail_run >> simp[] >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all fragGasSeqAbortTheory.run_inst_seq_abort_zero_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "evaluate_slice range"))`,
                `es`, `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[gasSummaryTheory.gas_marked_exec_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.bind_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
       exprSimSliceSourceTheory.slice_bytes_nat,
       vyperStateTheory.raise_def, exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Theorem slice_code_continue_entry_seq[local]:
  compile_slice_out_buf sz sa = ((out, dst), sb) /\
  emit_op CODESIZE [] sb = (src_len, sc) /\
  compile_assert_slice_bounds sop lop src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; sop; lop] sd = ((), se) /\
  emit_void MSTORE [out; lop] se = ((), sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op. MEM op [sop; lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  LENGTH cx.txn.code < dimword (:256) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32 + n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] ==>
  gas_outcome F (cx_tops cx) (ctx, func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice (BytesV cx.txn.code) (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es, s)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result es sa sf s ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_slice_out_buf, SND] >>
  `ci_mono sb sf /\ sb.cs_current_bb = sf.cs_current_bb /\
   sf.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sf` by
    (drule_all slice_code_tail_control >> simp[]) >>
  `fn_has_code sa sb func /\ fn_has_code sb sf func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `local_ptrs_reserved cenv sb` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  drule_all slice_extcode_output_entry >> strip_tac >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  drule slice_extcode_out_control >> strip_tac >>
  `u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted` by
    (drule_all slice_extcode_out_run_control >> simp[]) >>
  irule slice_extcode_output_outcome_prefix >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`dst`, `out`, `sz`] >> simp[] >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  simp[] >>
  qabbrev_tac `u1 = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `stmt_state_rel ctx func cenv cx es u1` by simp[Abbr `u1`, stmt_state_rel_inst_idx] >>
  `wb_frame cenv es es sa s u1` by
    fs[Abbr `u1`, loweringPostsTheory.wb_frame_def,
       loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def,
       venomStateTheory.lookup_var_def] >>
  `!op. MEM op [sop; lop] ==> eval_operand op u1 = eval_operand op s` by
    (rpt strip_tac >>
     `(?w. op = Lit w) \/ (?z. op = Var z /\ not_fresh_at sa z)` by metis_tac[] >>
     gvs[Abbr `u1`, venomStateTheory.eval_operand_def,
         venomStateTheory.lookup_var_def] >>
     `lookup_var z u = lookup_var z s` by metis_tac[] >>
     fs[venomStateTheory.lookup_var_def]) >>
  `eval_operand out u1 = SOME p /\ eval_operand dst u1 = SOME (p + 32w)` by
    (Cases_on `out` >> Cases_on `dst` >>
     gvs[Abbr `u1`, venomStateTheory.eval_operand_def,
         venomStateTheory.lookup_var_def]) >>
  `!nm off len. local_region cenv es.scopes u1 nm off len ==>
     regions_disjoint (w2n p) sz off len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes u nm off len` by
       fs[Abbr `u1`, local_region_def, venomStateTheory.lookup_var_def] >>
     metis_tac[]) >>
  `?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sb sf) (DROP (LENGTH sb.cs_current_insts) bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sb sf func` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> gvs[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ef z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result es sa sf u1 ef tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts)` >>
  qexists_tac `(\res ef r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac
  >- (BETA_TAC >> rpt strip_tac >> gvs[] >>
      irule exprSimCalldataSliceTheory.vv_post_prefix_frame >> simp[] >>
      qexistsl_tac [`es`, `sa`, `u1`] >> simp[]) >>
  irule slice_code_tail_outcome >>
  qpat_assum `emit_op CODESIZE _ _ = _` (irule_at Any) >>
  qpat_assum `compile_assert_slice_bounds _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void CODECOPY _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  `FLOOKUP u1.vs_allocas sa.cs_next_id = SOME (w2n p, sz)` by simp[Abbr `u1`] >>
  qpat_assum `FLOOKUP u1.vs_allocas _ = _` (irule_at Any) >>
  qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[mk_inst_def] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_id <= sf.cs_next_id` by
    fs[ci_mono_def] >>
  `~u1.vs_halted /\ u1.vs_current_bb = sb.cs_current_bb /\
   u1.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[Abbr `u1`] >>
  simp[] >> qexists_tac `bb` >> simp[] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!nm off len. local_region _ _ u1 _ _ _ ==> _` irule >>
      qexists_tac `nm` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> fs[Abbr `u1`] >>
      qpat_x_assum `!j b len. j < _ /\ _ ==> _` irule >>
      qexists_tac `j` >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  rename1 `not_fresh_at sb v` >>
  qpat_x_assum `!op. _ ==> (?w. op = Lit w) \/ _`
    (qspec_then `Var v` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]
QED

Theorem slice_self_code_pipeline_context[local]:
  lower_value compile_expr cenv ty start sa = (start_op, s1) /\
  lower_value compile_expr cenv ty len s1 = (len_op, s2) /\
  compile_slice_out_buf out_size s2 = ((out, dst), s3) /\
  emit_op CODESIZE [] s3 = (src_len, sc) /\
  compile_assert_slice_bounds start_op len_op src_len sc = ((), sd) /\
  emit_void CODECOPY [dst; start_op; len_op] sd = ((), se) /\
  emit_void MSTORE [out; len_op] se = ((), sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by metis_tac[compile_expr_grows, ci_mono_def] >>
  `ci_mono s2 s3` by metis_tac[ci_mono_compile_slice_out_buf, SND] >>
  `ci_mono s3 sb` by (drule_all slice_code_tail_control >> simp[]) >>
  `ci_mono s3 s3` by simp[ci_mono_def, cs_extends_refl] >>
  simp[] >>
  mp_tac (Q.INST [`s4` |-> `s3`] (SPEC_ALL slice_pipeline_code_context)) >>
  simp[]
QED

Theorem slice_self_code_typed_entry[local]:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es /\
  expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  slice_operands_ok (Slice n)
    [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len] /\
  exprs_case nocalls ctx func cenv cx [start; len] /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) ==>
  expr_vv_sim ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call, is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2` >>
  gvs[as_ptr_val_def] >>
  drule slice_code_decompose >> strip_tac >> gvs[] >>
  drule_all slice_self_code_pipeline_context >> strip_tac >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32 + n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ _` kall_tac >>
  qpat_x_assum `!xs. ~names_builtin _ xs` kall_tac >>
  `expr_sim ctx func cenv cx ty start es` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> fs[exprs_case_def]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[slice_self_code_actions] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `start_op`, `sa`, `st1`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?gs. bind (eval_expr cx start) (read_result cx) (es with gas_obs := gs) =
    (INL v, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_case nocalls ctx func cenv cx len` by
    (fs[exprs_case_def] >>
     qpat_x_assum `(_ ==> expr_sim_case _ _ _ _ _ len /\ _)` mp_tac >>
     impl_tac >- (qpat_x_assum `bind _ _ _ = (INL _, _)` mp_tac >>
                  simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     simp[]) >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env len (mid with gas_obs := [])` by
    gvs[expr_body_pre_def] >>
  `expr_sim ctx func cenv cx ty len (mid with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `len_op`, `st1`, `st2`, `ty`] >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `exprs_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ len _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ es` kall_tac >>
  qpat_x_assum `gas_admissible _ _ mid` kall_tac >>
  `?gs2. bind (eval_expr cx len) (read_result cx)
     ((mid with gas_obs := []) with gas_obs := gs2) =
     (INL v, mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := []) /\
   MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM (mid' with gas_obs := []).scopes /\
   ?k. v = IntV (&k) /\ k < dimword (:256) /\ eval_operand len_op t' = SOME (n2w k)` by
    (irule slice_uint_read_post >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `~t'.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` kall_tac >>
  gvs[] >>
  `k <= n` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >> drule slice_literal_read_length >> intLib.ARITH_TAC) >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    metis_tac[expr_post_state] >>
  `LENGTH cx.txn.code < dimword (:256)` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.context_well_typed_def,
       wordsTheory.dimword_def] >>
  `(!z. start_op = Var z ==> not_fresh_at st1 z) /\ (!l. start_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ start _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `(!z. len_op = Var z ==> not_fresh_at st2 z) /\ (!l. len_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ len _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `eval_operand start_op t' = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` kall_tac >>
  qpat_x_assum `bind _ _ (mid with gas_obs := gs2) = _` kall_tac >>
  qpat_x_assum `slice_operands_ok _ _` kall_tac >>
  `!op. MEM op [start_op; len_op] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at st2 x)` by
    (Cases_on `start_op` >> Cases_on `len_op` >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def]) >>
  `fn_has_code st2 r func` by
    (irule fragExecTheory.fn_has_code_mid >>
     fs[ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, compileEnvTheory.cs_extends_refl]) >>
  irule slice_gas_outcome_conseq >>
  qexistsl_tac [
    `\res ee z. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
          [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len])
        (mid' with gas_obs := []) st2 r t' ee tv
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) z /\
      z.vs_current_bb = r.cs_current_bb /\ z.vs_inst_idx = LENGTH r.cs_current_insts`,
    `\res ee rr. expr_exit res rr`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule (slice_two_operand_post_rebase |> SPEC_ALL |> Q.INST
        [`sd` |-> `st1`, `se` |-> `st2`,
         `e1` |-> `mid with gas_obs := []`, `e2` |-> `mid' with gas_obs := []`]) >>
      qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
      fs[ci_mono_def] >> metis_tac[]) >>
  irule (slice_code_continue_entry_seq |> SPEC_ALL |> Q.INST
    [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
       [Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]; start; len]`]
    |> SRULE [expr_type_def]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qpat_assum `compile_slice_out_buf _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op CODESIZE _ _ = _` (irule_at Any) >>
  qpat_assum `compile_assert_slice_bounds _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void CODECOPY _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Theorem compile_slice_self_code_case:
  !nocalls ctx func cenv cx ann n args.
    is_self_code (HD args) /\ slice_extcode_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ann (Slice n) args)` by
    fs[expr_body_pre_def] >>
  drule slice_typed_args >>
  disch_then (qx_choose_then `src` (qx_choose_then `start` (qx_choose_then `len`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  gvs[] >>
  `?ct st. src = Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]` by
    gvs[is_self_code_thm] >>
  gvs[] >>
  `well_typed_expr env (Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `!e. MEM e [start; len] ==> ~is_extcode e` by
    (gvs[vyperTypeSystemTheory.well_typed_expr_def] >> rpt strip_tac >>
     imp_res_tac exprSimSourceTheory.well_typed_extcode_type >> gvs[]) >>
  fs[Once vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeSystemTheory.well_typed_builtin_app_def,
     vyperTypeSystemTheory.account_item_type_def, vyperASTTheory.expr_type_def] >>
  `exprs_case nocalls ctx func cenv cx [start; len]` by
    fs[slice_extcode_case_def] >>
  `expr_body_pre cenv cx env start es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac
     >- fs[expr_body_pre_def] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env len es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac
     >- fs[expr_body_pre_def] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >> simp[]) >>
  irule slice_self_code_typed_entry >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `nocalls` >>
  fs[vyperTypeCallGraphTheory.int_calls_expr_def]
QED
