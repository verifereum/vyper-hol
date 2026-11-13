(* The external-call return-size guard and cap execute on the counted path. *)
Theory extcallReturnGuardMemory
Ancestors
  exprSimRawCallCalldata builtinProps builtinSimple emitHelperProps exprLoweringProps
  exprLowering compileEnv emitHelper loweringStateRelDefs venomExecSemantics venomState venomInst
  finite_map
  rawCallCountedRun varsExt exprSimProps exprSimConcatPath
  bodyUnopFragMemory fragExecMem fragGasPathMem fragGasMode fragGasPathFrameMem
  instMemFrontier memSafeRun
  words list rich_list arithmetic

Theorem extcall_return_decode_code[local]:
  compile_return_value_decode mn mx sa = (hi,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; ISZERO; ASSERT; XOR; MUL] /\
    (i.inst_opcode = RETURNDATASIZE ==> ?out. i.inst_outputs = [out]) /\
    EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[compile_return_value_decode_def, compile_select_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, not_fresh_at_def]
QED

Theorem extcall_return_decode_frame[local]:
  compile_return_value_decode mn mx sa = (hi,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule extcall_return_decode_code >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `not_fresh_at sa`, `s`, `t`]
    mp_tac run_inst_seq_protected_frame >>
  simp[lookup_var_def] >> disch_then irule >>
  map_every qx_gen_tac [`i`,`u`,`v`] >> strip_tac >>
  `MEM i.inst_opcode [RETURNDATASIZE; LT; ISZERO; ASSERT; XOR; MUL] /\
   (i.inst_opcode = RETURNDATASIZE ==> ?out. i.inst_outputs = [out]) /\
   EVERY (\x. ~not_fresh_at sa x) i.inst_outputs` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = RETURNDATASIZE`
  >- (fs[] >>
      `MEM i.inst_opcode [RETURNDATASIZE;LT;XOR;MUL]` by simp[] >>
      drule_all raw_call_cap_step_frame >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  `MEM i.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
     SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSERT; ASSERT_UNREACHABLE]` by fs[MEM] >>
  drule_all step_pure_opcode_frame >> strip_tac >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem extcall_return_size_test_run[local]:
  emit_op RETURNDATASIZE [] sa = (rds,s1) /\
  emit_op LT [rds; Lit (n2w mn)] s1 = (small,s2) /\
  emit_op ISZERO [small] s2 = (ok,s3) /\
  fresh_vars_wrt sa s /\ mn < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa s3) s = OK t /\
    eval_operand ok t = SOME (bool_to_word (mn <= LENGTH s.vs_returndata)) /\
    eval_operand rds t = SOME (n2w (LENGTH s.vs_returndata)) /\
    fresh_vars_wrt s3 t /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p t = SOME w)
Proof
  strip_tac >> drule_all raw_call_size_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `eval_operand (Lit (n2w mn)) u = SOME (n2w mn)` by simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  drule_all emit_op_ISZERO_correct >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac
  >- (irule run_emitted_compose3 >> qexistsl_tac [`u`, `v`, `s1`, `s2`] >>
      simp[] >> imp_res_tac emit_op_extends >> simp[]) >>
  simp[NOT_LESS] >> metis_tac[]
QED

Theorem extcall_return_decode_stages[local]:
  compile_return_value_decode mn mx sa = (hi,sb) ==>
  ?rds s1 small s2 ok s3 s4.
    emit_op RETURNDATASIZE [] sa = (rds,s1) /\
    emit_op LT [rds; Lit (n2w mn)] s1 = (small,s2) /\
    emit_op ISZERO [small] s2 = (ok,s3) /\
    emit_void ASSERT [ok] s3 = ((),s4) /\
    compile_builtin_min rds (Lit (n2w mx)) T s4 = (hi,sb)
Proof
  simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[compile_builtin_min_def, comp_bind_def] >> metis_tac[]
QED

Theorem extcall_return_decode_success_run[local]:
  compile_return_value_decode mn mx sa = (hi,sb) /\
  fresh_vars_wrt sa s /\ mn < dimword (:256) /\ mx < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\ mn <= LENGTH s.vs_returndata ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand hi t = SOME (n2w (MIN (LENGTH s.vs_returndata) mx))
Proof
  strip_tac >> drule extcall_return_decode_stages >> strip_tac >>
  drule_all extcall_return_size_test_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `eval_operand ok u = SOME 1w` by fs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >>
  disch_then (qx_choose_then `v` strip_assume_tac) >> gvs[] >>
  `eval_operand (Lit (n2w mx)) u = SOME (n2w mx)` by simp[eval_operand_def] >>
  drule_all compile_builtin_min_correct >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac >- suspend "sequence" >>
  fs[w2n_n2w] >> simp[MIN_DEF] >>
  Cases_on `LENGTH s.vs_returndata < mx` >> simp[] >>
  Cases_on `LENGTH s.vs_returndata = mx` >> simp[]
QED

Resume extcall_return_decode_success_run[sequence]:
  `s3.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa s3` by
    (imp_res_tac emit_op_extends >> metis_tac[emit_extends_trans]) >>
  `sb.cs_current_insts = s4.cs_current_insts ++ emitted_insts s4 sb` by
    (gvs[compile_builtin_min_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
     imp_res_tac emit_op_extends >> imp_res_tac compile_select_extends >>
     metis_tac[emit_extends_trans]) >>
  irule run_emitted_compose3 >> qexistsl_tac [`u`, `u`, `s3`, `s4`] >>
  simp[] >> imp_res_tac emit_void_extends >> simp[]
QED

Finalise extcall_return_decode_success_run[local]

Theorem extcall_return_decode_success_mem:
  compile_return_value_decode mn mx sa = (hi,sb) /\
  mn < dimword (:256) /\ mx < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\ mn <= LENGTH s.vs_returndata /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    eval_operand hi u = SOME (n2w (MIN (LENGTH s.vs_returndata) mx)) /\
    stmt_state_rel ctx func cenv cx es u /\ alloca_history func u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >> drule extcall_return_decode_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ (emitted_insts sa sb)`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     fs[MEM] >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> GAS)
     (emitted_insts sa sb)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ (emitted_insts sa sb)`
       (fn th => strip_assume_tac
         (MP (Q.SPEC `i` (REWRITE_RULE [EVERY_MEM] th))
           (ASSUME ``MEM i (emitted_insts sa sb)``))) >>
     fs[MEM, is_terminator_def, is_ext_call_op_def] >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
     eval_operand hi t0 = SOME (n2w (MIN (LENGTH s.vs_returndata) mx))` by
    (mp_tac (Q.INST [`s` |-> `drop_fresh sa s`] extcall_return_decode_success_run) >>
     simp[fresh_vars_wrt_drop_fresh, drop_fresh_def] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> fs[same_blocks_def] >> metis_tac[]) >>
  drule_all clean_run_counted_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all extcall_return_decode_frame >> strip_tac >>
  suspend "finish"
QED

Resume extcall_return_decode_success_mem[finish]:
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = s with vs_vars := t.vs_vars` (fn th => once_rewrite_tac[th]) >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    metis_tac[gas_path_mem_allocation_state] >>
  `eval_operand hi t = SOME (n2w (MIN (LENGTH s.vs_returndata) mx))` by
    (mp_tac (Q.SPECL [`hi`,`t0`,`t.vs_vars`] eval_operand_vars_ext) >>
     simp[] >> fs[vars_ext_def] >> metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, instIdxIndepTheory.eval_op_inst_idx,
    lookup_var_def] >>
  qpat_assum `t = s with vs_vars := t.vs_vars`
    (strip_assume_tac o REWRITE_RULE [venom_state_component_equality]) >>
  fs[same_blocks_def, lookup_var_def] >> conj_tac
  >- (`LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
       LENGTH sb.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
      qpat_assum `LENGTH sa.cs_current_insts + _ = LENGTH sb.cs_current_insts`
        (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  simp[venom_state_component_equality]
QED

Finalise extcall_return_decode_success_mem

Theorem extcall_return_decode_reject_run[local]:
  compile_return_value_decode mn mx sa = (hi,sb) /\
  fresh_vars_wrt sa s /\ mn < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\ LENGTH s.vs_returndata < mn ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    t.vs_returndata = []
Proof
  strip_tac >> drule extcall_return_decode_stages >> strip_tac >>
  drule_all extcall_return_size_test_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `eval_operand ok u = SOME 0w` by fs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  `inst_extends sa s3` by
    (imp_res_tac inst_extends_emit_op >> metis_tac[inst_extends_trans]) >>
  `inst_extends s3 s4` by
    metis_tac[inst_extends_emit_void] >>
  `inst_extends s4 sb` by
    (gvs[compile_builtin_min_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
     imp_res_tac inst_extends_emit_op >>
     imp_res_tac (REWRITE_RULE [GSYM inst_extends_def] compile_select_extends) >>
     metis_tac[inst_extends_trans]) >>
  `run_inst_seq (emitted_insts sa s4) s =
    Abort Revert_abort (revert_state (set_returndata [] u))` by
    metis_tac[run_inst_seq_emit_extend] >>
  `inst_extends sa s4` by metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_abort_extends >>
  strip_tac >> goal_assum drule >> simp[revert_state_def, set_returndata_def]
QED

Theorem extcall_return_decode_reject_mem:
  compile_return_value_decode mn mx sa = (hi,sb) /\
  mn < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  LENGTH s.vs_returndata < mn /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\ t.vs_returndata = []
Proof
  strip_tac >> drule extcall_return_decode_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ (emitted_insts sa sb)`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     fs[MEM] >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> GAS)
     (emitted_insts sa sb)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ (emitted_insts sa sb)`
       (fn th => strip_assume_tac
         (MP (Q.SPEC `i` (REWRITE_RULE [EVERY_MEM] th))
           (ASSUME ``MEM i (emitted_insts sa sb)``))) >>
     fs[MEM, is_terminator_def, is_ext_call_op_def] >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) =
       Abort Revert_abort t0 /\ t0.vs_returndata = []` by
    (mp_tac (Q.INST [`s` |-> `drop_fresh sa s`] extcall_return_decode_reject_run) >>
     simp[fresh_vars_wrt_drop_fresh, drop_fresh_def] >> metis_tac[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> fs[same_blocks_def] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
  (impl_tac >- fs[EVERY_MEM]) >> strip_tac >>
  fs[gas_marked_path_def] >> goal_assum drule >>
  fs[vars_ext_def, venom_state_component_equality]
QED
