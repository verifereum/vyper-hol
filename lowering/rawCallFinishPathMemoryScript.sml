(* Counted raw-call finish paths after the external call. *)
Theory rawCallFinishPathMemory
Ancestors
  bodyMemRawCallFinish rawCallRevertPathMemory rawCallCountedRun
  exprSimRawCall exprSimRawCallCalldata fragGasPathMem fragGasSeqMem
  stmtSimProps fragExec emitHelper loweringHalt builtinSimple context compileEnv exprLoweringProps venomExecSemantics
  venomState venomInst finite_map rich_list list
Libs
  monadsyntax

Theorem raw_call_failure_prefix_run[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) ==>
  ?u addr. run_inst_seq (emitted_insts sa sc) s = OK u /\
    eval_operand buf.buf_operand u = SOME addr /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    u.vs_returndata = s.vs_returndata
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read0_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_alloca_def, update_var_def] >>
  Cases_on `FLOOKUP s.vs_allocas (sa.cs_next_id + 1)`
  >- (simp[run_inst_seq_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]) >>
  rename1 `FLOOKUP _ _ = SOME p` >> PairCases_on `p` >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]
QED

Theorem raw_call_failure_prefix_code[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) ==>
  sc.cs_current_bb = sa.cs_current_bb /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sc)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_failure_prefix_counted_mem[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\ fn_has_code sa sc func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u addr. gas_path_mem ctx func s 0 (OK u) /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME addr /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    u.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule_all raw_call_failure_prefix_code >> strip_tac >>
  drule_all raw_call_failure_prefix_run >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    (irule raw_call_failure_prefix_mem_ok >> metis_tac[]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sc)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sc) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sc)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule_all exec_block_run_inst_seq >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc)`,
    `addr`] >>
  simp[eval_operand_def, lookup_var_def] >> metis_tac[LENGTH_APPEND]
QED

Theorem raw_call_failure_counted_mem[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\
  emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] sc = ((),sd) /\
  emit_inst REVERT [buf.buf_operand;rds] [] sd = ((),se) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  fn_has_code sa se func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\
      t.vs_returndata = s.vs_returndata
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\
   cs_extends sd se` by
    (qspecl_then [`RETURNDATASIZE`, `[]`, `sa`] mp_tac ci_mono_emit_op >>
     qspecl_then [`RETURNDATACOPY`, `[buf.buf_operand;Lit 0w;rds]`, `sc`]
       mp_tac ci_mono_emit_void >>
     drule emit_inst_metadata >> drule compile_alloc_buffer_extends >>
     simp[ci_mono_def] >> metis_tac[]) >>
  `cs_extends sa sc /\ cs_extends sc se` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all raw_call_failure_prefix_counted_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~u.vs_halted` by
    (drule gas_path_mem_exec >> strip_tac >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  `eval_operand rds u = SOME (n2w (LENGTH u.vs_returndata)) /\
   LENGTH u.vs_returndata < dimword (:256)` by simp[] >>
  drule_all raw_call_failure_tail_counted_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD]
QED

Theorem raw_call_finish_branch_guarded_mem[local]:
  (?cond ok_lbl fl sa sx x sf z sz rb sp sc se y sk sb success.
  emit_inst JNZ [cond;Label ok_lbl;Label fl] [] sa = ((),sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = ((),sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = ((),se) /\
  new_block ok_lbl se = (y,sk) /\ cs_extends sf se /\ cs_extends sk sb /\
  eval_operand cond s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (~success ==> !t. t.vs_returndata = s.vs_returndata ==>
    R (Abort Revert_abort t)) /\
  (success ==> ?r. gas_path_mem ctx func (jump_to ok_lbl s) 0 r /\ P r)) ==>
  ?r. gas_path_mem ctx func s 0 r /\
    (P r \/ R r)
Proof
  strip_tac >>
  `cs_extends sa sx /\ cs_extends sx sf /\ cs_extends se sk` by
    metis_tac[emit_inst_metadata, cs_extends_new_block] >>
  `cs_extends sx sb /\ cs_extends se sb /\ cs_extends sa sf` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa sx func /\ fn_has_code sf se func` by
    metis_tac[fn_has_code_split, fn_has_code_mid] >>
  qpat_assum `emit_inst JNZ _ _ _ = _`
    (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK (jump_to (if success then ok_lbl else fl) s))` by
    (irule assert_jnz_zero_path_mem >> simp[] >> metis_tac[]) >>
  Cases_on `success`
  >- (gvs[] >> qexists_tac `r` >> simp[] >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD]) >>
  gvs[] >>
  `?t. gas_path_mem ctx func (jump_to fl s) 0 (Abort Revert_abort t) /\
       t.vs_returndata = s.vs_returndata` by
    (`?t. gas_path_mem ctx func (jump_to fl s) 0 (Abort Revert_abort t) /\
          t.vs_returndata = (jump_to fl s).vs_returndata` suffices_by
       simp[jump_to_def] >>
     irule raw_call_failure_counted_mem >> simp[jump_to_def] >>
     qexistsl_tac [`rb`,`z`,`sf`,`sz`,`sp`,`sc`,`se`] >>
     simp[] >> gvs[new_block_def]) >>
  qexists_tac `Abort Revert_abort t` >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD]
QED

Theorem raw_call_success_suffix_counted_mem[local]:
  (if 0 < n then
     do z <- emit_op RETURNDATASIZE [];
        cmp <- emit_op LT [z;Lit (n2w n)];
        cap <- compile_select cmp z (Lit (n2w n));
        emit_void MSTORE [ov;cap]; return ov od
   else return (Lit 0w)) sa = (result,sb) /\
  (0 < n ==> eval_operand ov s = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sa x) /\
    w2n addr + 32 <= s.vs_alloca_next) /\
  n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
       eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    (if 0 < n then result = ov /\ eval_operand result t = SOME addr /\
       raw_call_finish_view t = raw_call_finish_view
         (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
     else result = Lit 0w /\ eval_operand result t = SOME 0w /\
       raw_call_finish_view t = raw_call_finish_view s)
Proof
  strip_tac >> Cases_on `0 < n`
  >- (gvs[] >> drule_all raw_call_success_counted_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[comp_return_def] >> qexists_tac `s` >>
  simp[gas_path_mem_rules, eval_operand_def]
QED

Theorem raw_call_revert_finish_path_mem:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  (0 < n ==> eval_operand ov s = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sc x) /\
    w2n addr + 32 <= s.vs_alloca_next) /\
  fn_has_code sc sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?r. gas_path_mem ctx func s 0 r /\
    ((?u. r = OK u /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\ success /\
       (!a w. (!x. a = Var x ==> not_fresh_at sc x) /\
          eval_operand a s = SOME w ==> eval_operand a u = SOME w) /\
       (if 0 < n then result = ov /\ eval_operand result u = SOME addr /\
          raw_call_finish_view u = raw_call_finish_view
            (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
        else result = Lit 0w /\ eval_operand result u = SOME 0w /\
          raw_call_finish_view u = raw_call_finish_view s)) \/
     (?u. ~success /\ r = Abort Revert_abort u /\
       u.vs_returndata = s.vs_returndata))
Proof
  strip_tac >> drule raw_call_finish_revert_compile >>
  simp[arithmeticTheory.GREATER_DEF] >> strip_tac >>
  rename1 `fresh_label "call_failed" ce = (fl,s2)` >>
  rename1 `fresh_label "call_ok" s2 = (kl,s3)` >>
  `ce = sc /\ success' = ok` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  rename1 `fresh_label "call_failed" sc = (fl,s2)` >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(case _ of RegularCall => _ | DelegateCall => _ | StaticCall => _) = _` kall_tac >>
  `ci_mono sc s3 /\ ci_mono s3 s10 /\ cs_extends s5 s9 /\ cs_extends s10 sb` by
    suspend "metadata" >>
  `cs_extends sc s3 /\ cs_extends s3 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s3 sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `cs_extends s3 s10` by fs[ci_mono_def] >>
  `fn_has_code s10 sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `s.vs_current_bb = s3.cs_current_bb /\
   s.vs_inst_idx = LENGTH s3.cs_current_insts` by
    (imp_res_tac emitHelperPropsTheory.fresh_label_props >> simp[]) >>
  suspend "branch"
QED

Resume raw_call_revert_finish_path_mem[metadata]:
  `ci_mono sc s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  `cs_extends s10 sb` by
    (Cases_on `0 < n` >> fs[comp_return_def]
     >- (drule raw_call_success_code >> strip_tac >>
         irule cs_extends_same_block >>
         fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
     gvs[] >> simp[cs_extends_refl]) >>
  fs[ci_mono_def] >> rpt conj_tac >> metis_tac[cs_extends_trans]
QED

Resume raw_call_revert_finish_path_mem[branch]:
  ho_match_mp_tac raw_call_finish_branch_guarded_mem >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void RETURNDATACOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  simp[] >> qexistsl_tac [`sb`,`success`] >> simp[] >> strip_tac >>
  suspend "success"
QED

Resume raw_call_revert_finish_path_mem[success]:
  `sc.cs_next_var <= s10.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `?t. gas_path_mem ctx func (jump_to kl s) 0 (OK t) /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (!a w. (!x. a = Var x ==> not_fresh_at s10 x) /\
        eval_operand a (jump_to kl s) = SOME w ==> eval_operand a t = SOME w) /\
     (if 0 < n then result = ov /\ eval_operand result t = SOME addr /\
        raw_call_finish_view t = raw_call_finish_view
          (mstore (w2n addr) (n2w (MIN (LENGTH (jump_to kl s).vs_returndata) n)) (jump_to kl s))
      else result = Lit 0w /\ eval_operand result t = SOME 0w /\
        raw_call_finish_view t = raw_call_finish_view (jump_to kl s))` by
    (irule raw_call_success_suffix_counted_mem >>
     goal_assum (drule_at Any) >>
     simp[jump_to_def] >>
     gvs[new_block_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> simp[]) >>
  qexists_tac `OK t` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      simp[jump_to_def] >> rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sc` >> simp[]) >>
  `!p w. mstore p w (jump_to kl s) = jump_to kl (mstore p w s)` by
    simp[mstore_def, jump_to_def, write_memory_with_expansion_def] >>
  `(jump_to kl s).vs_returndata = s.vs_returndata` by simp[jump_to_def] >>
  fs[raw_call_finish_view_control]
QED

Finalise raw_call_revert_finish_path_mem
