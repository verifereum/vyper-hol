(* A constructor body that falls off its end at sb runs the jump to the exit
 * block, the unlock and the epilogue memory-safely, to a halt.  The memory
 * twin of deploy_ctor_fallthrough.
 * TOP-LEVEL: deploy_ctor_fallthrough_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemFallthrough
Ancestors
  ctorDeployLoweringDefs stmtSimDefs memSafeRun immutableDeployExecution
  allocaSiteResource exprLoweringProps venomInst venomExecSemantics venomState
  fragExecMem instMemFrontier ctorReturnFrame nonreentrantExit loweringHalt
  stmtSimProps bodySim fragExec compileEnv emitHelper moduleLowering
  exprLoweringProps context unitTransformDefs contextCodegenRel codegenRel

Theorem compile_constructor_epilogue_related_alloca_frontier:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  rt + cap < dimword(:256) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st x)) ==>
  ?t pos codepos.
    step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w (rt + cap))]
      ["%" ++ toString st.cs_next_var]) s = OK t /\
    pos + rt + cap < dimword(:256) /\
    pos + rt + cap <= t.vs_alloca_next /\
    eval_operand (Var ("%" ++ toString st.cs_next_var)) t = SOME (n2w pos) /\
    FLOOKUP s.vs_labels "runtime_begin" = SOME codepos /\
    (cap <> 0 ==> eval_operand imm
      (update_var ("%" ++ toString (st.cs_next_var + 1))
        (n2w (pos + rt)) t) = SOME 0w) /\
    t.vs_memory = s.vs_memory /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_code = s.vs_code /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all compile_constructor_epilogue_alloca_member >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `alloca_room ctx func s /\ alloca_inv s /\ immutable_base_zero cenv s` by
    fs[stmt_state_rel_def] >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = w2n (n2w (rt + cap):bytes32)` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >>
     qpat_x_assum `!inst n base sz. _` drule >>
     disch_then (qspecl_then [`n2w (rt + cap)`, `b`, `sz`] mp_tac) >>
     simp[Abbr `inst`, mk_inst_def]) >>
  `inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit (n2w (rt + cap))] /\
   inst.inst_outputs = ["%" ++ toString st.cs_next_var]` by
    simp[Abbr `inst`, mk_inst_def, NoAsms] >>
  drule_all alloca_site_execute >> strip_tac >>
  qpat_x_assum `!id p sz. _` kall_tac >>
  qpat_x_assum `!b sz. _` kall_tac >>
  `b + rt + cap <= t.vs_alloca_next` by
    (gvs[wordsTheory.w2n_n2w] >> decide_tac) >>
  `b + rt + cap < dimword(:256)` by
    (drule alloca_room_next_lt >> gvs[wordsTheory.w2n_n2w] >> decide_tac) >>
  `?codepos. FLOOKUP s.vs_labels "runtime_begin" = SOME codepos` by
    fs[immutable_base_zero_alt, optionTheory.IS_SOME_EXISTS] >>
  qexistsl_tac [`t`, `b`, `codepos`] >>
  simp[Abbr `inst`, mk_inst_def, step_inst_base_def, eval_operand_def] >>
  qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
  simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[update_var_def, mk_inst_def] >>
  rpt strip_tac >>
  gvs[] >> Cases_on `imm` >>
  gvs[immutable_base_zero_alt, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      compileEnvTheory.not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LE_ADD,
            stringTheory.STRCAT_def, listTheory.APPEND]
QED

Theorem constructor_epilogue_copy_return_mem_ok[local]:
  eval_operand (Var buf) s = SOME (n2w pos) /\
  pos + rt + cap < dimword(:256) /\
  pos + rt + cap <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w rt)] [];
     mk_inst ret_id RETURN [Var buf; Lit (n2w (rt + cap))] []] s
Proof
  strip_tac >>
  `pos < dimword(:256) /\ rt < dimword(:256) /\
   rt + cap < dimword(:256)` by decide_tac >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  conj_tac >- (simp[below_frontier_CODECOPY, eval_operand_def,
                    wordsTheory.w2n_n2w] >> decide_tac) >>
  conj_tac >- simp[inst_dload_in_section_other, mk_inst_def] >>
  simp[mk_inst_def, step_inst_base_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_labels "runtime_begin"` >> simp[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_RETURN,
       inst_dload_in_section_other, mk_inst_def,
       immutable_deploy_write_frame, eval_operand_def,
       write_memory_with_expansion_def, wordsTheory.w2n_n2w] >>
  simp[GSYM mk_inst_def, below_frontier_RETURN, eval_operand_def,
       lookup_var_def, wordsTheory.w2n_n2w] >>
  gvs[eval_operand_def, lookup_var_def] >> decide_tac
QED

Theorem constructor_epilogue_tail_mem_ok[local]:
  eval_operand (Var buf) s = SOME (n2w pos) /\ buf <> tmp /\
  eval_operand imm (update_var tmp (n2w (pos + rt)) s) = SOME 0w /\
  pos + rt + cap < dimword(:256) /\
  pos + rt + cap <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id ADD [Var buf; Lit (n2w rt)] [tmp];
     mk_inst copy_id MCOPY [Var tmp; imm; Lit (n2w cap)] [];
     mk_inst code_id CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w rt)] [];
     mk_inst ret_id RETURN [Var buf; Lit (n2w (rt + cap))] []] s
Proof
  strip_tac >>
  `pos < dimword(:256) /\ rt < dimword(:256) /\ cap < dimword(:256) /\
   pos + rt < dimword(:256)` by decide_tac >>
  qabbrev_tac `s1 = update_var tmp (n2w (pos + rt)) s` >>
  `step_inst_base (mk_inst id ADD [Var buf; Lit (n2w rt)] [tmp]) s = OK s1` by
    simp[Abbr `s1`, mk_inst_def, step_inst_base_def, exec_pure2_def,
         eval_operand_def, wordsTheory.word_add_n2w] >>
  `eval_operand (Var buf) s1 = SOME (n2w pos) /\
   eval_operand (Var tmp) s1 = SOME (n2w (pos + rt)) /\
   s1.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> fs[eval_operand_def, lookup_var_def]) >>
  `eval_operand imm s1 = SOME 0w` by fs[Abbr `s1`] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  conj_tac >- simp[inst_dload_in_section_other, mk_inst_def] >>
  simp[] >> once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  conj_tac >- (simp[below_frontier_MCOPY, eval_operand_def,
                    wordsTheory.w2n_n2w] >> decide_tac) >>
  conj_tac >- simp[inst_dload_in_section_other, mk_inst_def] >>
  qabbrev_tac `s2 = mcopy (pos + rt) 0 cap s1` >>
  `step_inst_base (mk_inst copy_id MCOPY [Var tmp; imm; Lit (n2w cap)] []) s1 = OK s2` by
    simp[Abbr `s2`, mk_inst_def, step_inst_base_def, eval_operand_def,
         wordsTheory.w2n_n2w] >>
  simp[] >> irule (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
    constructor_epilogue_copy_return_mem_ok) >>
  qexists_tac `pos` >>
  simp[Abbr `s2`, mcopy_def, immutable_deploy_write_frame,
       write_memory_with_expansion_def] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem compile_constructor_epilogue_mem_ok:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  rt + cap < dimword(:256) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st x)) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule_all compile_constructor_epilogue_related_alloca_frontier >>
  strip_tac >> Cases_on `cap = 0`
  >- (gvs[] >> drule compile_constructor_epilogue_zero_insts >> strip_tac >>
      qpat_x_assum `emitted_insts _ _ = _` SUBST1_TAC >>
      once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
      conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
      conj_tac >- simp[inst_dload_in_section_other, mk_inst_def] >>
      simp[] >>
      irule (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
        (Q.INST [`cap` |-> `0`] constructor_epilogue_copy_return_mem_ok)) >>
      qexists_tac `pos` >> simp[]) >>
  `0 < cap` by decide_tac >>
  drule_all compile_constructor_epilogue_positive_insts >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST1_TAC >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  conj_tac >- simp[inst_dload_in_section_other, mk_inst_def] >>
  simp[] >>
  irule (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
    constructor_epilogue_tail_mem_ok) >>
  simp[ASCIInumbersTheory.toString_11] >>
  qexists_tac `pos` >> simp[] >>
  qpat_assum `cap <> 0 ==> eval_operand _ _ = _` mp_tac >>
  pure_rewrite_tac[stringTheory.STRCAT_def, listTheory.APPEND] >>
  gvs[stringTheory.STRCAT_def, listTheory.APPEND]
QED

Theorem epilogue_DROP_EQ_CONS[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem epilogue_return_not_OK[local]:
  !id dst szop s u.
    step_inst_base (mk_inst id RETURN [dst;szop] []) s <> OK u
Proof
  rpt gen_tac >>
  simp[mk_inst_def, Once step_inst_base_def, AllCaseEqs()]
QED

Theorem epilogue_mem_ok_index[local]:
  !pre s n id dst szop.
    EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
    (run_inst_seq_mem_ok (pre ++ [mk_inst id RETURN [dst;szop] []])
       (s with vs_inst_idx := n) <=>
     run_inst_seq_mem_ok (pre ++ [mk_inst id RETURN [dst;szop] []]) s)
Proof
  Induct
  >- simp[run_inst_seq_mem_ok_last] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  once_rewrite_tac[run_inst_seq_mem_ok_def] >>
  simp[instIdxIndepTheory.step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem mem_safe_run_return_seq[local]:
  !pre s fuel ctx fn bb id dst szop.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (pre ++ [mk_inst id RETURN [dst;szop] []])
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    run_inst_seq_mem_ok (pre ++ [mk_inst id RETURN [dst;szop] []]) s ==>
    mem_safe_run fuel ctx fn s
Proof
  Induct
  >- (rpt gen_tac >> simp[run_inst_seq_mem_ok_last] >> strip_tac >>
      `?rest. DROP s.vs_inst_idx bb.bb_instructions =
        mk_inst id RETURN [dst;szop] [] :: rest` by
        (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
      drule epilogue_DROP_EQ_CONS >> strip_tac >>
      `get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [dst;szop] [])` by
        simp[get_instruction_def] >>
      Cases_on `step_inst_base (mk_inst id RETURN [dst;szop] []) s` >>
      gvs[epilogue_return_not_OK] >>
      simp[mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def,
           step_inst_non_invoke, mem_safe_step_non_invoke] >>
      fs[mk_inst_def]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h::rest /\
    isPREFIX (pre ++ [mk_inst id RETURN [dst;szop] []]) rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule epilogue_DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  qpat_x_assum `run_inst_seq_mem_ok (h::_) s` mp_tac >>
  once_rewrite_tac[run_inst_seq_mem_ok_def] >> strip_tac >>
  `mem_safe_step fuel ctx h s` by simp[mem_safe_step_non_invoke] >>
  `step_inst fuel ctx h s = step_inst_base h s` by simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[]
  >~ [`step_inst_base h s = OK s1`]
  >- (`s1.vs_current_bb = s.vs_current_bb` by
        metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
      `mem_safe_run fuel ctx fn s <=>
       mem_safe_run fuel ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
        (drule_all mem_safe_run_step >> simp[]) >>
      simp[] >> first_x_assum irule >>
      qexistsl_tac [`bb`, `dst`, `id`, `szop`] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) pre` by
        fs[listTheory.EVERY_MEM] >>
      simp[epilogue_mem_ok_index]) >>
  simp[mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def]
QED

Theorem compile_constructor_epilogue_mem_safe_run:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  rt + cap < dimword(:256) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st x)) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  mem_safe_run fuel ctx func s
Proof
  strip_tac >> drule_all compile_constructor_epilogue_mem_ok >> strip_tac >>
  drule compile_constructor_epilogue_terminal_shape >> strip_tac >>
  irule mem_safe_run_return_seq >>
  qexistsl_tac [`bb`, `dst`, `id`, `pre`, `szop`] >> simp[] >>
  conj_tac >- (fs[listTheory.EVERY_MEM] >>
               metis_tac[immutable_deploy_prefix_opcodes, listTheory.MEM]) >>
  gvs[]
QED

(* The epilogue's instructions sit at the run's position in its block. *)
Theorem constructor_epilogue_block_prefix[local]:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  ~block_is_terminated st /\ fn_has_code st st' func /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule_all compile_constructor_epilogue_append >> strip_tac >>
  qabbrev_tac `E = emitted_insts st st'` >>
  gvs[fn_has_code_def] >>
  qpat_x_assum `isPREFIX _ bb.bb_instructions` mp_tac >>
  rw[rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
  simp[listTheory.DROP_APPEND]
QED

(* The memory twin of constructor_exit_run: the unlock and the epilogue run
   to a halt memory-safely. *)
Theorem constructor_exit_run_mem[local]:
  !ctx func cenv body_cenv cx es s nr nkey ut st_exit st_epilogue st_final
   rt cap imm.
  cenv.ce_is_ctor /\ same_frame cenv body_cenv /\
  st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func /\
  rt + cap < dimword(:256) /\
  (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st_epilogue x)) /\
  stmt_state_rel ctx func body_cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st_exit.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  ?fuel final. run_from fuel ctx func s = Halt final /\
    mem_safe_run fuel ctx func s
Proof
  rpt gen_tac >> strip_tac >>
  `nr ==> ut` by simp[] >>
  drule_all ctorReturnFrameTheory.constructor_exit_code >> strip_tac >>
  qabbrev_tac `es1 = if nr then
    es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) 0w (es.tStorage cx.txn.target)) es.tStorage
    else es` >>
  qabbrev_tac `s1 = (if nr then tstore (n2w nkey) 0w s else s) with
    vs_inst_idx := LENGTH st_epilogue.cs_current_insts` >>
  `stmt_state_rel ctx func body_cenv cx es1 s1` by
    (simp[Abbr `s1`, stmt_state_rel_inst_idx] >>
     Cases_on `nr` >> gvs[Abbr `es1`] >>
     irule constructor_unlock_stmt_state_rel >> simp[]) >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule optional_unlock_frag_mem >>
  disch_then (qspecl_then [`ctx`, `\s0. s0 = s`, `\s2. s2 = s1`, `\r. F`]
                mp_tac) >>
  simp[Abbr `s1`] >>
  simp[frag_exec_mem_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func body_cenv cx es1 s1` >>
  `body_cenv.ce_is_ctor /\
   (cap <> 0 ==> body_cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x))` by
    gvs[same_frame_def, compile_env_component_equality] >>
  `~s1.vs_halted /\ s1.vs_current_bb = st_epilogue.cs_current_bb /\
   s1.vs_inst_idx = LENGTH st_epilogue.cs_current_insts` by
    simp[Abbr `s1`] >>
  drule_all compile_constructor_epilogue_padded_run_from >> strip_tac >>
  drule_all constructor_epilogue_block_prefix >> strip_tac >>
  qpat_x_assum `!fuel. (!e. _) ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`fuel'`, `final`] >> simp[] >>
  first_x_assum irule >>
  irule compile_constructor_epilogue_mem_safe_run >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem deploy_ctor_fallthrough_mem_safe:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func cx cenv' ee t.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    cenv.ce_is_ctor /\ cenv_top_ext cenv cenv' ee.scopes /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    stmt_state_rel dunit.cu_context func cenv' cx ee t /\ ~t.vs_halted /\
    ~block_is_terminated sb /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?fuel. mem_safe_run fuel dunit.cu_context func t /\
           !e. run_from fuel dunit.cu_context func t <> Error e
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule cenv_top_ext_same_frame >> strip_tac >>
  qspecl_then [`dunit.cu_context`, `func`, `cenv`, `cenv'`, `cx`, `ee`,
               `jump_to exit_lbl t`, `nr`, `nkey`, `ut`, `st_exit`,
               `st_epilogue`, `st_final`, `LENGTH runtime_bc`,
               `imm_len tops`, `imm`] mp_tac constructor_exit_run_mem >>
  impl_tac
  >- gvs[new_block_def, jump_to_def, stmt_state_rel_jump_to] >>
  strip_tac >>
  qspecl_then [`dunit.cu_context`, `func`, `sb`, `sj`, `t`,
               `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`]
    mp_tac run_from_jump_end_mem >>
  impl_tac
  >- (gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
      simp[mk_inst_def, is_terminator_def, Once step_inst_base_def,
           inst_mem_below_frontier_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def]) >>
  disch_then (qspecl_then [`fuel`, `Halt final`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `fuel'` >> simp[]
QED
