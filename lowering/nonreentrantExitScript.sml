Theory nonreentrantExit
Ancestors
  list rich_list
  loweringHalt fragExecMem instMemFrontier
  context compileEnv exprLoweringProps venomState venomInst venomExecSemantics
  transientLockPtr fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  fragGasEmitCtrl emitHelperProps gasCount gasEvents
  fragExec fragGasMode unitTransformDefs memSafeRun
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  nonreentrantEquiv bodyPtrDefs ghostPcTransportPtr sourceUnitExecution
  loweringStateRelDefs vyperInterpreter vyperState accountsRelProps finite_map
  pred_set words arithmetic

Theorem literal_tstore_mem_safe[local]:
  !id key s.
    inst_mem_below_frontier (mk_inst id TSTORE [Lit key; Lit 0w] []) s
Proof
  rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem literal_tstore_step[local]:
  !id key s.
    ~s.vs_call_ctx.cc_static ==>
    step_inst_base (mk_inst id TSTORE [Lit key; Lit 0w] []) s =
    OK (tstore key 0w s)
Proof
  rpt gen_tac >> simp[mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def, eval_operands_def]
QED

(* The paths share one endpoint and the actual transient taint update. *)
Theorem optional_transient_unlock_paths_joint:
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) st =
    ((),st') /\ fn_has_code st st' func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  (nr /\ ~iv ==> ~s.vs_call_ctx.cc_static /\ allocas_from lo s) /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u tn'.
    u = ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
           vs_inst_idx := LENGTH st'.cs_current_insts) /\
    tn' = (if nr /\ ~iv then
       tn with t_trans := key_update tn.t_trans (n2w nkey) {} else tn) /\
    tn'.t_var = tn.t_var /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_imm = tn.t_imm /\
    (!op. op_taint tn' op = op_taint tn op) /\
    gas_path ctx func s 0 (OK u) /\
    gas_path_mem ctx func s 0 (OK u) /\
    (!D explicit.
       gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,G,tn')) /\
    (!D fuel.
       ptr_safe_run D lo fuel ctx func PG G tn' u ==>
       ptr_safe_run D lo fuel ctx func PG G tn s) /\
    ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    u.vs_gas_readings = s.vs_gas_readings /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_code = s.vs_code /\ u.vs_labels = s.vs_labels /\
    (!op. eval_operand op u = eval_operand op s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`ut` |-> `T`] (SPEC_ALL optional_unlock_code)) >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `code = if nr /\ ~iv then
    [mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []] else []` >>
  qabbrev_tac `t = if nr /\ ~iv then tstore (n2w nkey) 0w s else s` >>
  qabbrev_tac `tn1 = if nr /\ ~iv then
    tn with t_trans := key_update tn.t_trans (n2w nkey) {} else tn` >>
  `st'.cs_current_insts = st.cs_current_insts ++ code /\
   st'.cs_current_bb = st.cs_current_bb` by
    (Cases_on `nr /\ ~iv` >> gvs[Abbr `code`]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
     gvs[] >> simp[DROP_APPEND]) >>
  `run_inst_seq code s = OK t` by
    (Cases_on `nr /\ ~iv` >>
     gvs[Abbr `code`, Abbr `t`, run_inst_seq_def, literal_tstore_step]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s G tn1` by
    (gen_tac >> Cases_on `nr /\ ~iv` >>
     gvs[Abbr `code`, Abbr `tn1`, inst_seq_ptr_def] >>
     mp_tac (Q.INST [`ss` |-> `s`, `key` |-> `n2w nkey`,
       `value` |-> `0w`, `id` |-> `st.cs_next_id`]
       (SPEC_ALL literal_tstore_inst_seq_ptr_at)) >> simp[inst_seq_ptr_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (Cases_on `nr /\ ~iv` >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  `ctx_has_dalloca ctx ==>
    !pre i post u. code = (pre ++ [i]) ++ post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u` by
    (strip_tac >> rpt gen_tac >> Cases_on `nr /\ ~iv` >> Cases_on `pre` >>
     simp[Abbr `code`] >> strip_tac >> gvs[mk_inst_def, dalloca_no_wrap_def]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `nr /\ ~iv` >>
     simp[Abbr `code`, mk_inst_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G,tn1)` by
    (rpt gen_tac >>
     mp_tac (Q.SPECL [`code`, `s`, `t`, `G`, `tn`, `G`, `tn1`,
       `ctx`, `func`, `bb`] run_inst_seq_gas_origin_ptr_path) >> simp[] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `gas_path ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
   gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (first_x_assum (qspecl_then [`ARB:dead`, `{}:(string # num) set`]
       mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_path_ptr_erase >> drule gas_origin_path_erase >>
     simp[gas_marked_path_def]) >>
  `tn1.t_var = tn.t_var /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_imm = tn.t_imm /\
   (!op. op_taint tn1 op = op_taint tn op)` by
    (Cases_on `nr /\ ~iv` >> simp[Abbr `tn1`, op_taint_def]) >>
  `!D fuel.
    ptr_safe_run D lo fuel ctx func PG G tn1
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH code) ==>
    ptr_safe_run D lo fuel ctx func PG G tn s` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`code`, `s`, `t`, `G`, `tn`, `G`, `tn1`,
       `ctx`, `func`, `bb`, `fuel`] run_inst_seq_ptr_continuation) >> simp[]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_gas_readings = s.vs_gas_readings /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_code = s.vs_code /\ t.vs_labels = s.vs_labels /\
   (!op. eval_operand op t = eval_operand op s)` by
    (Cases_on `nr /\ ~iv` >> simp[Abbr `t`, tstore_def] >>
     Cases >> simp[eval_operand_def, lookup_var_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH st'.cs_current_insts`, `tn1`] >>
  `LENGTH st'.cs_current_insts = s.vs_inst_idx + LENGTH code` by simp[] >>
  qpat_x_assum `s.vs_inst_idx = _` SUBST_ALL_TAC >>
  fs[ADD_COMM] >> simp[Abbr `t`, Abbr `tn1`]
QED

Theorem empty_frag_mem_indexed[local]:
  !ctx st P Q R.
    (!s. P s ==> Q (s with vs_inst_idx := LENGTH st.cs_current_insts)) ==>
    frag_exec_mem ctx st st P Q R
Proof
  rw[frag_exec_mem_def] >> disj1_tac >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!s. P s ==> _` (qspec_then `s` mp_tac) >>
      qpat_x_assum `s.vs_inst_idx = _`
        (fn th => pure_once_rewrite_tac[GSYM th]) >> simp[]) >>
  rpt strip_tac >> qexists_tac `fuel` >> simp[]
QED

Theorem optional_unlock_frag_mem:
  !ctx nr nkey ut iv st st' P Q R.
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      st = ((), st') /\
    (nr /\ ~iv ==> ut) /\
    (nr /\ ~iv ==> !s. P s ==> ~s.vs_call_ctx.cc_static) /\
    (!s. P s ==>
         Q ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
              vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> drule_all optional_unlock_code >> strip_tac >>
  Cases_on `nr /\ ~iv`
  >- (gvs[] >> irule frag_exec_mem_step >> simp[] >>
      rpt strip_tac >> res_tac >>
      gvs[literal_tstore_mem_safe, literal_tstore_step, is_terminator_def]) >>
  gvs[] >> irule empty_frag_mem_indexed >> simp[]
QED

(* The zero store can remove taint without making any dead byte live. *)
Theorem optional_transient_unlock_stor_taint:
  u = ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
         vs_inst_idx := n) /\
  tn' = (if nr /\ ~iv then
    tn with t_trans := key_update tn.t_trans (n2w nkey) {} else tn) /\
  dead_lo_ok H (DF H) lo cenv cx /\ stor_taint_ok_at (DF H) tn s ==>
  stor_taint_ok_at (DF H) tn' u
Proof
  strip_tac >> Cases_on `nr /\ ~iv` >>
  gvs[stor_taint_ok_at_def, dead_lo_ok_def, tstore_def,
      cx_dead_def, combinTheory.APPLY_UPDATE_THM] >>
  fs[SUBSET_DEF, key_update_def] >>
  rpt strip_tac >> res_tac >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >> gvs[] >>
  irule storage_dead_update_zero >>
  rename1 `storage_dead H T _ (w2n slot) byte` >>
  qpat_x_assum `!x. x IN tn.t_trans ==> _`
    (qspec_then `(slot,byte)` mp_tac) >> simp[]
QED

(* Explicit Return and body fallthrough share this terminal suffix. *)
Theorem optional_transient_unlock_stop_joint_at:
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) st =
    ((),su) /\
  emit_inst STOP [] [] su = ((),sb) /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lo s /\
  (nr /\ ~iv ==> ~s.vs_call_ctx.cc_static) /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ss tn'.
    ss.vs_returndata = [] /\ ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient =
      (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
       else s.vs_transient) /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions /\
    ss = halt_state
      ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
        <|vs_inst_idx := LENGTH su.cs_current_insts; vs_returndata := []|>) /\
    (!H explicit.
       dead_lo_ok H (DF H) lo cenv cx /\ stor_taint_ok_at (DF H) tn s ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (Halt ss,G,tn'))
Proof
  strip_tac >>
  mp_tac (Q.INST [`st'` |-> `su`] optional_transient_unlock_paths_joint) >>
  impl_tac >- simp[] >> strip_tac >>
  `allocas_from lo u` by
    (PURE_REWRITE_TAC[allocas_from_def] >>
     qpat_assum `u.vs_allocas = s.vs_allocas`
       (fn eq => PURE_ONCE_REWRITE_TAC[eq]) >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  drule emit_inst_extends >> strip_tac >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME (mk_inst su.cs_next_id STOP [] [])` by
    (qspecl_then [`su`, `sb`, `func`, `[mk_inst su.cs_next_id STOP [] []]`]
       mp_tac fn_has_code_same_block >>
     impl_tac >- simp[] >> strip_tac >>
     qpat_x_assum `!i. i < _ ==> get_instruction _ _ = _`
       (qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >> qexists_tac `bb` >> metis_tac[]) >>
  qexistsl_tac [`halt_state (u with vs_returndata := [])`, `tn'`] >>
  ntac 6 (conj_tac >- (Cases_on `nr /\ ~iv` >>
    gvs[halt_state_def, tstore_def])) >>
  conj_tac >-
    (qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
     Cases_on `nr /\ ~iv` >> simp[venomStateTheory.venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  `stor_taint_ok_at (DF H) tn' u` by
    (irule optional_transient_unlock_stor_taint >> metis_tac[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn') []
     (Halt (halt_state (u with vs_returndata := [])),G,tn')` by
    (irule exit_inst_origin_ptr >> simp[exit_result_def] >>
     qexists_tac `mk_inst su.cs_next_id STOP [] []` >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          gas_events_step_def, gas_count_step_def, mem_safe_step_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
     fs[mk_inst_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def,
        stor_taint_ok_at_def, step_inst_non_invoke,
        step_inst_base_opcode_eqs, step_taint_def, ret_taint_def,
        store_taint_def, imm_taint_def, adopt_reset_def, halt_state_def,
        allocas_from_def] >>
     Cases_on `nr /\ ~iv` >> gvs[tstore_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem optional_transient_unlock_stop_joint:
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) st =
    ((),su) /\
  emit_inst STOP [] [] su = ((),sb) /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lo s /\
  (nr /\ ~iv ==> ~s.vs_call_ctx.cc_static) /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ss tn'.
    ss.vs_returndata = [] /\ ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient =
      (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
       else s.vs_transient) /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions /\
    (!H explicit.
       dead_lo_ok H (DF H) lo cenv cx /\ stor_taint_ok_at (DF H) tn s ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (Halt ss,G,tn'))
Proof
  strip_tac >>
  mp_tac (Q.INST [`DF` |-> `DF`,`cenv` |-> `cenv`,`cx` |-> `cx`,
       `G` |-> `G`,`tn` |-> `tn`,`PG` |-> `PG`]
      (SPEC_ALL optional_transient_unlock_stop_joint_at)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`ss`,`tn'`] strip_assume_tac) >>
  qexistsl_tac [`ss`,`tn'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The compiler uses the same optional release and STOP on fallthrough. *)
Theorem compile_guarded_body_stop_unlock_parts:
  compile_guarded_body cenv nr nkey T iv stmts NONE st = ((),sb) /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) st =
    ((),sl) /\
  compile_stmts cenv NoLoop (BaseT BoolT) stmts sl = ((),se) /\
  ~block_is_terminated se ==>
  ?su. (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ())
          se = ((),su) /\
       emit_inst STOP [] [] su = ((),sb) /\
       cs_extends se su /\ cs_extends su sb
Proof
  strip_tac >>
  `?su. (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ())
          se = ((),su) /\
       emit_inst STOP [] [] su = ((),sb)` by
    (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[moduleLoweringTheory.compile_guarded_body_def,
          comp_ignore_bind_def, comp_bind_def,
          comp_get_def] >>
     Cases_on `(if nr then compile_nonreentrant_unlock nkey T iv
                else comp_return ()) se` >>
     rename1 `_ = (answer,su)` >> Cases_on `answer` >> simp[]) >>
  qexists_tac `su` >> simp[] >>
  reverse conj_tac >- metis_tac[cs_extends_emit_inst] >>
  mp_tac (Q.INST [`st` |-> `se`, `st'` |-> `su`, `ut` |-> `T`]
    (SPEC_ALL optional_unlock_code)) >> simp[] >>
  disch_then SUBST1_TAC >>
  Cases_on `nr /\ ~iv` >> simp[cs_extends_refl] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED


Theorem optional_transient_unlock_stmt_state_rel:
  unlock_if_nr cx nr iv es = (INL (),us) /\
  (nr /\ ~iv ==> cx.nonreentrant_slot = SOME nkey /\
                  nkey < dimword (:256)) /\
  u = ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
         vs_inst_idx := n) /\
  stmt_state_rel H ctx func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx us u
Proof
  strip_tac >> Cases_on `nr /\ ~iv`
  >- (`cx.nonreentrant_slot = SOME nkey` by fs[] >>
      `us = es with <|
         storage_trace := es.storage_trace ++ [StorageLock nkey];
         tStorage := (cx.txn.target =+ update_storage (n2w nkey) 0w
           (es.tStorage cx.txn.target)) es.tStorage |>` by
        gvs[unlock_if_nr_def, release_nonreentrant_lock_execution] >>
      `us.scopes = es.scopes /\ us.immutables = es.immutables` by simp[] >>
      `state_rel H func cenv cx es s /\
       immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
      `state_rel H func cenv cx us (tstore (n2w nkey) 0w s)` by
        (`us = (es with tStorage :=
             (cx.txn.target =+ update_storage (n2w nkey) 0w
               (es.tStorage cx.txn.target)) es.tStorage)
             with storage_trace := us.storage_trace` by
           simp[evaluation_state_component_equality] >>
         pop_assum SUBST1_TAC >> PURE_REWRITE_TAC[state_rel_storage_trace] >>
         irule state_rel_transient_update >>
         simp[] >>
         metis_tac[storage_dead_update_zero]) >>
      `immutable_alloca_sep func cenv cx us (tstore (n2w nkey) 0w s)` by
        (match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `us`, `s`,
           `tstore (n2w nkey) 0w s`] immutable_alloca_sep_fields) >>
         simp[tstore_def] >>
         rpt strip_tac >> qexists_tac `id` >>
         fs[local_region_def, lookup_var_def]) >>
      `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
          immutable_alloca_sep func (cenv with ce_module := src) cx us
            (tstore (n2w nkey) 0w s)` by
        (rpt strip_tac >>
         irule immutable_alloca_sep_fields >>
         qexistsl_tac [`s`,`es`] >>
         qpat_assum `stmt_state_rel H ctx func cenv cx es s`
           (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
         simp[tstore_def] >>
         rpt strip_tac >> qexists_tac `id` >>
         fs[local_region_def, lookup_var_def]) >>
      `stmt_state_rel H ctx func cenv cx us (tstore (n2w nkey) 0w s)` by
        (match_mp_tac (Q.SPECL [`H`, `func`, `cenv`, `cx`, `es`, `s`,
           `us`, `tstore (n2w nkey) 0w s`, `ctx`]
           stmt_state_rel_allocas_frame) >>
         simp[tstore_def] >>
         fs[stmt_state_rel_def, immutable_base_zero_alt, tstore_def]) >>
      gvs[stmt_state_rel_inst_idx]) >>
  `us = es` by gvs[unlock_if_nr_def, vyperStateTheory.return_def] >>
  gvs[stmt_state_rel_inst_idx]
QED

(* Zeroing transient storage preserves each horizon relation. *)
Theorem optional_transient_unlock_source_joint:
  unlock_if_nr cx nr iv es = (INL (),us) /\
  (nr /\ ~iv ==> cx.nonreentrant_slot = SOME nkey /\
                  nkey < dimword (:256)) /\
  u = ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
         vs_inst_idx := n) /\
  tn' = (if nr /\ ~iv then
    tn with t_trans := key_update tn.t_trans (n2w nkey) {} else tn) /\
  dead_lo_ok H (DF H) lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at (DF H) lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx us u /\
  ghost_inv_at (DF H) lo d cenv cx us G tn' u
Proof
  strip_tac >> conj_tac
  >- (drule_all optional_transient_unlock_stmt_state_rel >> disch_then ACCEPT_TAC) >>
  Cases_on `nr /\ ~iv`
  >- (`cx.nonreentrant_slot = SOME nkey` by fs[] >>
      `us = es with <|
         storage_trace := es.storage_trace ++ [StorageLock nkey];
         tStorage := (cx.txn.target =+ update_storage (n2w nkey) 0w
           (es.tStorage cx.txn.target)) es.tStorage |>` by
        gvs[unlock_if_nr_def, release_nonreentrant_lock_execution] >>
      `stor_taint_ok_at (DF H) tn' u` by
        (irule optional_transient_unlock_stor_taint >>
         fs[ghost_inv_at_def] >> metis_tac[]) >>
      qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> strip_tac >>
      Cases_on `d`
      >- (gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
              tstore_def, op_taint_def, lookup_var_def, allocas_from_def] >>
          metis_tac[]) >>
      rename1 `return_buf_ptr (SOME pair) _ _ _ _` >>
      PairCases_on `pair` >>
      gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
          tstore_def, op_taint_def, lookup_var_def, allocas_from_def] >>
      metis_tac[]) >>
  `us = es` by gvs[unlock_if_nr_def, vyperStateTheory.return_def] >>
  gvs[ghost_inv_at_inst_idx]
QED
