(* Joint paths for the transient unlock emitted before external exits. *)
Theory nonreentrantExitPath
Ancestors
  nonreentrantEntryPath nonreentrantEntryEquiv loweringHalt transientLockProps
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec fragExecMem
  ptrSafeRun ptrDiscipline memSafeRun instMemFrontier codegenRel contextCodegenRel
  venomExecSemantics venomInst venomState list rich_list
  emitHelperProps exprLoweringProps compileEnv context emitHelper
  bodyPtrDefs bodyPtrWordBuiltinsIntervalGhost nonreentrantSource unitTransformDefs
  nonreentrantEquiv loweringStateRelDefs vyperScopePreservation vyperState
  fragExecPtr fragGasEmitCtrl gasEvents gasCount moduleLowering stmtLowering
  fragGasOriginPtrLoop vyperInterpreter

(* A store to an untainted literal slot leaves the complete ghost unchanged. *)
Theorem literal_tstore_clean_origin_ptr:
  ~ctx_has_dalloca ctx /\ (!b. ~((key,b) IN tn.t_trans)) /\
  ~ss.vs_halted /\ ~ss.vs_call_ctx.cc_static /\
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id TSTORE [Lit key; Lit value] []]
    (DROP ss.vs_inst_idx bb.bb_instructions) ==>
  gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
    (OK (tstore key value ss with vs_inst_idx := SUC ss.vs_inst_idx), G, tn)
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id TSTORE [Lit key; Lit value] []] ss G tn` by
    (irule literal_tstore_clean_inst_seq_ptr >> simp[]) >>
  `step_inst_base (mk_inst id TSTORE [Lit key; Lit value] []) ss =
    OK (tstore key value ss)` by
    (irule transientLockPropsTheory.step_TSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq_mem_ok [mk_inst id TSTORE [Lit key; Lit value] []] ss` by
    simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, mk_inst_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  mp_tac (Q.INST [`code` |-> `[mk_inst id TSTORE [Lit key; Lit value] []]`,
    `s` |-> `ss`, `t` |-> `tstore key value ss`, `G'` |-> `G`,
    `tn'` |-> `tn`, `lo` |-> `0:num`]
    (SPEC_ALL run_inst_seq_gas_origin_ptr_path)) >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def, arithmeticTheory.ADD1]
QED

(* The actual optional unlock is empty or one clean literal transient store. *)
Theorem optional_transient_unlock_origin_ptr:
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) st =
    ((),st') /\ fn_has_code st st' func /\
  ~ctx_has_dalloca ctx /\ (!b. ~((n2w nkey,b) IN tn.t_trans)) /\
  ~ss.vs_halted /\ ~ss.vs_call_ctx.cc_static /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
    (OK ((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
      vs_inst_idx := LENGTH st'.cs_current_insts), G, tn)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`nr`, `nkey`, `T`, `iv`, `st`, `st'`]
    optional_unlock_code) >> simp[] >> strip_tac >>
  Cases_on `nr /\ ~iv`
  >- (`?bb. lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX [mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []]
         (DROP ss.vs_inst_idx bb.bb_instructions)` by
        (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
         simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
         gvs[] >> simp[DROP_APPEND]) >>
      mp_tac (Q.INST [`key` |-> `n2w nkey`, `value` |-> `0w`,
        `id` |-> `st.cs_next_id`]
        (SPEC_ALL literal_tstore_clean_origin_ptr)) >>
      simp[arithmeticTheory.ADD1]) >>
  gvs[] >>
  qpat_x_assum `ss.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[gas_origin_ptr_path_rules]
QED

(* The unlock preserves every live local/return pointer and every horizon
   storage observation, with the same complete ghost at the next cursor. *)
Theorem optional_transient_unlock_origin_ptr_ghost:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H d cenv cx es G tn ss /\ es'.scopes = es.scopes /\
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) st =
    ((),st') /\ fn_has_code st st' func /\
  ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\ ~ss.vs_call_ctx.cc_static /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
    (OK ((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
      vs_inst_idx := LENGTH st'.cs_current_insts), G, tn) /\
  ghost_inv H d cenv cx es' G tn
    ((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
      vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `stor_taint_ok H cx tn ss` by fs[ghost_inv_def] >>
  `!b. ~((n2w nkey,b) IN tn.t_trans)` by
    (mp_tac (SPEC_ALL nonreentrant_slot_untainted) >> simp[]) >>
  conj_tac
  >- (mp_tac (SPEC_ALL optional_transient_unlock_origin_ptr) >> simp[]) >>
  `ghost_inv H d cenv cx es' G tn ss` by
    (fs[ghost_inv_def] >> first_assum ACCEPT_TAC) >>
  `ghost_inv H d cenv cx es' G tn
    (ss with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    simp[word_interval_ghost_inv_index] >>
  Cases_on `nr /\ ~iv` >> simp[] >>
  mp_tac (Q.INST [`es` |-> `es'`,
    `ss` |-> `ss with vs_inst_idx := LENGTH st'.cs_current_insts`,
    `value` |-> `0w`]
    (SPEC_ALL nonreentrant_ghost_inv_frame)) >> simp[tstore_def]
QED

(* This is the same source release action used by Return and fall-through. *)
Theorem checked_transient_unlock_origin_ptr:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  state_rel H func cenv cx vs ss /\ ghost_inv H d cenv cx vs G tn ss /\
  compile_nonreentrant_unlock nkey T iv st = ((),st') /\
  fn_has_code st st' func /\ ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?vs'.
    (if iv then vyperState$return () else
       release_nonreentrant_lock cx.txn.target nkey) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss =
      OK (if iv then ss else tstore (n2w nkey) 0w ss) /\
    state_rel H func cenv cx vs' (if iv then ss else tstore (n2w nkey) 0w ss) /\
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (OK ((if iv then ss else tstore (n2w nkey) 0w ss) with
        vs_inst_idx := LENGTH st'.cs_current_insts), G, tn) /\
    ghost_inv H d cenv cx vs' G tn
      ((if iv then ss else tstore (n2w nkey) 0w ss) with
        vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `~ss.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  mp_tac (Q.INST [`key` |-> `nkey`, `is_view` |-> `iv`]
    (SPEC_ALL compile_nonreentrant_unlock_source_correct)) >>
  simp[] >> strip_tac >>
  `ss' = if iv then ss else tstore (n2w nkey) 0w ss` by
    (Cases_on `iv`
     >- gvs[compile_nonreentrant_unlock_transient_view, emitted_insts_def,
            run_inst_seq_def] >>
     drule_all compile_nonreentrant_unlock_transient_correct >> gvs[]) >>
  `vs'.scopes = vs.scopes` by
    (Cases_on `iv` >> gvs[vyperStateTheory.return_def] >>
     metis_tac[release_nonreentrant_lock_scopes]) >>
  qexists_tac `vs'` >> simp[] >>
  mp_tac (Q.INST [`nr` |-> `T`, `es` |-> `vs`, `es'` |-> `vs'`]
    (SPEC_ALL optional_transient_unlock_origin_ptr_ghost)) >>
  Cases_on `iv` >> simp[] >> fs[]
QED

(* Reuse the canonical STOP pointer check and the joint exit-edge constructor. *)
Theorem stop_origin_ptr:
  stor_taint_ok H cx tn ss /\ ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb ss.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  gas_origin_ptr_path (cx_dead H cx, 0, explicit, ctx, func, PG) (ss, G, tn) []
    (Halt (halt_state (ss with vs_returndata := [])), G, tn)
Proof
  strip_tac >>
  `ptr_inst_ok (cx_dead H cx) 0 0 ctx func G tn
    (mk_inst id STOP [] []) ss` by
    (irule ptr_inst_ok_stop >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `ss`, `i` |-> `mk_inst id STOP [] []`,
    `D` |-> `cx_dead H cx`, `lo` |-> `0:num`,
    `r` |-> `Halt (halt_state (ss with vs_returndata := []))`]
    (SPEC_ALL exit_inst_origin_ptr)) >>
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
       exit_result_def, gas_events_step_def, gas_count_step_def,
       mem_safe_step_non_invoke, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem compile_guarded_body_stop_unlock_suffix:
  compile_guarded_body cenv nr nkey T iv stmts NONE st = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) st =
    ((),sa) /\
  compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((),sb) /\
  ~block_is_terminated sb ==>
  comp_ignore_bind
    (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ())
    (emit_inst STOP [] []) sb = ((),st')
Proof
  strip_tac >>
  qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
       comp_get_def, comp_return_def]
QED

(* Falling through the actual guarded body releases a mutating guard before
   STOP; neither the unlock nor the exit changes the complete pointer ghost. *)
Theorem compile_guarded_body_stop_unlock_origin_ptr:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H d cenv cx es G tn ss /\
  compile_guarded_body cenv nr nkey T iv stmts NONE st = ((),st') /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) st =
    ((),sa) /\
  compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((),sb) /\
  ~block_is_terminated sb /\ fn_has_code sb st' func /\
  ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\ ~ss.vs_call_ctx.cc_static /\
  ss.vs_current_bb = sb.cs_current_bb /\
  ss.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?su.
    (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) sb =
      ((),su) /\
    gas_origin_ptr_path (cx_dead H cx, 0, explicit, ctx, func, PG)
      (ss, G, tn) []
      (Halt (halt_state
        (((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
          vs_inst_idx := LENGTH su.cs_current_insts) with vs_returndata := [])),
       G, tn)
Proof
  strip_tac >>
  qabbrev_tac `su = SND
    ((if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) sb)` >>
  `(if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) sb =
    ((),su)` by
    (Cases_on `nr` >> Cases_on `iv` >>
     simp[Abbr `su`, compile_nonreentrant_unlock_def, comp_return_def,
          emit_void_def, comp_bind_def, fresh_id_def, emit_def]) >>
  drule_all compile_guarded_body_stop_unlock_suffix >>
  simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
  `su.cs_blocks = sb.cs_blocks /\ su.cs_current_bb = sb.cs_current_bb /\
   isPREFIX sb.cs_current_insts su.cs_current_insts` by
    (mp_tac (Q.SPECL [`nr`, `nkey`, `T`, `iv`, `sb`, `su`]
      optional_unlock_code) >> simp[] >> strip_tac >>
     Cases_on `nr /\ ~iv` >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sb su /\ cs_extends su st'` by
    (conj_tac >> irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qabbrev_tac `u = (if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
    vs_inst_idx := LENGTH su.cs_current_insts` >>
  `gas_origin_ptr_path (cx_dead H cx, 0, explicit, ctx, func, PG)
    (ss,G,tn) [] (OK u,G,tn) /\ ghost_inv H d cenv cx es G tn u` by
    (mp_tac (Q.INST [`st` |-> `sb`, `st'` |-> `su`, `es'` |-> `es`,
       `D` |-> `cx_dead H cx`]
       (SPEC_ALL optional_transient_unlock_origin_ptr_ghost)) >>
     simp[Abbr `u`]) >>
  `~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb` by
    (Cases_on `nr /\ ~iv` >> simp[Abbr `u`, tstore_def]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME (mk_inst su.cs_next_id STOP [] [])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> conj_tac >- metis_tac[] >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[Abbr `u`]) >>
  `gas_origin_ptr_path (cx_dead H cx, 0, explicit, ctx, func, PG) (u,G,tn) []
    (Halt (halt_state (u with vs_returndata := [])),G,tn)` by
    (mp_tac (Q.INST [`ss` |-> `u`, `id` |-> `su.cs_next_id`]
      (SPEC_ALL stop_origin_ptr)) >> simp[] >> fs[ghost_inv_def]) >>
  drule_all gas_origin_ptr_path_trans >> simp[Abbr `u`]
QED

(* External Return uses this prefix before its value/copy/raw return suffix. *)
Theorem compile_return_unlock_origin_ptr_ghost:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H d cenv cx es G tn ss /\ es'.scopes = es.scopes /\
  cenv.ce_nonreentrant = (nr,nkey,T,iv) /\
  compile_return_unlock cenv st = ((),st') /\ fn_has_code st st' func /\
  ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\ ~ss.vs_call_ctx.cc_static /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
    (OK ((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
      vs_inst_idx := LENGTH st'.cs_current_insts), G, tn) /\
  ghost_inv H d cenv cx es' G tn
    ((if nr /\ ~iv then tstore (n2w nkey) 0w ss else ss) with
      vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL optional_transient_unlock_origin_ptr_ghost) >>
  gvs[compile_return_unlock_def]
QED

Theorem checked_return_unlock_origin_ptr:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  state_rel H func cenv cx vs ss /\ ghost_inv H d cenv cx vs G tn ss /\
  cx.nonreentrant_slot = SOME nkey /\
  cenv.ce_nonreentrant = (T,nkey,T,iv) /\
  compile_return_unlock cenv st = ((),st') /\
  fn_has_code st st' func /\ ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?vs'.
    unlock_if_nr cx T iv vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss =
      OK (if iv then ss else tstore (n2w nkey) 0w ss) /\
    state_rel H func cenv cx vs' (if iv then ss else tstore (n2w nkey) 0w ss) /\
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (OK ((if iv then ss else tstore (n2w nkey) 0w ss) with
        vs_inst_idx := LENGTH st'.cs_current_insts), G, tn) /\
    ghost_inv H d cenv cx vs' G tn
      ((if iv then ss else tstore (n2w nkey) 0w ss) with
        vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL checked_transient_unlock_origin_ptr) >>
  gvs[compile_return_unlock_def, unlock_if_nr_def] >>
  Cases_on `iv` >> simp[]
QED
