(* Same-run source and target entry facts for the successful lock prefix. *)
Theory nonreentrantEntryPath
Ancestors
  nonreentrantEquiv transientLockPtr transientLockFrameProps transientLockProps
  nonreentrantSource fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasMode
  fragGasPathPtr fragGasSeqMem fragExecMem fragExec memSafeRun ptrSafeRun
  ptrDiscipline gasEvents gasCount allocaHistoryFragment allocaHistory
  exprSimPtrProps exprLoweringProps codegenRel contextCodegenRel
  bodyPtrDefs loweringPosts loweringStateRelDefs compileEnv context emitHelper
  emitHelperProps venomExecSemantics venomExecProofs venomInst venomInstProofs
  venomState instIdxIndep vyperInterpreter vyperTypeContract vyperState
  list rich_list arithmetic finite_map pred_set words

Theorem compile_nonreentrant_lock_transient_same_block:
  compile_nonreentrant_lock nkey T iv st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ transient_lock_code nkey iv st
Proof
  Cases_on `iv` >>
  simp[compile_nonreentrant_lock_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, transient_lock_code_def] >>
  strip_tac >> gvs[arithmeticTheory.ADD_ASSOC]
QED

Theorem compile_nonreentrant_lock_transient_prefix:
  compile_nonreentrant_lock nkey T iv st = ((),st') /\
  fn_has_code st st' func /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code nkey iv st)
      (DROP ss.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  drule compile_nonreentrant_lock_transient_same_block >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
  gvs[] >> simp[DROP_APPEND]
QED

Theorem transient_lock_code_memory_checks[local]:
  !code s.
    EVERY (\i. MEM i.inst_opcode [TLOAD; EQ; ISZERO; ASSERT; TSTORE]) code ==>
    run_inst_seq_mem_ok code s
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `inst_mem_below_frontier h s /\ inst_dload_in_section h s` by
    (gvs[MEM] >>
     simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  simp[run_inst_seq_mem_ok_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> fs[]
QED

Theorem nonreentrant_ghost_inv_frame:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H NONE cenv cx es G tn ss /\ es'.scopes = es.scopes ==>
  ghost_inv H NONE cenv cx es' G tn (tstore (n2w nkey) value ss)
Proof
  strip_tac >>
  `stor_taint_ok H cx tn ss` by fs[ghost_inv_def] >>
  `stor_taint_ok H cx tn (tstore (n2w nkey) value ss)` by
    (irule nonreentrant_stor_taint_frame >> simp[]) >>
  fs[ghost_inv_def, return_buf_ptr_def, ptr_covers_def, lookup_var_def,
     tstore_def] >> rpt strip_tac >>
  qpat_x_assum `!name entry p sz. _`
    (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[] >> gvs[]
QED

Theorem transient_lock_checked_stmt_state_rel:
  stmt_state_rel H ctx func cenv cx es ss /\ local_ptrs_reserved cenv st ==>
  stmt_state_rel H ctx func cenv cx es
    (transient_lock_checked_state st nkey ss)
Proof
  strip_tac >>
  `!n. st.cs_next_var <= n ==>
    not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >>
     qexists_tac `st` >> simp[]) >>
  simp[transient_lock_checked_state_def] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule stmt_state_rel_update_var >> simp[]
QED

Theorem nonreentrant_lock_success_source:
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = SOME nkey /\
  lock_if_nr cx T (is_view_mut mut) es_reg = (INL (),es_lock) ==>
  (mut <> View ==> ~cx.txn.is_static) /\
  acquire_nonreentrant_lock cx.txn.target nkey (mut = View) es_reg =
    (INL (),es_lock)
Proof
  strip_tac >>
  `is_view_mut mut = (mut = View)` by
    (drule function_header_nonreentrant_view >> simp[is_view_mut_def]) >>
  `(mut <> View ==> ~cx.txn.is_static)` by
    metis_tac[lock_if_nr_success_not_static] >>
  simp[] >> Cases_on `mut = View` >>
  gvs[lock_if_nr_def, check_not_static_def, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.bind_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()]
QED
