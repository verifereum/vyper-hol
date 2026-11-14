(* Same-run source and target entry facts for the successful lock prefix. *)
Theory nonreentrantEntryPath
Ancestors
  nonreentrantEquiv transientLockPtr transientLockFrameProps transientLockProps
  nonreentrantSource accountsRelProps fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasMode
  fragGasPathPtr fragGasSeqMem fragExecMem fragExec memSafeRun unitTransformDefs ptrSafeRun
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

(* The ghost update is independent of the mask used to check the prefix. *)
Theorem nonreentrant_lock_paths:
  compile_nonreentrant_lock nkey T iv sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ tload (n2w nkey) s <> 1w /\
  (~iv ==> ~s.vs_call_ctx.cc_static) /\
  (!b. ~((n2w nkey,b) IN tn.t_trans)) ==>
  ?u G' tn'.
    run_inst_seq (transient_lock_code nkey iv sa) s = OK u /\
    (!D. inst_seq_ptr D 0 ctx func [] G tn
      (transient_lock_code nkey iv sa) s G' tn') /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,func,[])
      (s,G,tn) []
      (OK (u with vs_inst_idx :=
        s.vs_inst_idx + LENGTH (transient_lock_code nkey iv sa)),G',tn')) /\
    (!D fuel.
      ptr_safe_run D 0 fuel ctx func [] G' tn'
        (u with vs_inst_idx :=
          s.vs_inst_idx + LENGTH (transient_lock_code nkey iv sa)) ==>
      ptr_safe_run D 0 fuel ctx func [] G tn s)
Proof
  strip_tac >>
  `?u. run_inst_seq (transient_lock_code nkey iv sa) s = OK u` by
    (Cases_on `iv` >> simp[transient_lock_code_execution]) >>
  mp_tac (Q.INST [`D` |-> `ARB:dead`, `PG` |-> `[]`,
    `ss` |-> `s`, `st` |-> `sa`]
    (SPEC_ALL transient_lock_code_ptr_frame)) >> simp[] >> strip_tac >>
  `!D. inst_seq_ptr D 0 ctx func [] G tn
    (transient_lock_code nkey iv sa) s G' tn'` by
    (gen_tac >>
     mp_tac (Q.INST [`PG` |-> `[]`, `ss` |-> `s`, `st` |-> `sa`]
       (SPEC_ALL transient_lock_code_ptr_frame)) >> simp[] >> strip_tac >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code nkey iv sa)
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[compile_nonreentrant_lock_transient_prefix] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (transient_lock_code nkey iv sa)` by
    (Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def,
      is_terminator_def]) >>
  `run_inst_seq_mem_ok (transient_lock_code nkey iv sa) s` by
    (irule transient_lock_code_memory_checks >> Cases_on `iv` >>
     simp[transient_lock_code_def, mk_inst_def]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (rpt gen_tac >>
      mp_tac (Q.INST [`lo` |-> `0`, `PG` |-> `[]`]
        (Q.SPECL [`transient_lock_code nkey iv sa`, `s`, `u`,
        `G`, `tn`, `G'`, `tn'`, `ctx`, `func`, `bb`]
        run_inst_seq_gas_origin_ptr_path)) >>
      simp[] >>
      `FILTER (\i. i.inst_opcode = GAS) (transient_lock_code nkey iv sa) = []` by
        (Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]) >>
      simp[]) >>
  rpt strip_tac >>
  mp_tac (Q.INST [`lo` |-> `0`, `PG` |-> `[]`]
    (Q.SPECL [`transient_lock_code nkey iv sa`, `s`, `u`,
    `G`, `tn`, `G'`, `tn'`, `ctx`, `func`, `bb`, `fuel`]
    run_inst_seq_ptr_continuation)) >> simp[]
QED

Theorem transient_lock_checked_ghost_frame:
  ghost_inv H NONE cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  cenv.ce_return_buf = NONE /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ghost_inv H NONE cenv cx es G' tn'
    (transient_lock_checked_state sa nkey s)
Proof
  strip_tac >> irule ghost_inv_fresh_frame >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
  simp[transient_lock_checked_state_def, update_var_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var) /\
   x <> STRING #"%" (toString (sa.cs_next_var + 1)) /\
   x <> STRING #"%" (toString (sa.cs_next_var + 2))` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

(* Horizon-indexed relations share the physical and ghost endpoints above. *)
Theorem nonreentrant_lock_relations:
  storage_locks_separated (FST H) (SND H) /\ MEM nkey (SND H) /\
  nkey < dimword (:256) /\ cx.nonreentrant_slot = SOME nkey /\
  acquire_nonreentrant_lock cx.txn.target nkey iv es = (INL (),locked) /\
  (~iv ==> ~cx.txn.is_static) /\
  compile_nonreentrant_lock nkey T iv sa = ((),sb) /\
  tload (n2w nkey) s <> 1w /\ fresh_vars_wrt sa s /\
  local_ptrs_reserved cenv sa /\ cenv.ce_return_buf = NONE /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv H NONE cenv cx es G tn s /\
  run_inst_seq (transient_lock_code nkey iv sa) s = OK u /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  stmt_state_rel H ctx func cenv cx locked u /\
  ghost_inv H NONE cenv cx locked G' tn' u
Proof
  strip_tac >>
  `state_rel H func cenv cx es s` by fs[stmt_state_rel_def] >>
  `state_rel H func cenv cx locked u` by
    (drule_all compile_nonreentrant_lock_source_correct >>
     drule compile_nonreentrant_lock_transient_code >> strip_tac >>
     rpt strip_tac >> gvs[]) >>
  `~iv ==> ~s.vs_call_ctx.cc_static` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  `locked.scopes = es.scopes /\ locked.immutables = es.immutables` by
    (Cases_on `iv` >>
     gvs[acquire_nonreentrant_lock_execution, AllCaseEqs()]) >>
  `stmt_state_rel H ctx func cenv cx es
    (transient_lock_checked_state sa nkey s)` by
    metis_tac[transient_lock_checked_stmt_state_rel] >>
  `ghost_inv H NONE cenv cx es G' tn'
    (transient_lock_checked_state sa nkey s)` by
    (irule transient_lock_checked_ghost_frame >>
     qexistsl_tac [`G`, `tn`] >> simp[]) >>
  conj_tac
  >- (irule stmt_state_rel_allocas_frame >>
      qexistsl_tac [`es`, `transient_lock_checked_state sa nkey s`] >>
      simp[] >> Cases_on `iv` >>
      gvs[transient_lock_code_execution, stmt_state_rel_def,
          immutable_alloca_sep_def, immutable_base_zero_def,
          local_region_def, tstore_def, eval_operand_def, lookup_var_def]) >>
  Cases_on `iv` >> gvs[transient_lock_code_execution]
  >- fs[ghost_inv_def] >>
  irule nonreentrant_ghost_inv_frame >>
  qexists_tac `es` >> simp[]
QED
