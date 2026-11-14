(* Same-run source and target entry facts for the lock prefix. *)
Theory nonreentrantEntryPath
Ancestors
  nonreentrantEquiv transientLockPtr transientLockFrameProps transientLockProps
  bodyFullHashShaOrigin bodyFullHashShaAbortOrigin
  nonreentrantSource accountsRelProps ghostPcTransportPtr
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasMode
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
    (irule run_inst_seq_mem_ok_every >> Cases_on `iv` >>
     simp[transient_lock_code_def, mk_inst_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
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
    (mp_tac (SPEC_ALL transient_lock_checked_ghost_frame) >> simp[]) >>
  `immutable_alloca_sep func cenv cx es
    (transient_lock_checked_state sa nkey s)` by fs[stmt_state_rel_def] >>
  `immutable_alloca_sep func cenv cx locked u` by
    (match_mp_tac (Q.SPECL
       [`func`, `cenv`, `cx`, `es`, `locked`,
        `transient_lock_checked_state sa nkey s`, `u`]
       immutable_alloca_sep_fields) >>
     simp[] >> Cases_on `iv` >>
     gvs[transient_lock_code_execution, tstore_def] >>
     rpt strip_tac >> qexists_tac `id` >>
     fs[local_region_def, lookup_var_def]) >>
  `immutable_base_zero cenv u` by
    (Cases_on `iv` >> gvs[transient_lock_code_execution] >>
     fs[stmt_state_rel_def, immutable_base_zero_alt, tstore_def]) >>
  conj_tac
  >- (match_mp_tac (Q.SPECL
        [`H`, `func`, `cenv`, `cx`, `es`,
         `transient_lock_checked_state sa nkey s`, `locked`, `u`, `ctx`]
        stmt_state_rel_allocas_frame) >>
      simp[] >> Cases_on `iv` >>
      gvs[transient_lock_code_execution, tstore_def]) >>
  Cases_on `iv` >> gvs[transient_lock_code_execution]
  >- (qpat_x_assum `ghost_inv H NONE cenv cx es G' tn' _` mp_tac >>
      simp[ghost_inv_def] >> strip_tac >> simp[]) >>
  match_mp_tac (Q.INST
    [`es'` |-> `locked`,
     `ss` |-> `transient_lock_checked_state sa nkey s`,
     `G` |-> `G'`, `tn` |-> `tn'`, `value` |-> `1w`]
    nonreentrant_ghost_inv_frame) >> simp[]
QED

Theorem nonreentrant_entry_success_joint:
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = SOME nkey /\ nkey < dimword (:256) /\
  lock_if_nr cx T (is_view_mut mut) es_reg = (INL (), es_lock) /\
  compile_nonreentrant_lock nkey T (mut = View) sa = ((), body_sa) /\
  fn_has_code sa body_sa func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s_reg.vs_halted /\
  ~block_is_terminated sa /\
  s_reg.vs_current_bb = sa.cs_current_bb /\
  s_reg.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s_reg /\ local_ptrs_reserved cenv sa /\
  return_buf_frame NONE cenv sa s_reg /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  alloca_history func s_reg /\
  (!H : (bool # 'a word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es_reg s_reg /\
       ghost_inv H NONE cenv cx es_reg G_reg tn_reg s_reg) ==>
  ?s_lock G_lock tn_lock.
    gas_path ctx func s_reg 0 (OK s_lock) /\
    gas_path_mem ctx func s_reg 0 (OK s_lock) /\
    (!D explicit.
       gas_origin_ptr_path (D, 0, explicit, ctx, func, [])
         (s_reg, G_reg, tn_reg) [] (OK s_lock, G_lock, tn_lock)) /\
    (!D. (!fuel. ptr_safe_run D 0 fuel ctx func []
                    G_lock tn_lock s_lock) ==>
         !fuel. ptr_safe_run D 0 fuel ctx func []
                    G_reg tn_reg s_reg) /\
    alloca_history func s_lock /\
    return_buf_frame NONE cenv body_sa s_lock /\
    fresh_vars_wrt body_sa s_lock /\ local_ptrs_reserved cenv body_sa /\
    ~block_is_terminated body_sa /\ ~s_lock.vs_halted /\
    s_lock.vs_current_bb = body_sa.cs_current_bb /\
    s_lock.vs_inst_idx = LENGTH body_sa.cs_current_insts /\
    s_lock.vs_gas_readings = s_reg.vs_gas_readings /\
    s_lock.vs_code = s_reg.vs_code /\ s_lock.vs_labels = s_reg.vs_labels /\
    (mut <> View ==> ~cx.txn.is_static) /\
    (!H : (bool # 'a word # type_value) list # num list.
       storage_locks_separated (FST H) (SND H) /\ MEM nkey (SND H) ==>
       stmt_state_rel H ctx func cenv cx es_lock s_lock /\
       ghost_inv H NONE cenv cx es_lock G_lock tn_lock s_lock)
Proof
  strip_tac >>
  drule_all nonreentrant_lock_success_source >> strip_tac >>
  qpat_assum `!H. _`
    (qspec_then `([], [nkey])` strip_assume_tac) >>
  `state_rel ([], [nkey]) func cenv cx es_reg s_reg` by
    fs[stmt_state_rel_def] >>
  `lookup_storage (n2w nkey) (es_reg.tStorage cx.txn.target) =
    tload (n2w nkey) s_reg` by
    (match_mp_tac (Q.INST [`H` |-> `([], [nkey])`]
      (SPEC_ALL nonreentrant_lock_agreement)) >>
     simp[vyperStorageFootprintTheory.storage_locks_separated_def]) >>
  `tload (n2w nkey) s_reg <> 1w` by
    (spose_not_then assume_tac >>
     fs[acquire_nonreentrant_lock_execution]) >>
  `~(mut = View) ==> ~s_reg.vs_call_ctx.cc_static` by
    fs[state_rel_def, call_ctx_rel_def] >>
  `!b. ~((n2w nkey,b) IN tn_reg.t_trans)` by
    (match_mp_tac (Q.INST
       [`H` |-> `([], [nkey])`, `tn` |-> `tn_reg`, `ss` |-> `s_reg`]
       (SPEC_ALL nonreentrant_slot_untainted)) >>
     fs[ghost_inv_def]) >>
  mp_tac (Q.INST [`s` |-> `s_reg`, `sb` |-> `body_sa`,
    `iv` |-> `mut = View`, `G` |-> `G_reg`, `tn` |-> `tn_reg`]
    (SPEC_ALL nonreentrant_lock_paths)) >> simp[] >> strip_tac >>
  `cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
  `local_ptrs_rel func cenv es_reg.scopes s_reg /\ alloca_inv s_reg` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `fresh_vars_wrt body_sa u` by
    (drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
     drule compile_nonreentrant_lock_transient_code >> strip_tac >> gvs[]) >>
  drule compile_nonreentrant_lock_transient_same_block >> strip_tac >>
  drule compile_nonreentrant_lock_transient_counter >> strip_tac >>
  `local_ptrs_reserved cenv body_sa` by
    (match_mp_tac (Q.SPECL [`cenv`, `sa`, `body_sa`]
      local_ptrs_reserved_next_var) >> simp[]) >>
  `?bb rest. lookup_block s_reg.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s_reg.vs_inst_idx bb.bb_instructions =
      transient_lock_code nkey (mut = View) sa ++ rest` by
    (drule_all compile_nonreentrant_lock_transient_prefix >>
     simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode)
    (transient_lock_code nkey (mut = View) sa)` by
    (Cases_on `mut = View` >>
     simp[transient_lock_code_def, mk_inst_def, is_terminator_def]) >>
  `alloca_history func (u with vs_inst_idx := s_reg.vs_inst_idx +
    LENGTH (transient_lock_code nkey (mut = View) sa))` by
    (mp_tac (Q.SPECL [`func`, `bb`, `s_reg`,
       `transient_lock_code nkey (mut = View) sa`, `rest`, `u`]
       alloca_history_run_inst_seq) >> simp[]) >>
  `gas_origin_path T {} ctx func s_reg []
     (OK (u with vs_inst_idx := s_reg.vs_inst_idx +
       LENGTH (transient_lock_code nkey (mut = View) sa))) /\
   gas_path_ptr (ARB:dead) 0 ctx func [] G_reg tn_reg s_reg 0 G' tn'
     (OK (u with vs_inst_idx := s_reg.vs_inst_idx +
       LENGTH (transient_lock_code nkey (mut = View) sa)))` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
       (qspecl_then [`ARB:dead`, `{}`] mp_tac) >>
     strip_tac >> drule gas_origin_ptr_path_projections >> simp[]) >>
  `gas_path ctx func s_reg 0
     (OK (u with vs_inst_idx := s_reg.vs_inst_idx +
       LENGTH (transient_lock_code nkey (mut = View) sa)))` by
    (drule gas_path_ptr_erase >> simp[]) >>
  `gas_path_mem ctx func s_reg 0
     (OK (u with vs_inst_idx := s_reg.vs_inst_idx +
       LENGTH (transient_lock_code nkey (mut = View) sa)))` by
    (drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `!H : (bool # 'a word # type_value) list # num list.
    storage_locks_separated (FST H) (SND H) /\ MEM nkey (SND H) ==>
    stmt_state_rel H ctx func cenv cx es_lock u /\
    ghost_inv H NONE cenv cx es_lock G' tn' u` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`es` |-> `es_reg`, `locked` |-> `es_lock`,
       `s` |-> `s_reg`, `G` |-> `G_reg`, `tn` |-> `tn_reg`,
       `sb` |-> `body_sa`, `iv` |-> `mut = View`]
       (SPEC_ALL nonreentrant_lock_relations)) >> simp[]) >>
  `!H : (bool # 'a word # type_value) list # num list.
    storage_locks_separated (FST H) (SND H) /\ MEM nkey (SND H) ==>
    stmt_state_rel H ctx func cenv cx es_lock
      (u with vs_inst_idx := s_reg.vs_inst_idx +
        LENGTH (transient_lock_code nkey (mut = View) sa)) /\
    ghost_inv H NONE cenv cx es_lock G' tn'
      (u with vs_inst_idx := s_reg.vs_inst_idx +
        LENGTH (transient_lock_code nkey (mut = View) sa))` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx es_lock u /\
      ghost_inv H NONE cenv cx es_lock G' tn' u` by simp[] >>
     fs[stmt_state_rel_inst_idx, ghost_inv_cx_dead,
        ghost_inv_at_inst_idx]) >>
  `fresh_vars_wrt body_sa (u with vs_inst_idx := s_reg.vs_inst_idx +
    LENGTH (transient_lock_code nkey (mut = View) sa))` by
    fs[fresh_vars_wrt_def] >>
  `~block_is_terminated body_sa /\ ~u.vs_halted /\
    u.vs_current_bb = body_sa.cs_current_bb /\
    s_reg.vs_inst_idx + LENGTH (transient_lock_code nkey (mut = View) sa) =
      LENGTH body_sa.cs_current_insts /\
    u.vs_gas_readings = s_reg.vs_gas_readings /\
    u.vs_code = s_reg.vs_code /\ u.vs_labels = s_reg.vs_labels` by
    (Cases_on `mut = View` >> Cases_on `sa.cs_current_insts` >>
     gvs[transient_lock_code_execution, transient_lock_checked_state_def,
         update_var_def, tstore_def, block_is_terminated_def,
         transient_lock_code_def, LAST_APPEND, LAST_CONS_cond,
         mk_inst_def, is_terminator_def]) >>
  qexistsl_tac
    [`u with vs_inst_idx := s_reg.vs_inst_idx +
        LENGTH (transient_lock_code nkey (mut = View) sa)`, `G'`, `tn'`] >>
  simp[return_buf_frame_def] >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem nonreentrant_entry_abort_joint:
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = SOME nkey /\ nkey < dimword (:256) /\
  lock_if_nr cx T (is_view_mut mut) es_reg = (INR exc, es_abort) /\
  compile_nonreentrant_lock nkey T (mut = View) sa = ((), body_sa) /\
  fn_has_code sa body_sa func /\
  ~ctx_has_dalloca ctx /\ ~s_reg.vs_halted /\
  s_reg.vs_current_bb = sa.cs_current_bb /\
  s_reg.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H : (bool # 'a word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es_reg s_reg /\
       ghost_inv H NONE cenv cx es_reg G_reg tn_reg s_reg) ==>
  ?a s_abort G_abort tn_abort.
    gas_path ctx func s_reg 0 (Abort a s_abort) /\
    gas_path_mem ctx func s_reg 0 (Abort a s_abort) /\
    (!D explicit.
       gas_origin_ptr_path (D, 0, explicit, ctx, func, [])
         (s_reg, G_reg, tn_reg) [] (Abort a s_abort, G_abort, tn_abort)) /\
    expr_exit (INR exc : unit + exception) (Abort a s_abort) /\
    ((tload (n2w nkey) s_reg = 1w /\ a = Revert_abort /\
      exc = Error (RuntimeError "nonreentrant lock")) \/
     (tload (n2w nkey) s_reg <> 1w /\ mut <> View /\ cx.txn.is_static /\
      a = ExHalt_abort /\
      exc = Error (RuntimeError "write in static context"))) /\
    s_abort.vs_gas_readings = s_reg.vs_gas_readings /\
    s_abort.vs_memory = s_reg.vs_memory /\
    s_abort.vs_allocas = s_reg.vs_allocas /\
    s_abort.vs_alloca_next = s_reg.vs_alloca_next /\
    s_abort.vs_code = s_reg.vs_code /\ s_abort.vs_labels = s_reg.vs_labels
Proof
  strip_tac >>
  `is_view_mut mut = (mut = View)` by
    (drule function_header_nonreentrant_view >> simp[is_view_mut_def]) >>
  qpat_assum `!H. _`
    (qspec_then `([], [nkey])` strip_assume_tac) >>
  `state_rel ([], [nkey]) func cenv cx es_reg s_reg` by
    fs[stmt_state_rel_def] >>
  `lookup_storage (n2w nkey) (es_reg.tStorage cx.txn.target) =
    tload (n2w nkey) s_reg` by
    (match_mp_tac (Q.INST [`H` |-> `([], [nkey])`]
      (SPEC_ALL nonreentrant_lock_agreement)) >>
     simp[vyperStorageFootprintTheory.storage_locks_separated_def]) >>
  `cx.txn.is_static = s_reg.vs_call_ctx.cc_static` by
    fs[state_rel_def, call_ctx_rel_def] >>
  `(tload (n2w nkey) s_reg = 1w /\
      exc = Error (RuntimeError "nonreentrant lock")) \/
   (tload (n2w nkey) s_reg <> 1w /\ mut <> View /\ cx.txn.is_static /\
      exc = Error (RuntimeError "write in static context"))` by
    (Cases_on `tload (n2w nkey) s_reg = 1w` >>
     Cases_on `mut = View` >> Cases_on `cx.txn.is_static` >>
     gvs[lock_if_nr_def, acquire_nonreentrant_lock_execution,
         check_not_static_def, vyperStateTheory.check_def,
         vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
         vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def]) >>
  `?a t. run_inst_seq (transient_lock_code nkey (mut = View) sa) s_reg =
       Abort a t /\
     ((tload (n2w nkey) s_reg = 1w /\ a = Revert_abort /\
       exc = Error (RuntimeError "nonreentrant lock")) \/
      (tload (n2w nkey) s_reg <> 1w /\ mut <> View /\ cx.txn.is_static /\
       a = ExHalt_abort /\
       exc = Error (RuntimeError "write in static context")))` by
    (Cases_on `tload (n2w nkey) s_reg = 1w` >>
     fs[] >> simp[transient_lock_code_execution]) >>
  `t.vs_gas_readings = s_reg.vs_gas_readings /\
   t.vs_memory = s_reg.vs_memory /\ t.vs_allocas = s_reg.vs_allocas /\
   t.vs_alloca_next = s_reg.vs_alloca_next /\
   t.vs_code = s_reg.vs_code /\ t.vs_labels = s_reg.vs_labels` by
    (Cases_on `tload (n2w nkey) s_reg = 1w` >>
     gvs[transient_lock_code_execution, transient_lock_checked_state_def,
         revert_state_def, halt_state_def, set_returndata_def, update_var_def]) >>
  `key_taint tn_reg.t_trans (n2w nkey) = {}` by
    (`!b. ~((n2w nkey,b) IN tn_reg.t_trans)` by
      (match_mp_tac (Q.INST
        [`H` |-> `([], [nkey])`, `tn` |-> `tn_reg`, `ss` |-> `s_reg`]
        (SPEC_ALL nonreentrant_slot_untainted)) >> fs[ghost_inv_def]) >>
     simp[key_taint_def, EXTENSION]) >>
  mp_tac (Q.INST [`D` |-> `ARB:dead`, `PG` |-> `[]`,
    `ss` |-> `s_reg`, `st` |-> `sa`, `iv` |-> `mut = View`,
    `G` |-> `G_reg`, `tn` |-> `tn_reg`]
    (SPEC_ALL transient_lock_abort_ptr_ghost)) >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choose_then `G'` (qx_choose_then `tn'` assume_tac)) >>
  `!D. inst_seq_ptr D 0 ctx func [] G_reg tn_reg
    (transient_lock_code nkey (mut = View) sa) s_reg G' tn'` by
    (gen_tac >>
     mp_tac (Q.INST [`PG` |-> `[]`, `ss` |-> `s_reg`, `st` |-> `sa`,
       `iv` |-> `mut = View`, `G` |-> `G_reg`, `tn` |-> `tn_reg`]
       (SPEC_ALL transient_lock_abort_ptr_ghost)) >>
     (impl_tac >- fs[]) >>
     disch_then (qx_choose_then `G_D` (qx_choose_then `tn_D` assume_tac)) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `?bb. lookup_block s_reg.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code nkey (mut = View) sa)
      (DROP s_reg.vs_inst_idx bb.bb_instructions)` by
    metis_tac[compile_nonreentrant_lock_transient_prefix] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode)
    (transient_lock_code nkey (mut = View) sa)` by
    (Cases_on `mut = View` >>
     simp[transient_lock_code_def, mk_inst_def, is_terminator_def]) >>
  `run_inst_seq_mem_ok (transient_lock_code nkey (mut = View) sa) s_reg` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `mut = View` >>
     simp[transient_lock_code_def, mk_inst_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  mp_tac (Q.INST [`D` |-> `ARB:dead`, `lo` |-> `0`,
    `explicit` |-> `{}`, `PG` |-> `[]`]
    (Q.SPECL [`transient_lock_code nkey (mut = View) sa`, `s_reg`, `t`,
       `a`, `G_reg`, `tn_reg`, `G'`, `tn'`, `ctx`, `func`, `bb`]
       sha_zero_origin_abort)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `j` assume_tac) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,func,[])
    (s_reg,G_reg,tn_reg) [] (Abort a (t with vs_inst_idx := j),G',tn')` by
    (rpt gen_tac >>
     mp_tac (Q.INST [`lo` |-> `0`, `PG` |-> `[]`]
       (Q.SPECL [`transient_lock_code nkey (mut = View) sa`, `s_reg`, `t`,
         `a`, `G_reg`, `tn_reg`, `G'`, `tn'`, `ctx`, `func`, `bb`]
         sha_zero_origin_abort)) >> simp[] >>
     disch_then (qx_choose_then `k` assume_tac) >>
     `(t with vs_inst_idx := k) = (t with vs_inst_idx := j)` by
       (irule sha_origin_abort_endpoint_unique >>
        goal_assum (drule_at Any) >> metis_tac[]) >>
     metis_tac[]) >>
  `gas_origin_path T {} ctx func s_reg [] (Abort a (t with vs_inst_idx := j)) /\
   gas_path_ptr (ARB:dead) 0 ctx func [] G_reg tn_reg s_reg 0 G' tn'
     (Abort a (t with vs_inst_idx := j))` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
       (qspecl_then [`ARB:dead`, `{}`] mp_tac) >>
     strip_tac >> drule gas_origin_ptr_path_projections >> simp[]) >>
  `gas_path ctx func s_reg 0 (Abort a (t with vs_inst_idx := j))` by
    (drule gas_path_ptr_erase >> simp[]) >>
  `gas_path_mem ctx func s_reg 0 (Abort a (t with vs_inst_idx := j))` by
    (drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  qexistsl_tac [`a`, `t with vs_inst_idx := j`, `G'`, `tn'`] >>
  simp[] >> fs[exprSimDefsTheory.expr_exit_def]
QED
