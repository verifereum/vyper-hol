(* Install a local byte/string assignment using the rounded live extent. *)
Theory bodyAssignLocalBytesInstallAtPathMods
Ancestors
  bodyAssignLocalStoreCutsMods bodyLocalBytesCopyPathMods bodyLocalCopyWritesMods
  bodyFullPathHistory placeMemoryStateRebuild tuplePlaceStep
  valueCopyBytes exprOpenCopies exprLoweringProps freshWrites fragGasOriginPtr
  words stateRelProj typedMemoryCopy bodyAssignLocalPreStoreMods
  stmtSimDeclMem bytesCopyCode valueEncodingTyping bodyLocalSnapshotPhysicalMods
  bodyLocalSnapshotResourcesMods annassignRelayoutCode wordArgsPtr bodyMemoryDefs
  vyperStorageFootprint vyperState bodyFullHashKeccakFixed loweringPosts venomState
  reasonCopySourcePtr stmtSimDefs bodyPtrDefs allocaHistory fragExec loweringStateRelDefs
  venomInst ptrDiscipline valueEncoding exprSimProps vyperTyping

Theorem local_bytes_install_suffix[local]:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sm = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME ptv /\
  value_has_type stv v /\ value_has_type ptv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n sw) m) /\
  not_fresh_at sm xs /\ not_fresh_at sm xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  w2n dw = w2n w + k /\ k + n <= cap /\ lo <= w2n dw /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~block_is_terminated sb /\ alloca_history func s /\ ee.gas_obs = [] /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  lookup_scopes id ee.scopes = SOME entry /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME w /\
  local_region cenv ee.scopes s id (w2n w) cap /\ local_ptrs_reserved cenv sm /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  return_buf_frame d cenv sm s /\ return_buf_sep d cenv ee s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x s = SOME u) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP s.vs_allocas aid = SOME a) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_frame cenv es sa s0 cenv ee s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) ==>
  ?f Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf)) /\
    !H. valid_horizon cx st0 H ff.storage_trace ==>
        local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
          (ff with gas_obs := []) f Gf tf s0 sa es G0 tn0 (INL ())
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by simp[] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `~is_word_type dty` by simp[is_bytestring_word_type] >>
  drule_all local_bytes_copy_path_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`f`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  `sm.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`cenv`,`Var xs`,`Var xd`,`dty`,`sty`,`sm`] mp_tac
       ci_mono_compile_store_memory >> simp[ci_mono_def]) >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func f` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule body_full_path_alloca_history >> simp[]) >>
  qexistsl_tac [`f`,`Gf`,`tf`] >> conj_tac >- first_assum ACCEPT_TAC >>
  `ff.storage_trace = ee.storage_trace` by metis_tac[write_place_storage_trace] >>
  `ff with gas_obs := [] = ff` by
    (drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = ee with scopes := _` (once_rewrite_tac o single) >>
     simp[evaluation_state_component_equality]) >>
  simp[local_assign_normal_at_cut_mods] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  suspend "install"
QED

Resume local_bytes_install_suffix[install]:
  `!x. not_fresh_at sm x ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `typed_copy_state_frame sm (w2n w+k) n s f` by metis_tac[] >>
  drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [alpha |-> ``:256``] bodyAssignLocalInstallModsTheory.assign_local_install_post_mods) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`tf`,`sb`,`lctx`,`func`,`ctx`,`H`,`Gf`] mp_tac) >>
  qpat_assum `w2n dw = w2n w + k` (once_rewrite_tac o single o SYM) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL local_copy_immutable_frame_mods))])) >>
  disch_then (qx_choose_then `ce` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Finalise local_bytes_install_suffix[local]

Theorem local_bytes_positive[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  0 < type_memory_size tv
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem local_bytes_root_reserved[local]:
  local_ptrs_reserved cenv cur /\ FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) ==>
  not_fresh_at cur p
Proof
  simp[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem local_bytes_len_size[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) ==>
  val_store_size tv v = 32 + 32 * word_size len
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bytestring_type_value >> strip_tac >>
  qpat_x_assum `(?bs. v = BytesV bs /\ _ ) \/ _` strip_assume_tac >>
  gvs[value_has_type_def,val_store_size_def]
QED

Theorem local_bytes_extent[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * word_size len
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, val_store_size_def]
QED

Theorem assign_local_bytes_install_at_path_mods:
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,k,ptv,dw)
    ee cur s G tn /\
  local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw)
    (op,sw) sa ee cur s G tn /\
  compile_assign_value cenv (FST dst) LocMemory op F (vv_location vv) dty
    (lowered_value_type cenv e) (type_memory_bytes cenv dty) cur = ((),sb) /\
  is_bytestring_type dty /\ fn_has_code cur sb func /\ fn_inst_ids_distinct func /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?f Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf) /\
    local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
      (ff with gas_obs := []) f Gf tf s0 sa es G0 tn0 (INL ())
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type dty` by simp[is_bytestring_word_type] >>
  qhdtm_x_assum `local_assign_here_mods`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  qpat_assum `~is_word_type dty` (fn th =>
    qhdtm_x_assum `local_assign_store_source_mods`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [local_assign_store_source_mods_def,LET_THM,th])) >>
  qabbrev_tac `sty = lowered_value_type cenv e` >>
  `is_bytestring_type sty` by (drule_all_then ACCEPT_TAC typed_copy_bytestring_source) >>
  `0 < type_memory_size ptv /\ 0 < type_memory_size stv` by
    (conj_tac
     >- (irule local_bytes_positive >> qexistsl_tac [`get_tenv cx`,`dty`] >> simp[]) >>
     irule local_bytes_positive >> qexistsl_tac [`get_tenv cx`,`sty`] >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x`
    by fs[ret_pc_ok_def] >>
  `~block_is_terminated sb` by
    (irule compile_assign_value_memory_widen_open >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  qpat_assum `0 < type_memory_size ptv ==> _`
    (drule_then (qx_choose_then `xd` (map_every assume_tac o CONJUNCTS))) >>
  `lookup_var xd s = SOME dw` by fs[eval_operand_def] >>
  Cases_on `vv_location vv = SOME LocMemory`
  >- suspend "stage" >>
  suspend "direct"
QED

Resume assign_local_bytes_install_at_path_mods[direct]:
  qpat_x_assum `if _ then _ else n = _`
    (mp_tac) >> simp[] >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  `0 < n` by simp[] >>
  qpat_assum `0 < n ==> _` (drule_then
    (CONJUNCTS_THEN2 (qx_choose_then `xs` (map_every assume_tac o CONJUNCTS))
      (map_every assume_tac o CONJUNCTS))) >>
  `n = 32 + 32 * word_size len` by decide_tac >>
  `lookup_var xs s = SOME sw` by fs[eval_operand_def] >>
  `compile_store_memory cenv (Var xs) (Var xd) dty sty cur = ((),sb)` by
    fs[stmtLoweringTheory.compile_assign_value_def] >>
  `n <= type_memory_size ptv` by suspend "live_bound" >>
  `ptr_covers G tn xd s n` by
    (irule ptr_covers_mono >> qexists_tac `type_memory_size ptv` >> simp[]) >>
  `k+n <= cap /\ w2n dw+n <= s.vs_alloca_next /\ n < dimword (:256)` by decide_tac >>
  suspend "run_direct"
QED

Resume assign_local_bytes_install_at_path_mods[live_bound]:
  `val_store_size ptv v <= type_memory_size ptv` by simp[val_store_size_le] >>
  `val_store_size ptv v = n` suffices_by (strip_tac >> decide_tac) >>
  qpat_assum `n = 32 + 32 * word_size len` (pure_once_rewrite_tac o single) >>
  irule local_bytes_len_size >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`get_tenv cx`,`dty`] >> simp[]
QED

Resume assign_local_bytes_install_at_path_mods[run_direct]:
  `?f Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf)) /\
     !H. valid_horizon cx st0 H ff.storage_trace ==>
       local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
         (ff with gas_obs := []) f Gf tf s0 sa es G0 tn0 (INL ())` suffices_by
    (disch_then (qx_choosel_then [`f`,`Gf`,`tf`] strip_assume_tac) >>
     qexistsl_tac [`f`,`Gf`,`tf`] >> simp[]) >>
  irule local_bytes_install_suffix >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = SOME stv`)) >>
  goal_assum (drule_at (Pat `ptr_covers G tn xd s _`)) >>
  qexistsl_tac [`dw`,`len`,`sw`,`b`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Resume assign_local_bytes_install_at_path_mods[stage]:
  `n = type_memory_size stv` by
    (qpat_x_assum `if _ then _ else n = _` mp_tac >> simp[]) >>
  `0 < n` by simp[] >>
  qpat_assum `0 < n ==> _` (drule_then
    (CONJUNCTS_THEN2 (qx_choose_then `xs` (map_every assume_tac o CONJUNCTS))
      (map_every assume_tac o CONJUNCTS))) >>
  `lookup_var xs s = SOME sw` by fs[eval_operand_def] >>
  `compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory)
     dty sty (type_memory_bytes cenv dty) cur = ((),sb)` by fs[] >>
  drule_all_then (qx_choosel_then [`buf`,`alloc`,`store`] (map_every assume_tac o CONJUNCTS))
    assign_memory_relayout_code >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by simp[] >>
  qpat_x_assum `n = type_memory_size stv` SUBST_ALL_TAC >>
  `ptr_covers G tn xs s (type_memory_bytes cenv sty)` by simp[] >>
  `w2n sw + type_memory_bytes cenv sty <= s.vs_alloca_next /\
   w2n sw + type_memory_bytes cenv sty < dimword (:256)` by fs[] >>
  `type_memory_bytes cenv sty < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `w2n sw + type_memory_bytes cenv sty` >> simp[]) >>
  `type_memory_size stv = type_memory_bytes cenv sty` by simp[] >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) local_snapshot_physical_mods >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `type_memory_size _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`v`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj2_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choosel_then [`u`,`ys`,`q`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `type_memory_size stv = type_memory_bytes cenv sty` kall_tac >>
  `!x. not_fresh_at cur x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!name a len. local_region cenv ee.scopes s name a len ==>
      loweringStateRelDefs$regions_disjoint q (type_memory_bytes cenv sty) a len` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name a len. local_region _ _ u name a len ==> _`
       (qspecl_then [`name`,`a`,`len`] mp_tac) >> simp[]) >>
  suspend "stage_resources"
QED

Resume assign_local_bytes_install_at_path_mods[stage_resources]:
  drule local_snapshot_resources_mods >>
  disch_then (drule_at (Pat `MEM _ _`)) >>
  disch_then (drule_at (Pat `typed_copy_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `_.t_stor = _.t_stor`)) >>
  disch_then (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`Gu`,`G`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (pure_rewrite_tac[venomInstTheory.mk_inst_def] >> simp[] >> NO_TAC)])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cur.cs_next_var <= store.cs_next_var /\ cur.cs_next_id <= store.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at cur x ==> not_fresh_at store x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `cur` >> simp[]) >>
  `not_fresh_at cur p` by
    (irule local_bytes_root_reserved >> qexistsl_tac [`cap`,`cenv`,`id`] >> simp[]) >>
  `local_ptrs_reserved cenv store` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cur` >> simp[]) >>
  `lookup_var xd u = SOME dw /\ lookup_var p u = SOME b` by simp[] >>
  `local_region cenv ee.scopes u id (w2n b) cap` by simp[] >>
  `alloca_history func u` by
    (`alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o SPEC_ALL) >>
     drule body_full_path_alloca_history >> simp[]) >>
  `ptr_covers Gu tu xd u (type_memory_size ptv)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `w2n (n2w q : 256 word) = q` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `compile_store_memory cenv (Var ys) (Var xd) dty sty store = ((),sb)` by fs[] >>
  suspend "stage_return"
QED

Resume assign_local_bytes_install_at_path_mods[stage_return]:
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at store x`
    by (rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at store x` irule >>
        first_assum (drule_then ACCEPT_TAC)) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at store x`
    by (rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at store x` irule >>
        first_assum (drule_then ACCEPT_TAC)) >>
  `return_buf_frame d cenv store u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`cur`] >> simp[]) >>
  `!floor. allocas_from floor s /\ floor <= s.vs_alloca_next ==> allocas_from floor u` by
    (simp[allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid a len. FLOOKUP u.vs_allocas aid = SOME (a,len) ==> _`
       (drule_then (DISJ_CASES_THEN assume_tac))
     >- (qpat_assum `!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) ==> _`
           (drule_then ACCEPT_TAC)) >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> simp[]) >>
  `return_buf_sep d cenv ee u` by suspend "return_sep" >>
  suspend "stage_live"
QED

Resume assign_local_bytes_install_at_path_mods[return_sep]:
  irule bodyFullSharedTheory.return_buf_sep_transport >> reverse conj_tac
  >- (qexistsl_tac [`cenv`,`ee`,`s`] >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!floor. allocas_from floor s /\ _ ==> allocas_from floor u` irule >>
  fs[return_buf_frame_def,bodySimFullTheory.return_buf_sep_def]
QED

Resume assign_local_bytes_install_at_path_mods[stage_live]:
  drule_at (Pat `evaluate_type _ sty = SOME stv`) local_bytes_extent >>
  disch_then (drule_at (Pat `value_has_type stv v`)) >>
  disch_then (drule_at (Pat `is_bytestring_type sty`)) >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `live = 32 + 32 * word_size len` >>
  `live <= type_memory_bytes cenv sty` by metis_tac[val_store_size_le] >>
  `live <= type_memory_size ptv` by
    (`val_store_size ptv v = live` suffices_by metis_tac[val_store_size_le] >>
     qpat_assum `Abbrev (live = _)` (pure_once_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule local_bytes_len_size >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`get_tenv cx`,`dty`] >> simp[]) >>
  `ptr_covers Gu tu ys u live` by
    (irule ptr_covers_mono >> qexists_tac `type_memory_bytes cenv sty` >> simp[]) >>
  `ptr_covers Gu tu xd u live` by
    (irule ptr_covers_mono >> qexists_tac `type_memory_size ptv` >> simp[]) >>
  `live < dimword (:256) /\ q + live <= u.vs_alloca_next /\
   w2n dw + live <= u.vs_alloca_next /\ k + live <= cap` by
    (qpat_assum `live <= type_memory_bytes cenv sty` mp_tac >>
     qpat_assum `live <= type_memory_size ptv` mp_tac >>
     qpat_assum `q + type_memory_bytes cenv sty < dimword (:256)` mp_tac >>
     qpat_assum `q + type_memory_bytes cenv sty <= u.vs_alloca_next` mp_tac >>
     qpat_assum `w2n dw = w2n b + k` mp_tac >>
     qpat_assum `k + type_memory_size ptv <= cap` mp_tac >>
     qpat_assum `w2n b + cap <= s.vs_alloca_next` mp_tac >>
     qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  suspend "run_staged"
QED

Resume assign_local_bytes_install_at_path_mods[run_staged]:
  `not_fresh_at store xd` by simp[] >>
  `ghost_kept_at lo cenv ee store Gu tu u Gu tu` by simp[ghost_kept_at_refl] >>
  `alloca_frame cenv ee store u cenv ee u` by simp[alloca_frame_same] >>
  `!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory stv v (w2n (n2w q : 256 word)) m`
    by simp[] >>
  `?f Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK f,Gf,tf)) /\
     !H. valid_horizon cx st0 H ff.storage_trace ==>
       local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
         (ff with gas_obs := []) f Gf tf u store ee Gu tu (INL ())` suffices_by
    (disch_then (qx_choosel_then [`f`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
     qexistsl_tac [`f`,`Gf`,`tf`] >> gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] _`
           (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
         simp[] >> disch_then irule >> simp[]) >>
     suspend "lift_normal") >>
  irule local_bytes_install_suffix >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE (simp[] >> NO_TAC))) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = SOME stv`)) >>
  goal_assum (drule_at (Pat `ptr_covers Gu tu xd u live`)) >>
  qexistsl_tac [`dw`,`len`,`n2w q`,`b`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (simp[Abbr `live`] >> NO_TAC),
    gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt conj_tac >> simp[]]
QED

Resume assign_local_bytes_install_at_path_mods[lift_normal]:
  `ff with gas_obs := [] = ff` by
    (drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = ee with scopes := _` (once_rewrite_tac o single) >>
     simp[evaluation_state_component_equality]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> local_assign_normal_mods _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ _ _ _ _ (INL ())`
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [local_assign_normal_at_cut_mods])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at cur x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at store x` by simp[] >>
  `sa.cs_next_id <= store.cs_next_id` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `cur.cs_next_id` >> simp[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a` by simp[] >>
  `alloca_frame cenv es sa s0 cenv ee u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`s`,`cur`] >> simp[]) >>
  simp[local_assign_normal_at_cut_mods] >>
  conj_tac
  >- first_assum (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  conj_tac
  >- (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`u`,`store`] >> simp[]) >>
  suspend "lift_taint"
QED

Resume assign_local_bytes_install_at_path_mods[lift_taint]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ FLOOKUP u.vs_allocas aid = SOME (off,sz)` by simp[] >>
  `aid < cur.cs_next_id /\ aid < store.cs_next_id` by
    (rpt conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  `!n b len. local_region cenv ee.scopes s n b len ==> off + sz <= b \/ b + len <= off` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv ee s`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `!n b len. local_region cenv ee.scopes u n b len ==> off + sz <= b \/ b + len <= off` by
    (map_every qx_gen_tac [`nm`,`addr`,`width`] >> disch_tac >>
     `local_region cenv ee.scopes s nm addr width` by
       (qpat_assum `!n a len. local_region _ _ u n a len <=> local_region _ _ s n a len`
          (qspecl_then [`nm`,`addr`,`width`] (irule o iffLR)) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!n b len. local_region cenv ee.scopes s n b len ==> off + sz <= b \/ b + len <= off`
       (qspecl_then [`nm`,`addr`,`width`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `i IN tu.t_mem` by
    (qpat_assum `!aid off len i. FLOOKUP u.vs_allocas aid = SOME (off,len) /\ _ ==> i IN tu.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `i IN tn.t_mem` by
    (qpat_assum `!aid off len i. FLOOKUP s.vs_allocas aid = SOME (off,len) /\ _ ==> i IN tn.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
    (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Finalise assign_local_bytes_install_at_path_mods
