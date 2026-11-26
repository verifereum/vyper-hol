(* Stop at the input of the emitted final store, before modifying the local. *)
Theory bodyAssignNameCopyStoreInputMods
Ancestors
  bodyLocalSnapshotPhysicalMods bodyLocalSnapshotResourcesMods bodyFullPathHistory
  bodyFullShared annassignRelayoutCode stmtLowering stateRelProj memoryValueTyping
  fragGasOriginPtr fragExec bodyMemoryDefs abiBuiltinAllocation exprLoweringProps
  exprSimProps bodyPtrDefs stmtSimDefs bodyFullHashKeccakFixed freshWrites words
  finite_map ptrDiscipline venomState loweringStateRelDefs loweringPosts
  venomInst venomMemDefs typedMemoryCopy assignTuplePtrCopyLen bodySimFull

Theorem assign_name_copy_store_input_mods:
  compile_assign_value ce (Var p) LocMemory (Var xs) F loc ty sty bytes sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list) ctx func ce cx mid u /\
  alloca_history func u /\ ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  local_ptrs_reserved ce sm /\
  (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  not_fresh_at sm xs /\ lookup_var xs u = SOME sw /\
  type_memory_bytes ce sty = type_memory_size rt /\ value_has_type rt v /\
  ptr_covers Gi ti xs u (type_memory_size rt) /\
  (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
  w2n sw + val_store_size rt v <= u.vs_alloca_next /\
  (loc = SOME LocMemory ==> w2n sw + type_memory_size rt <= u.vs_alloca_next) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  not_fresh_at sm p /\ lookup_var p u = SOME dw /\ ptr_covers Gi ti p u cap /\
  local_region ce mid.scopes u id (w2n dw) cap /\
  lo <= w2n dw /\ w2n dw + cap <= u.vs_alloca_next ==>
  ?sc z Gz tz ys wy.
    compile_store_memory ce (Var ys) (Var p) ty sty sc = ((),sb) /\
    fn_has_code sc sb func /\ sm.cs_next_var <= sc.cs_next_var /\
    sm.cs_next_id <= sc.cs_next_id /\ sc.cs_next_var <= sb.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gi,ti) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    local_ptrs_reserved ce sc /\
    (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x) /\
    (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x) /\
    not_fresh_at sc ys /\ lookup_var ys z = SOME wy /\
    ptr_covers Gz tz ys z (type_memory_size rt) /\
    (!m. mem_agree_outside tz.t_mem z.vs_memory m ==> val_in_memory rt v (w2n wy) m) /\
    w2n wy + val_store_size rt v <= z.vs_alloca_next /\
    not_fresh_at sc p /\ lookup_var p z = SOME dw /\ ptr_covers Gz tz p z cap /\
    local_region ce mid.scopes z id (w2n dw) cap /\
    lo <= w2n dw /\ w2n dw + cap <= z.vs_alloca_next /\
    z.vs_alloca_next < dimword (:256) /\
    allocas_from lo z /\ lo <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func ce cx mid u ==> stmt_state_rel H ctx func ce cx mid z) /\
    (immutable_frame_mods func ce cx mid u ==> immutable_frame_mods func ce cx mid z) /\
    (!D d. ghost_inv_at_mods D lo d ce cx mid Gi ti u ==> ghost_inv_at_mods D lo d ce cx mid Gz tz z) /\
    (!d. return_buf_frame d ce sm u ==> return_buf_frame d ce sc z) /\
    (!d. return_buf_frame d ce sm u /\ return_buf_sep d ce mid u ==> return_buf_sep d ce mid z) /\
    (!floor. allocas_from floor u /\ floor <= u.vs_alloca_next ==> allocas_from floor z) /\
    u.vs_alloca_next <= z.vs_alloca_next /\
    (!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> FLOOKUP z.vs_allocas aid = SOME ent) /\
    (!aid a len. FLOOKUP z.vs_allocas aid = SOME (a,len) ==>
      FLOOKUP u.vs_allocas aid = SOME (a,len) \/ u.vs_alloca_next <= a) /\
    (!x. not_fresh_at sm x ==> not_fresh_at sc x /\ lookup_var x z = lookup_var x u) /\
    (!name a len. local_region ce mid.scopes z name a len <=> local_region ce mid.scopes u name a len) /\
    ghost_kept_at lo ce mid sm Gi ti u Gz tz /\ alloca_frame ce mid sm u ce mid z /\
    tz.t_stor = ti.t_stor /\ tz.t_trans = ti.t_trans /\ tz.t_imm = ti.t_imm /\
    (!i. loc <> SOME LocMemory \/ ~(w2n wy <= i /\ i < w2n wy + type_memory_size rt) ==>
      (i IN tz.t_mem <=> i IN ti.t_mem)) /\
    mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo u.vs_memory /\
    (!i. i < lo ==> (i IN tz.t_mem <=> i IN ti.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `u.vs_alloca_next < dimword (:256)` by
    (drule_then (irule o MATCH_MP (SPEC_ALL alloca_room_next_lt)) stmt_state_rel_alloca_room) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "stage" >>
  `compile_store_memory ce (Var xs) (Var p) ty sty sm = ((),sb)` by
    fs[compile_assign_value_def] >>
  `sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND] >>
  qexistsl_tac [`sm`,`u`,`Gi`,`ti`,`xs`,`sw`] >>
  simp[gas_origin_ptr_path_rules,ghost_kept_at_def,alloca_frame_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Resume assign_name_copy_store_input_mods[stage]:
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all_then (qx_choosel_then [`buf`,`sa`,`sc`] (map_every assume_tac o CONJUNCTS))
    assign_memory_relayout_code >>
  `val_wf rt v` by metis_tac[value_has_type_val_wf] >>
  qpat_x_assum `SOME LocMemory = SOME LocMemory ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `ptr_covers Gi ti xs u (type_memory_bytes ce sty)` by simp[] >>
  `w2n sw + type_memory_bytes ce sty <= u.vs_alloca_next` by simp[] >>
  `type_memory_bytes ce sty < dimword (:256)` by decide_tac >>
  `w2n sw + type_memory_bytes ce sty < dimword (:256)` by decide_tac >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) local_snapshot_physical_mods >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (simp[] >> NO_TAC)])) >>
  disch_then (qx_choosel_then [`z`,`ys`,`b`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  `w2n (n2w b : 256 word) = b` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gi x /\ op_taint tz (Var x) = op_taint ti (Var x)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "resources"
QED

Resume assign_name_copy_store_input_mods[resources]:
  `!name a len. local_region ce mid.scopes u name a len ==>
      loweringStateRelDefs$regions_disjoint b (type_memory_bytes ce sty) a len` by
    (gen_tac >> gen_tac >> gen_tac >> strip_tac >>
     qpat_assum `!n a l. local_region _ _ z n a l ==> _`
       (qspecl_then [`name`,`a`,`len`] mp_tac) >> simp[]) >>
  drule local_snapshot_resources_mods >>
  disch_then (drule_at (Pat `MEM _ _`)) >>
  disch_then (drule_at (Pat `typed_copy_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `_.t_stor = _.t_stor`)) >>
  disch_then (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`Gz`,`Gi`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (simp[venomInstTheory.mk_inst_def] >> NO_TAC)])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "transfers"
QED

Resume assign_name_copy_store_input_mods[transfers]:
  `sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
   sc.cs_next_var <= sb.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `alloca_history func z` by suspend "history" >>
  `z.vs_alloca_next < dimword (:256)` by
    (`stmt_state_rel H0 ctx func ce cx mid z` by
       (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     drule_then (irule o MATCH_MP (SPEC_ALL alloca_room_next_lt)) stmt_state_rel_alloca_room) >>
  `ptr_covers Gz tz p z cap` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Gi`,`u`,`ti`] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `b + val_store_size rt v <= z.vs_alloca_next` by
    (drule val_store_size_le >> simp[] >> decide_tac) >>
  `!floor. allocas_from floor u /\ floor <= u.vs_alloca_next ==> allocas_from floor z` by
    (simp[allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid a len. FLOOKUP z.vs_allocas aid = SOME (a,len) ==> _`
       (drule_then (DISJ_CASES_THEN assume_tac))
     >- (qpat_assum `!aid a len. FLOOKUP u.vs_allocas aid = SOME (a,len) ==> _`
           (drule_then ACCEPT_TAC)) >> decide_tac) >>
  `!d. return_buf_frame d ce sm u ==> return_buf_frame d ce sc z` by
    (rpt strip_tac >> irule return_buf_frame_frame >> qexistsl_tac [`ce`,`u`,`sm`] >>
     simp[]) >>
  `!d. return_buf_frame d ce sm u /\ return_buf_sep d ce mid u ==> return_buf_sep d ce mid z` by
    suspend "return_sep" >>
  `ghost_kept_at lo ce mid sm Gi ti u Gz tz` by suspend "kept" >>
  qexistsl_tac [`sc`,`z`,`Gz`,`tz`,`ys`,`n2w b`] >> suspend "assemble"
QED

Resume assign_name_copy_store_input_mods[history]:
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o SPEC_ALL) >>
  drule body_full_path_alloca_history >> simp[]
QED

Resume assign_name_copy_store_input_mods[return_sep]:
  Cases >> simp[return_buf_frame_def,return_buf_sep_def] >>
  rename1 `return_buf_frame (SOME a) _ _ _` >> Cases_on `a` >>
  simp[return_buf_frame_def,return_buf_sep_def] >> rpt strip_tac
  >- (qpat_assum `!floor. _ ==> allocas_from floor z` irule >> simp[]) >>
  qpat_assum `!n b sz. local_region _ _ u n b sz ==> _` (drule_then ACCEPT_TAC)
QED

Resume assign_name_copy_store_input_mods[kept]:
  simp[ghost_kept_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!aid off len i. FLOOKUP u.vs_allocas aid = SOME (off,len) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!n a l. local_region _ _ u n a l ==> _`
    (drule_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  disch_tac >>
  `~(b <= i /\ i < b + type_memory_bytes ce sty)` by decide_tac >>
  qpat_assum `!i. ~(b <= i /\ _) ==> _` (drule_then (irule o iffLR)) >> simp[]
QED

Resume assign_name_copy_store_input_mods[assemble]:
  conj_tac
  >- (qpat_assum `buf.buf_operand = Var ys` (pure_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC) >>
  `ptr_covers Gz tz ys z (type_memory_size rt)` by
    (qpat_assum `type_memory_bytes ce sty = type_memory_size rt`
       (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `lookup_var p z = SOME dw` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `w2n dw + cap <= z.vs_alloca_next` by decide_tac >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (simp[] >> NO_TAC)]
QED

Finalise assign_name_copy_store_input_mods
