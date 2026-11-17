(* Direct memory destination; the source has already been unwrapped. *)
Theory localMemoryStoreRunProbe
Ancestors
  localMemoryStoreGhostProbe localMemoryStoreStateProbe placeMemoryEntryUpdate
  bodyFullMemoryStore typedMemoryCopy bodyPtrDefs fragGasOriginPtr
  loweringPosts exprLoweringProps compileEnv stmtLowering
  loweringStateRelDefs context vyperState venomState valueEncoding
  stmtSimDefs ptrDiscipline vyperTypeSystem list words arithmetic

Theorem direct_memory_subpath_store_effect:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F NONE ty ty
    bytes sa = ((),sb) /\ ~is_word_type ty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size tv <= w2n sw) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel (H0:(bool # 'a word # type_value) list # num list)
    ctx func cenv cx es s /\
  ghost_inv_at D0 lo d0 cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  write_place cx (MemoryPlace id path) v es = (INL (),ff) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME bw /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  w2n dw = w2n bw+k /\ lo <= w2n dw /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!(H:(bool # 'a word # type_value) list # num list) D d.
      stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s ==>
      stmt_state_rel H ctx func cenv cx ff t /\
      ghost_inv_at D lo d cenv cx ff Gf tf t) /\
    alloca_frame cenv es sa s cenv ff t /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s n b sz' ==>
        off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule write_memory_place_entry_update >>
  disch_then (qx_choosel_then [`old`,`new`] strip_assume_tac) >>
  `old = entry` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `old = entry` SUBST_ALL_TAC >>
  `compile_store_memory cenv (Var xs) (Var xd) ty ty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `type_widens_to (get_tenv cx) ty ty` by simp[type_widens_to_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  mp_tac (Q.INST [`xs` |-> `xs`,`xd` |-> `xd`,`dty` |-> `ty`,
    `sty` |-> `ty`,`cenv` |-> `cenv`,`tenv` |-> `get_tenv cx`,
    `sa` |-> `sa`,`sb` |-> `sb`,`stv` |-> `tv`,`dtv` |-> `tv`,
    `v` |-> `v`,`s` |-> `s`,`sw` |-> `sw`,`dw` |-> `dw`,
    `tn` |-> `tn`,`G` |-> `G`,`lo` |-> `lo`,`ctx` |-> `ctx`,
    `func` |-> `func`,`explicit` |-> `explicit`,`PG` |-> `PG`]
    (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `w2n dw = _` (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  drule_all memory_subpath_state_post >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  drule_all memory_subpath_ghost_post >> strip_tac >>
  `!(H:(bool # 'a word # type_value) list # num list) D d.
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at D lo d cenv cx es G tn s ==>
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t` by
    (rpt strip_tac >>
     qpat_x_assum `stmt_state_rel H0 ctx func cenv cx es s` kall_tac >>
     qpat_x_assum `ghost_inv_at D0 lo d0 cenv cx es G tn s` kall_tac >>
     drule_all memory_subpath_state_post >> strip_tac >>
     drule_all memory_subpath_ghost_post >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem direct_memory_subpath_store_joint:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F NONE ty ty
    bytes sa = ((),sb) /\ ~is_word_type ty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size tv <= w2n sw) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  write_place cx (MemoryPlace id path) v es = (INL (),ff) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME bw /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  w2n dw = w2n bw+k /\ lo <= w2n dw /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  ?t Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t /\
    alloca_frame cenv es sa s cenv ff t /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s n b sz' ==>
        off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all direct_memory_subpath_store_effect >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_assum `!H D d. _ /\ _ ==> _`
    (qspecl_then [`H`,`D`,`d`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
