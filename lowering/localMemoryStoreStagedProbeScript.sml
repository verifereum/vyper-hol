(* The compiler's ALLOCA/MCOPY staging followed by a target subpath store. *)
Theory localMemoryStoreStagedProbe
Ancestors
  localMemoryStoreRunProbe bodyFullMemoryStage annassignRelayoutCode
  bodyFullMemoryFrames bodyPtrDefs stmtSimDefs localPtrsProps
  loweringStateRelDefs loweringPosts exprLoweringProps compileEnv
  stmtLowering context vyperState venomState ptrDiscipline
  fragGasOriginPtr freshWrites exprSimProps words list arithmetic

Theorem staged_memory_subpath_store_effect:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory) ty ty
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
  expr_val_at cenv cx ty start sa es v (Var xs) s /\
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
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
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
    (!(H:(bool # 256 word # type_value) list # num list) D d.
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
  drule_all assign_memory_relayout_code >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
   compile_copy_memory buf.buf_operand (Var xs) (type_memory_size tv) sm = ((),sc)` by
    metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size tv`]
    (SPEC_ALL (INST_TYPE
      (map (fn ty => ty |-> ``:256``)
        (type_vars_in_term (concl body_full_memory_stage_effect)))
      body_full_memory_stage_effect)))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `lookup_var root u = SOME (n2w b)` >>
  rename1 `ptr_covers G1 tn1 root u (type_memory_size tv)` >>
  `stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
     ctx func cenv cx es u /\
   ghost_inv_at D0 lo d0 cenv cx es G1 tn1 u` by
    (conj_tac
     >- (qpat_assum `!h:(bool # 256 word # type_value) list # num list.
            stmt_state_rel h _ _ _ _ _ _ ==> _`
           (qspec_then `H0` mp_tac) >> simp[]) >>
     qpat_assum `!df rd. ghost_inv_at df _ rd _ _ _ _ _ _ ==> _`
       (qspecl_then [`D0`,`d0`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var xd u = SOME dw /\ lookup_var p u = SOME bw /\
   not_fresh_at sc xd` by metis_tac[] >>
  `ptr_covers G1 tn1 xd u (type_memory_size tv)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `local_region cenv es.scopes u id (w2n bw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint b (type_memory_size tv) (w2n bw) cap` by metis_tac[] >>
  `type_memory_size entry.type <= cap` by
    (fs[stmt_state_rel_def,state_rel_def,local_ptrs_rel_def] >> metis_tac[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `b+type_memory_size tv <= w2n dw \/ w2n dw+type_memory_size tv <= b` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `b < dimword (:256)` by decide_tac >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `compile_assign_value cenv (Var xd) LocMemory (Var root) F NONE ty ty
    bytes sc = ((),sb)` by
    (simp[compile_assign_value_def] >>
     qpat_assum `buf.buf_operand = Var root` (fn eq =>
       qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) \/
      cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    metis_tac[] >>
  mp_tac (Q.INST [`xs` |-> `root`,`sa` |-> `sc`,`s` |-> `u`,
    `D0` |-> `D0`,`d0` |-> `d0`,
    `H0` |-> `(H0:(bool # 256 word # type_value) list # num list)`,
    `sw` |-> `(n2w b):bytes32`,`G` |-> `G1`,`tn` |-> `tn1`]
    (SPEC_ALL (INST_TYPE
      (map (fn ty => ty |-> ``:256``)
        (type_vars_in_term (concl direct_memory_subpath_store_effect)))
      direct_memory_subpath_store_effect))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> rpt strip_tac >>
    metis_tac[])) >> strip_tac >>
  `alloca_frame cenv es sa s cenv ff t` by
    (irule alloca_frame_trans >>
     qexistsl_tac [`cenv`,`es`,`u`,`sc`] >> simp[]) >>
  `!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sc.cs_next_id` by
       (conj_tac >- metis_tac[] >> decide_tac) >>
     `!n b sz'. local_region cenv es.scopes u n b sz' ==>
       off+sz <= b \/ b+sz' <= off` by
       (qpat_assum `alloca_frame cenv es sa s cenv es u`
          (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
        disch_then (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
        metis_tac[]) >>
     `i IN tn1.t_mem` by
       (qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[]) >>
  `!(H:(bool # 256 word # type_value) list # num list) D d.
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at D lo d cenv cx es G tn s ==>
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx es u` by
       (qpat_assum `!h:(bool # 256 word # type_value) list # num list.
          stmt_state_rel h _ _ _ _ _ s ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     `ghost_inv_at D lo d cenv cx es G1 tn1 u` by
       (qpat_assum `!df rd. ghost_inv_at df _ rd _ _ _ _ _ s ==> _`
          (qspecl_then [`D`,`d`] mp_tac) >> simp[]) >>
     qpat_assum `!h df rd. stmt_state_rel h _ _ _ _ _ u /\ _ ==> _`
       (qspecl_then [`H`,`D`,`d`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem staged_memory_subpath_store_joint:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory) ty ty
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
  expr_val_at cenv cx ty start sa es v (Var xs) s /\
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
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
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
  drule_all staged_memory_subpath_store_effect >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_assum `!H D d. _ /\ _ ==> _`
    (qspecl_then [`H`,`D`,`d`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
