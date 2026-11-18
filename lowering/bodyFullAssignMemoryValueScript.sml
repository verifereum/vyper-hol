(* The memory-local assignment suffix stages when the compiler stages. *)
Theory bodyFullAssignMemoryValue
Ancestors
  bodyFullMemoryStore bodyFullMemoryStage bodyFullLocalCopy bodyFullMemoryFrames
  annassignRelayoutCode assignRelayoutFrame typedMemoryCopy
  bodyMemBopRestWordPath fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath
  stmtLowering exprLoweringProps loweringStateRelDefs loweringPosts
  assignTuplePtrCopyLen localPtrsProps freshWrites compileEnv bodyPtrDefs
  venomState venomMemDefs venomInst ptrDiscipline memSafeRun fragExec arithmetic
  bodyFullHashKeccakFixed stateRelProj stmtSimDefs tupleTargetStoreProps

Theorem body_full_assign_local_memory_value_frame_path:
  compile_assign_value cenv (Var p) LocMemory (Var xs) F loc dty sty bytes sa = ((),sb) /\
  (loc = NONE \/ loc = SOME LocMemory) /\
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn p s (type_memory_size dtv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H0 ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\ entry.type = dtv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  type_memory_size dtv <= cap /\ local_ptrs_reserved cenv sa /\
  ~is_word_type sty /\ expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H D d. stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s ==>
      stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
      ghost_inv_at D lo d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame cenv es sa s cenv
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region cenv es.scopes s name a len ==> off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `MAP FDOM (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) =
   MAP FDOM es.scopes` by metis_tac[tuple_target_local_domain_frame] >>
  `local_region cenv es.scopes s id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[vyperLookupTheory.find_containing_scope_lookup]) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv (Var xs) (Var p) dty sty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  mp_tac (Q.INST [`xd` |-> `p`,`tenv` |-> `get_tenv cx`]
    (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_genl_tac [`H`,`D`,`d`] >> strip_tac >>
      irule body_full_local_copy_post >> simp[] >>
      conj_tac >- (qexists_tac `sb` >> simp[]) >>
      qexistsl_tac [`G`,`PG`,`dw`,`explicit`,`s`,`sa`,`tn`] >> simp[]) >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  simp[] >> conj_tac >- suspend "direct_frame" >> suspend "direct_taint"
QED

Resume body_full_assign_local_memory_value_frame_path[direct_frame]:
  irule alloca_frame_of_mem_frame >> simp[] >>
  conj_tac
  >- (qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
      `off+sz <= w2n dw \/ w2n dw+cap <= off` by metis_tac[] >>
      `off+sz <= w2n dw \/ w2n dw+type_memory_size dtv <= off` by decide_tac >>
      fs[typed_copy_state_frame_def,typed_copy_frame_def]) >>
  conj_tac >- fs[] >> metis_tac[]
QED

Resume body_full_assign_local_memory_value_frame_path[direct_taint]:
  qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
  `off+sz <= w2n dw \/ w2n dw+cap <= off` by metis_tac[] >>
  `~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv)` by decide_tac >>
  metis_tac[]
QED

Resume body_full_assign_local_memory_value_frame_path[staged]:
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all assign_memory_relayout_code >> strip_tac >>
  `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
   compile_copy_memory buf.buf_operand (Var xs) (type_memory_size stv) sm = ((),sc')` by
    metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size tv`]
    (SPEC_ALL body_full_memory_stage_frame_path))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `ptr_covers Gf tf root t (type_memory_size stv)` >>
  rename1 `lookup_var root t = SOME (n2w b)` >>
  `lookup_var p t = SOME dw /\ not_fresh_at sc' p` by metis_tac[] >>
  `ptr_covers Gf tf p t (type_memory_size dtv)` by
    (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_region cenv es.scopes t id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[vyperLookupTheory.find_containing_scope_lookup]) >>
  `regions_disjoint b (type_memory_size stv) (w2n dw) cap` by metis_tac[] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule rest_word_path_frontier >> simp[]) >>
  `b < dimword (:256) /\
   w2n dw + type_memory_size dtv <= t.vs_alloca_next` by decide_tac >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) \/
      cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc' x` by metis_tac[] >>
  `compile_store_memory cenv (Var root) (Var p) dty sty sc' = ((),sb)` by metis_tac[] >>
  `?t' Gf' tf'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,Gf,tf) [] (OK t',Gf',tf')) /\
    val_in_memory dtv v (w2n dw) t'.vs_memory /\
    (!mem. mem_agree_outside tf'.t_mem t'.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sc' (w2n dw) (type_memory_size dtv) t t' /\
    ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
    t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf'.t_stor = tf.t_stor /\ tf'.t_trans = tf.t_trans /\ tf'.t_imm = tf.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf'.t_mem <=> i IN tf.t_mem)) /\
    (!x. not_fresh_at sc' x ==>
      lookup_var x t' = lookup_var x t /\ FLOOKUP Gf' x = FLOOKUP Gf x /\
      op_taint tf' (Var x) = op_taint tf (Var x))` by
    (irule body_full_memory_store_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`,`get_tenv cx`] >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`t'`,`Gf'`,`tf'`] >>
  conj_tac >- suspend "join" >>
  conj_tac >- suspend "post" >>
  `gas_marked_path T ctx func t 0 (OK t')` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tf) _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  `alloca_history func t /\ alloca_inv t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >>
     drule_all rest_word_marked_alloca >> simp[]) >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  simp[] >> conj_tac >- suspend "allocation" >>
  conj_tac >- suspend "staged_frame" >> suspend "staged_taint"
QED

Resume body_full_assign_local_memory_value_frame_path[join]:
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`t`,`Gf`,`tf`,`[]`,`OK t'`,`Gf'`,`tf'`] mp_tac) >> simp[]
QED

Resume body_full_assign_local_memory_value_frame_path[post]:
  qx_genl_tac [`H`,`D`,`d`] >> strip_tac >>
  irule body_full_local_copy_post >> simp[] >>
  conj_tac >- (qexists_tac `sb` >> simp[]) >>
  qexistsl_tac [`Gf`,`PG`,`dw`,`explicit`,`t`,`sc'`,`tf`] >>
  simp[] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
      fs[ci_mono_def] >> decide_tac) >>
  metis_tac[]
QED

Resume body_full_assign_local_memory_value_frame_path[allocation]:
  fs[typed_copy_state_frame_def,venom_state_component_equality] >> metis_tac[]
QED

Resume body_full_assign_local_memory_value_frame_path[staged_frame]:
  irule alloca_frame_local_store >> simp[] >>
  reverse conj_tac >- (goal_assum (drule_at Any)) >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`w2n dw`,`id`,`type_memory_size dtv`,`cap`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa q` by metis_tac[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  conj_tac >- fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
  fs[]
QED

Resume body_full_assign_local_memory_value_frame_path[staged_taint]:
  qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
  `off+sz <= w2n dw \/ w2n dw+cap <= off` by metis_tac[] >>
  `~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv)` by decide_tac >>
  `i IN tf.t_mem` by metis_tac[] >>
  qpat_x_assum `!aid off sz i. _` irule >>
  (reverse conj_tac >- simp[]) >>
  qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Finalise body_full_assign_local_memory_value_frame_path

Theorem body_full_assign_local_memory_value_path:
  compile_assign_value cenv (Var p) LocMemory (Var xs) F loc dty sty bytes sa = ((),sb) /\
  (loc = NONE \/ loc = SOME LocMemory) /\
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn p s (type_memory_size dtv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H0 ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\ entry.type = dtv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  type_memory_size dtv <= cap /\ local_ptrs_reserved cenv sa /\
  ~is_word_type sty /\ expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H D d. stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s ==>
      stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
      ghost_inv_at D lo d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_tac >> mp_tac (SPEC_ALL body_full_assign_local_memory_value_frame_path) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED
