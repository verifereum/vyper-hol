(* Shared operational Stage + Store, independent of source binding installation. *)
Theory bodyFullMemoryValue
Ancestors
  bodyFullMemoryStore bodyFullMemoryStage bodyFullMemoryFrames
  annassignRelayoutCode typedMemoryCopy allocaSiteResource
  bodyMemBopRestWordPath fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath
  stmtLowering exprLoweringProps loweringStateRelDefs loweringPosts
  assignTuplePtrCopyLen localPtrsProps freshWrites compileEnv bodyPtrDefs
  venomState venomMemDefs venomInst ptrDiscipline memSafeRun fragExec arithmetic

Theorem body_full_memory_value_path:
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
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H0 ctx func cenv cx es s /\ alloca_history func s /\
  ((?id cap. local_region cenv es.scopes s id (w2n dw) cap /\
      type_memory_size dtv <= cap) \/
   (?aid cap. FLOOKUP s.vs_allocas aid = SOME (w2n dw,cap) /\
      aid <> sa.cs_next_id /\ type_memory_size dtv <= cap)) /\
  local_ptrs_reserved cenv sa /\
  ~is_word_type sty /\ expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf u Gu tu scStore.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es u) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gu tu u) /\
    typed_copy_state_frame scStore (w2n dw) (type_memory_size dtv) u t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    (!x. not_fresh_at scStore x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK t,Gf,tf)) /\
    fn_has_code scStore sb func /\ ci_mono sa scStore /\
    local_ptrs_reserved cenv scStore /\ lookup_var p u = SOME dw /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv (Var xs) (Var p) dty sty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  mp_tac (Q.INST [`xd` |-> `p`, `tenv` |-> `get_tenv cx`]
    (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`,`s`,`G`,`tn`,`sa`] >> simp[] >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def,state_rel_def] >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  fs[typed_copy_state_frame_def,venom_state_component_equality,ci_mono_def,cs_extends_def]
QED

Resume body_full_memory_value_path[staged]:
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all assign_memory_relayout_code >> strip_tac >>
  rename1 `compile_store_memory cenv buf.buf_operand (Var p) dty sty sc' = ((),sb)` >>
  `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
   compile_copy_memory buf.buf_operand (Var xs) (type_memory_size stv) sm = ((),sc')` by
    metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `type_memory_size tv`]
    (SPEC_ALL body_full_memory_stage_path))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `ptr_covers Gf tf root t (type_memory_size stv)` >>
  rename1 `lookup_var root t = SOME (n2w b)` >>
  `lookup_var p t = SOME dw /\ not_fresh_at sc' p` by metis_tac[] >>
  `ptr_covers Gf tf p t (type_memory_size dtv)` by
    (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  `alloca_history func t /\ alloca_inv t` by metis_tac[rest_word_marked_alloca] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by metis_tac[rest_word_marked_allocation_posts] >>
  `regions_disjoint b (type_memory_size stv) (w2n dw) (type_memory_size dtv)` by
    suspend "separation" >>
  `b < dimword (:256) /\
   w2n dw + type_memory_size dtv <= t.vs_alloca_next` by decide_tac >>
  `compile_store_memory cenv (Var root) (Var p) dty sty sc' = ((),sb)` by metis_tac[] >>
  `b MOD dimword (:256) = b` by simp[] >>
  mp_tac (Q.INST [`xd` |-> `p`, `tenv` |-> `get_tenv cx`,
    `xs` |-> `root`, `sa` |-> `sc'`, `s` |-> `t`,
    `sw` |-> `(n2w b):bytes32`, `G` |-> `Gf`, `tn` |-> `tf`]
    (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    fs[loweringStateRelDefsTheory.regions_disjoint_def])) >> strip_tac >>
  rename1 `typed_copy_state_frame sc' _ _ t t'` >>
  qexistsl_tac [`t'`,`Gf'`,`tf'`,`t`,`Gf`,`tf`,`sc'`] >>
  conj_tac >- suspend "join" >>
  simp[] >> suspend "frame"
QED

Resume body_full_memory_value_path[separation]:
  qpat_x_assum `(?id cap. local_region _ _ _ _ _ _ /\ _) \/ _` strip_assume_tac
  >- (`local_region cenv es.scopes t id (w2n dw) cap` by
        (fs[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
      `regions_disjoint b (type_memory_size stv) (w2n dw) cap` by metis_tac[] >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `FLOOKUP t.vs_allocas aid = SOME (w2n dw,cap)` by metis_tac[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def,
    loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
  disch_then drule >> simp[] >> decide_tac
QED

Resume body_full_memory_value_path[join]:
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`t`,`Gf`,`tf`,`[]`,`OK t'`,`Gf'`,`tf'`] mp_tac) >> simp[]
QED

Resume body_full_memory_value_path[frame]:
  `gas_marked_path T ctx func t 0 (OK t')` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tf) _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  `local_ptrs_reserved cenv sc'` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `ci_mono sa sc'` by metis_tac[ci_mono_trans] >>
  `t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)`` o
       CONJUNCT1 o REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  simp[]
QED

Finalise body_full_memory_value_path
