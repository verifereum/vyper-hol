(* The memory-local assignment suffix stages when the compiler stages. *)
Theory bodyFullAssignMemoryValue
Ancestors
  bodyFullMemoryValue bodyFullLocalCopy bodyFullMemoryFrames
  annassignRelayoutCode assignRelayoutFrame typedMemoryCopy
  bodyMemBopRestWordPath fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath
  stmtLowering exprLoweringProps loweringStateRelDefs loweringPosts
  assignTuplePtrCopyLen localPtrsProps freshWrites compileEnv bodyPtrDefs
  venomState venomMemDefs venomInst ptrDiscipline memSafeRun fragExec arithmetic

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
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?id cap. local_region cenv es.scopes s id (w2n dw) cap /\
    type_memory_size dtv <= cap` by
    (qexistsl_tac [`id`,`cap`] >> simp[local_region_def] >>
     metis_tac[vyperLookupTheory.find_containing_scope_lookup]) >>
  mp_tac (SPEC_ALL body_full_memory_value_path) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_genl_tac [`H`,`D`,`d`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      irule body_full_local_copy_post >> simp[] >>
      conj_tac >- (qexists_tac `sb` >> simp[]) >>
      qexistsl_tac [`Gu`,`PG`,`dw`,`explicit`,`u`,`scStore`,`tu`] >>
      simp[] >> rpt conj_tac
      >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
          qexists_tac `sa` >> fs[ci_mono_def]) >>
      metis_tac[freshWritesTheory.not_fresh_at_mono,ci_mono_def]) >>
  simp[]
QED
