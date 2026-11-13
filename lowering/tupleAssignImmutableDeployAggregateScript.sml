(* Aggregate immutable head stores.  The intermediate state is the actual
   registered normalization endpoint, not an independently chosen execution. *)
Theory tupleAssignImmutableDeployAggregate
Ancestors
  tupleAssignImmutableDeployAggregatePlain
  tupleAssignImmutableDeployAggregateNormalize tuplePlaceHeadOpen typedMemoryCopy

Theorem tuple_immutable_aggregate_store:
  place = (dst,SOME LocCode,SOME (ValPT dty)) /\
  src = EL i elems /\ sty = EL i ltys /\ L = type_memory_bytes cenv dty /\
  da = (case dty of ArrayT et (Dynamic _) =>
    SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
    | _ => NONE) /\
  (let dst = FST place; loc_opt = FST (SND place); dst_ty_opt = SND (SND place);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  ~is_word_type sty /\ type_widens_to (get_tenv cx) sty dty /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w off) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (dty <> sty /\ ~is_bytestring_type dty ==>
   !b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  regions_disjoint (w2n sw) (type_memory_size stv) off L /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at sa x) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty /\
  L = type_memory_size dtv /\ L = 32*n /\ 0 < L /\ off+L < dimword (:256) ==>
  ?r q. (dty = sty ==> r = s) /\
    stmt_state_rel ctx func cenv cx es r /\
    alloca_frame cenv es sa s cenv es r /\
    gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory dtv v off q.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off L q.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP r.vs_allocas aid = SOME entry) /\
    (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
    (!a k. regions_disjoint a k off L ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    (!aid b len a k. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id /\ b <= a /\ a+k <= b+len /\
      (!name lb sz. local_region cenv es.scopes s name lb sz ==>
        b+len <= lb \/ lb+sz <= b) /\ regions_disjoint a k off L ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH r.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_assign_value cenv dst LocCode src (is_word_type dty) NONE
     dty sty L sa = ((),sb)` by gvs[LET_THM] >>
  qpat_x_assum `place = _` kall_tac >>
  qpat_x_assum `src = EL i elems` kall_tac >>
  qpat_x_assum `sty = EL i ltys` kall_tac >>
  qpat_x_assum `L = type_memory_bytes cenv dty` kall_tac >>
  qpat_x_assum `da = _` kall_tac >>
  qpat_x_assum `(let dst = _ in _) = _` kall_tac >>
  `~is_word_type dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  fs[] >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
      `val_footprint stv v <= type_memory_size stv` by
        metis_tac[exprSimPropsTheory.val_footprint_le] >>
      drule tuple_immutable_bytestring_aggregate_store >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
      disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
      disch_then (qspec_then `off` mp_tac) >>
      (impl_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
      strip_tac >> gvs[] >> qexistsl_tac [`r`,`q`] >>
      simp[stmtSimDefsTheory.alloca_frame_def] >> metis_tac[]) >>
  Cases_on `dty = sty`
  >- (`dtv = stv` by metis_tac[optionTheory.SOME_11] >>
      `n = (if L <= 32 then 1 else (L+31) DIV 32)` by
        (Cases_on `L <= 32` >- (fs[] >> decide_tac) >>
         qpat_assum `L = 32*n` (fn th => rewrite_tac[th]) >>
         simp[arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_DIV_ADD_DIV]) >>
      drule tuple_immutable_direct_aggregate_store >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
      disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (qspecl_then [`n`,`type_memory_size stv`,`off`] mp_tac) >>
      (impl_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
        metis_tac[exprSimPropsTheory.val_footprint_le, arithmeticTheory.EQ_LESS_EQ])) >>
      strip_tac >>
      qpat_x_assum `n = if _ then _ else _` kall_tac >>
      qpat_x_assum `r = s` SUBST_ALL_TAC >>
      qexistsl_tac [`s`,`q`] >>
      simp[stmtSimDefsTheory.alloca_frame_def] >>
      conj_tac >- metis_tac[] >>
      gvs[]) >>
  drule tuple_immutable_normalized_aggregate_store >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP cenv.ce_module_vars _ = _`)) >>
  disch_then (qspec_then `n` mp_tac) >>
  (impl_tac >- (simp[] >> fs[])) >> strip_tac >>
  qexistsl_tac [`r`,`q`] >> simp[] >>
  gvs[venomStateTheory.venom_state_component_equality] >>
  first_assum ACCEPT_TAC
QED
