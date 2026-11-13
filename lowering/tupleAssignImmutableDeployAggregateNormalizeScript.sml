(* Normalize once, then transfer from that registered allocation.  The
   normalization byte frame is conditional on whole-allocation separation
   from live locals, exactly as in the owned tuple snapshot alternative. *)
Theory tupleAssignImmutableDeployAggregateNormalize
Ancestors
  immutableAssignStore immutableAssignNormalizeFrame immutableAssignStoreLength
  tuplePlaceSnapshot

Theorem tuple_immutable_normalized_aggregate_store:
  compile_assign_value cenv dst LocCode src F NONE dty sty L sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty /\
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
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w off) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at sa x) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty /\
  L = type_memory_size dtv /\ L = 32*n /\ 0 < L /\ off+L < dimword (:256) ==>
  ?buf mid sm r pw q.
    compile_alloc_buffer L sa = (buf,mid) /\
    compile_store_memory_typed cenv buf.buf_operand dty src sty mid = ((),sm) /\
    gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx es r /\
    eval_operand buf.buf_operand r = SOME pw /\
    val_in_memory dtv v (w2n pw) r.vs_memory /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n pw,L) /\
    w2n pw+L < dimword (:256) /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP r.vs_allocas aid = SOME entry) /\
    alloca_frame cenv es sa s cenv es r /\
    gas_marked_path F ctx func r 0 (OK q) /\
    gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory dtv v off q.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off L q.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
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
  drule_all immutable_assign_normalized_compile >> strip_tac >>
  `n = (if L <= 32 then 1 else (L+31) DIV 32)` by
    (Cases_on `L <= 32` >- (fs[] >> decide_tac) >>
     qpat_assum `L = 32*n` (fn th => rewrite_tac[th]) >>
     simp[arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_DIV_ADD_DIV]) >>
  `compile_imm_store_words cenv.ce_imm_alloca buf.buf_operand dst n 0 sm = ((),sb)` by
    (metis_tac[immutableDeployOperandTransferTheory.immutable_store_suffix_words]) >>
  qpat_x_assum `(if _ then _ else _) sm = _` kall_tac >>
  qpat_x_assum `n = if _ then _ else _` kall_tac >>
  `cs_extends sa mid /\ cs_extends mid sm /\ cs_extends sm sb` by
    (metis_tac[loweringHaltTheory.compile_alloc_buffer_extends,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND,
      cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family,
      exprLoweringPropsTheory.ci_mono_compile_imm_store_words]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,
      compileEnvTheory.cs_extends_trans] >>
  `compile_alloc_buffer (type_memory_size dtv) sa = (buf,mid)` by metis_tac[] >>
  drule_all immutable_assign_normalize_prefix >> strip_tac >>
  `regions_disjoint (w2n pw) L off L` by suspend "geometry" >>
  `(!x. dst = Var x ==> not_fresh_at sm x) /\
   (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
      not_fresh_at sm x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sm x)` by suspend "fresh" >>
  `eval_operand dst r = SOME (n2w off) /\
   (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region r = SOME 0w)` by
    suspend "operands" >>
  `eval_operand buf.buf_operand r = SOME (n2w (w2n pw))` by simp[] >>
  drule_at (Pat `compile_imm_store_words _ _ _ _ _ _ = _`)
    immutableDeployOperandTransferTheory.immutable_words_old_prefix_path >>
  disch_then (qspec_then `r` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand r = _`)) >>
  disch_then (qspecl_then [`L`,`func`,`ctx`,`off`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  (impl_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> suspend "post"
QED

Resume tuple_immutable_normalized_aggregate_store[geometry]:
  markerLib.RESUME_TAC >>
  qpat_assum `stmt_state_rel _ _ _ _ _ r`
    (strip_assume_tac o REWRITE_RULE[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[exprLoweringPropsTheory.immutable_alloca_sep_def]) >>
  qpat_x_assum `immutable_decl_sep _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[exprLoweringPropsTheory.immutable_decl_sep_def]) >>
  simp[] >> disch_then (qspecl_then [`id`,`dty`,`dtv`,`off`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!aid b sz. FLOOKUP r.vs_allocas aid = _ ==> _`
    (qspec_then `sa.cs_next_id` mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED
Resume tuple_immutable_normalized_aggregate_store[fresh]:
  markerLib.RESUME_TAC >>
  `ci_mono mid sm` by
    metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `mid.cs_next_var <= sm.cs_next_var` by gvs[exprLoweringPropsTheory.ci_mono_def] >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  rpt conj_tac >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `mid` >> simp[] >>
  gvs[] >> metis_tac[]
QED
Resume tuple_immutable_normalized_aggregate_store[operands]:
  markerLib.RESUME_TAC >>
  `r.vs_labels = s.vs_labels` by
    (drule stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_labels >> simp[]) >>
  conj_tac
  >- (Cases_on `dst` >> fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `region` >>
  fs[venomStateTheory.eval_operand_def] >> metis_tac[]
QED
Resume tuple_immutable_normalized_aggregate_store[post]:
  markerLib.RESUME_TAC >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (fragGasModeTheory.gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `r` >> simp[]) >>
  `val_in_memory dtv v off u.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_relocate >> metis_tac [arithmeticTheory.EQ_LESS_EQ]) >>
  `immutable_value_bytes_rel dtv v (mem_bytes_at off L u.vs_memory)` by
    (metis_tac[immutableDeployAssignBytesTheory.immutable_memory_bytes,
      immutableDeployAssignAdmissibleTheory.evaluated_immutable_admissible,
      vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  drule_all immutable_assign_store_words_memory_length >> strip_tac >>
  qexistsl_tac [`r`,`pw`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gvs[venomStateTheory.venom_state_component_equality,
      loweringStateRelDefsTheory.regions_disjoint_def,
      exprLoweringPropsTheory.same_blocks_def,
      venomStateTheory.lookup_var_def] >> (
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ s` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ r` kall_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (`ci_mono mid sm` by
           metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
         drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
         fs[exprLoweringPropsTheory.ci_mono_def] >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  `mem_bytes_at a k u.vs_memory = mem_bytes_at a k r.vs_memory` by
    (first_x_assum irule >> decide_tac) >>
  simp[] >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[stmtSimDefsTheory.alloca_frame_def]) >>
  disch_then (qspecl_then [`aid`,`b`,`len`] mp_tac) >> simp[] >> strip_tac >>
  `a = b + (a-b) /\ (a-b)+k <= len` by decide_tac >>
  metis_tac[valueEncodingPropsTheory.mem_bytes_at_translated_window])
QED
Finalise tuple_immutable_normalized_aggregate_store
