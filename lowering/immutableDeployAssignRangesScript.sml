(* Owned source ranges for constructor immutable stores. *)
Theory immutableDeployAssignRanges
Ancestors
  immutableDeployAssignFacts exprSimTypedAlloc annassignRelayoutSource
  compileEnv loweringPosts placeStoreStorage exprSimHyps valueTypingMemoryProps

Theorem immutable_assign_source_range:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  eval_operand op s = SOME w /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv ==>
  w2n w + val_footprint stv v < dimword (:256) /\
  (val_footprint stv v = 0 \/
   compileEnv$regions_disjoint off (type_memory_size dtv)
     (w2n w) (val_footprint stv v))
Proof
  strip_tac >> conj_tac
  >- (drule_all expr_val_at_bound >> simp[]) >>
  drule_all immutable_assign_declared_region >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem immutable_assign_copy_metadata:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es ==>
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields)
Proof
  strip_tac >> fs[bodySimTheory.body_inv_def, exprSimHypsDefsTheory.expr_sim_inv_def] >>
  metis_tac[]
QED

Theorem immutable_assign_nonbytes_source_owned:
  expr_val_at cenv cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  eval_operand op s = SOME w ==>
  type_memory_size stv = 0 \/
  (?aid b sz. aid < sb.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    b <= w2n w /\ w2n w + type_memory_size stv <= b + sz) \/
  (?n b sz. local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + type_memory_size stv <= b + sz)
Proof
  strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    (irule nonbytes_evaluated_val_footprint >> metis_tac[]) >>
  fs[expr_val_at_def] >> metis_tac[]
QED

Theorem immutable_assign_bytestring_extent:
  type_widens_to tenv sty dty /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_in_memory stv v p mem ==>
  ?len. mem_word_at p mem = n2w len /\
    val_footprint stv v = 32 + len /\
    val_footprint dtv v = 32 + len /\
    32 + len <= 32 * (1 + word_size len) /\
    32 * (1 + word_size len) <= type_memory_size dtv
Proof
  strip_tac >> drule_all place_store_bytestring_representation >>
  strip_tac >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      valueEncodingDefsTheory.val_in_memory_def, val_footprint_def,
      valueEncodingTheory.type_memory_size_def] >>
  qmatch_goalsub_abbrev_tac `word_size len` >>
  `len <= dst_cap` by (simp[Abbr `len`] >> decide_tac) >>
  drule word_size_monotone >>
  mp_tac (Q.SPEC `len` word_size_capacity) >> decide_tac
QED
