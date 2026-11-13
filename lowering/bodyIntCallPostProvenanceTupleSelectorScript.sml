(* Tuple selections retain the owner of the actual base outcome. *)
Theory bodyIntCallPostProvenanceTupleSelector
Ancestors
  bodyIntCallPostProvenanceAttributeSelector exprSimTuple
  tupleMemoryLayout valueEncoding valueEncodingProps valueEncodingDefs
  loweringPosts context vyperAST words list typeLayoutProps exprSimProps
  stmtReasonVvMemory vyperState vyperTyping exprSimHypsDefs vyperTypeSystem
  bodyIntCallArgType bodyIntCallProducerInterface exprSimVVFrame
  bodyPtrSubscriptSeamTupleMemory bodyIntCallPostProvenanceSelectors
  compileEnv exprSimAttributeProps

Theorem intcall_tuple_element_layout[local]:
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
  val_wf (EL k tvs) (EL k vs) ==>
  sub_layout (TupleTV tvs) (ArrayV (TupleV vs))
    (SUM (TAKE k (MAP type_memory_size tvs))) (EL k tvs) (EL k vs) /\
  SUM (TAKE k (MAP type_memory_size tvs)) +
    val_footprint (EL k tvs) (EL k vs) <=
    val_footprint (TupleTV tvs) (ArrayV (TupleV vs))
Proof
  strip_tac >>
  `SUM (TAKE k (MAP type_memory_size tvs)) + type_memory_size (EL k tvs) <=
   type_memory_size_list tvs` by
    (mp_tac tuple_element_interval >>
     simp[MAP_TAKE, type_memory_size_list_sum]) >>
  conj_tac
  >- (simp[sub_layout_def, type_memory_size_def] >> rpt strip_tac >>
      gvs[val_in_memory_def, GSYM MAP_TAKE] >>
      irule tuple_in_memory_element >> simp[] >> goal_assum (drule_at Any)) >>
  drule val_footprint_le >>
  simp[val_footprint_def, type_memory_size_def]
QED

Theorem intcall_tuple_memory_provenance[local]:
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  intcall_vv_provenance ce cx (TupleT tys) sa sb ee raw bvv t /\
  expr_sim_inv ce cx env es /\ expr_type obj = TupleT tys /\
  post_value_type ce obj = TupleT tys /\ vv_loc bvv = LocMemory /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  ~dynarray_free (TupleTV tvs) /\ k < LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx result ee = (INL (EL k vs),ee) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset ce tys LocMemory k)) ==>
  intcall_vv_provenance ce cx (EL k tys) sa sb ee result
    (LocatedValue (EL k tys) (mk_ptr dst LocMemory)) t
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee t /\
   vv_at ce cx (TupleT tys) sa sb ee raw bvv t` by gvs[vv_post_def] >>
  drule_all tuple_memory_child_address >> strip_tac >>
  drule_all tuple_memory_placement >> strip_tac >>
  `val_wf (EL k tvs) (EL k vs)` by
    metis_tac[tuple_child_wf] >>
  drule_all intcall_tuple_element_layout >> strip_tac >>
  irule intcall_dynamic_memory_selection >> goal_assum (drule_at Any) >>
  qexistsl_tac [`w + n2w (tuple_offset ce tys LocMemory k)`,
    `TupleT tys`, `bvv`, `vv_operand bvv`, `raw`] >> simp[] >>
  Cases_on `bvv` >>
  gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def]
QED
