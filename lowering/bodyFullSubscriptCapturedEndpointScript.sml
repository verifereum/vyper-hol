(* The dynamic length load observes the captured array at the index endpoint.
   The provenance row covers the allocation layout even when the length is zero. *)
Theory bodyFullSubscriptCapturedEndpoint
Ancestors
  bodyFullSubscriptCapturedPlace bodyPtrBopInMemoryContents
  bodyPtrBopHashFootprint exprSimSubscriptArraySuffix exprSimSubscriptArraySource
  exprSimSource typedCopyLayoutPtr valueEncodingProps ptrDiscipline bodyPtrDefs
  loweringPosts exprSimProps venomState valueEncoding words finite_map list

Theorem captured_dynamic_memory_input[local]:
  ptr_vv_ok cx ty raw (LocatedValue t p) fin G tn u /\
  p.ptr_location = LocMemory /\
  read_result cx raw fin = (INL (ArrayV (DynArrayV vs)),fin) /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV etv (Dynamic cap)) /\
  eval_operand p.ptr_operand u = SOME a ==>
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  mload (w2n a) u = n2w (LENGTH vs) /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  ?x b sz. p.ptr_operand = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n a /\ w2n a + 32 + cap * type_memory_size etv <= b + sz /\
    ptr_covers G tn x u 32
Proof
  strip_tac >>
  `op_taint tn p.ptr_operand = {} /\
   ptr_mem_ok cx ty (ArrayV (DynArrayV vs)) p.ptr_operand G tn u` by
    fs[ptr_vv_ok_def] >>
  conj_asm1_tac >- metis_tac[ptr_mem_ok_robust] >>
  conj_tac
  >- (`mem_agree_outside tn.t_mem u.vs_memory u.vs_memory` by
        simp[mem_agree_outside_def] >>
      metis_tac[dynarray_in_memory_robust_length, mem_word_at_eq_mload]) >>
  conj_tac >- metis_tac[dynarray_memory_header_clean] >>
  `val_footprint (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) <> 0` by
    simp[val_footprint_def, type_memory_size_def] >>
  drule_all_then strip_assume_tac ptr_mem_ok_bounds >>
  gvs[exprSimPropsTheory.val_store_size_def, type_memory_size_def,
      ptr_covers_def, eval_operand_def] >>
  goal_assum (drule_at Any) >> qexistsl [`a`,`b`,`sz`] >> simp[] >> decide_tac
QED

Theorem subscript_dynamic_header_at_index:
  expr_body_pre ce cx env (Subscript ty obj idx) es /\
  eval_expr cx obj es = (INL raw,mid) /\
  expr_type obj = ArrayT et (Dynamic cap) /\
  post_value_type ce obj = expr_type obj /\
  evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv (Dynamic cap)) /\
  vv_post H ctx fn ce cx obj es sa sm s0 mid raw (LocatedValue t p) s /\
  ptr_vv_ok cx (post_value_type ce obj) raw (LocatedValue t p) mid G tn s /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key op u /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  local_ptrs_reserved ce sm /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  ((?id path. raw = PlaceR (MemoryPlace id path) /\ base_from_pop obj) \/
   (?v. raw = Value v /\ p.ptr_location = LocMemory /\
        vv_own ce cx (post_value_type ce obj) sa sm mid raw (LocatedValue t p) s)) ==>
  p.ptr_location = LocMemory /\
  ptr_vv_ok cx (expr_type obj) raw (LocatedValue t p) fin G' tn' u /\
  ?a vs x b sz.
    read_result cx raw mid = (INL (ArrayV (DynArrayV vs)),mid) /\
    read_result cx raw fin = (INL (ArrayV (DynArrayV vs)),fin) /\
    value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    val_wf (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    LENGTH vs <= cap /\
    eval_operand p.ptr_operand s = SOME a /\ eval_operand p.ptr_operand u = SOME a /\
    (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
       val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
    mload (w2n a) u = n2w (LENGTH vs) /\
    mem_word_taint tn'.t_mem (w2n a) = {} /\
    p.ptr_operand = Var x /\ FLOOKUP G' x = SOME (b,sz) /\ b <= w2n a /\
    ptr_covers G' tn' x u 32 /\
    w2n a + 32 + cap * type_memory_size etv <= b + sz /\
    w2n a + 32 + cap * type_memory_size etv < dimword (:256) /\
    ((?id path. raw = PlaceR (MemoryPlace id path) /\
         runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Dynamic cap)) /\
         popped_keys_indexed fin.scopes /\
         vv_place_ptr ce cx fin u raw (LocatedValue t p) /\
         place_ptr_rel ce cx u raw a (SOME LocMemory) (Type (expr_type obj))) \/
     (raw = Value (ArrayV (DynArrayV vs)) /\
         vv_own ce cx (expr_type obj) sa sm fin raw (LocatedValue t p) u))
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME (ArrayTV etv (Dynamic cap))` by
    (simp[] >> (gvs[])) >>
  `p.ptr_location = LocMemory /\
   ptr_vv_ok cx (expr_type obj) raw (LocatedValue t p) fin G' tn' u /\
   ?a v. read_result cx raw mid = (INL v,mid) /\ read_result cx raw fin = (INL v,fin) /\
         val_wf (ArrayTV etv (Dynamic cap)) v /\
         eval_operand p.ptr_operand s = SOME a /\ eval_operand p.ptr_operand u = SOME a /\
         ((?id path. raw = PlaceR (MemoryPlace id path) /\
             runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Dynamic cap)) /\
             popped_keys_indexed fin.scopes /\
             vv_place_ptr ce cx fin u raw (LocatedValue t p) /\
             place_ptr_rel ce cx u raw a (SOME LocMemory) (Type (expr_type obj))) \/
          (raw = Value v /\ vv_own ce cx (expr_type obj) sa sm fin raw (LocatedValue t p) u))`
     by (qpat_x_assum `(?id path. _) \/ (?v. _)` strip_assume_tac
         >- (qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
             drule_all_then strip_assume_tac subscript_captured_pop_transport >>
             gvs[] >> metis_tac[]) >>
         qpat_x_assum `raw = Value _` SUBST_ALL_TAC >>
         drule_all_then strip_assume_tac subscript_owned_value_transport >>
         gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >> metis_tac[]) >>
  `expr_body_pre ce cx env obj es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx obj _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `value_has_type (ArrayTV etv (Dynamic cap)) v` by metis_tac[optionTheory.SOME_11] >>
  drule_all_then assume_tac vv_post_memory_footprint_bound >>
  drule_then strip_assume_tac typedMemoryCopyTheory.typed_copy_dynarray_typed_value >>
  gvs[] >>
  drule_all_then strip_assume_tac captured_dynamic_memory_input >>
  qexistsl [`x`,`b`,`sz`] >> gvs[val_footprint_def, type_memory_size_def] >> decide_tac
QED
