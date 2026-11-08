(* Tuple-indexed applications of the same-endpoint store runners. *)
Theory tuplePlaceBranchReady
Ancestors
  tuplePlacePointerReady tuplePlaceFramedStore tuplePlaceOwnedValueFrame
  tuplePlaceEqualMemory tuplePlaceBorrowStore

Theorem tuple_place_pointer_word_store:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\ is_word_type (EL i tys) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
    | _ => MSTORE) [dst; EL i elems] sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (loc = LocMemory ==> w2n w + type_memory_size_list ltvs <= w2n dw \/
    w2n dw + type_memory_size (EL i tvs) <= w2n w) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) t.vs_memory =
    mem_bytes_at (w2n w) (type_memory_size_list ltvs) s.vs_memory
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) (EL i tys)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuple_place_index_fit >> strip_tac >>
  drule_all tuple_place_pointer_source_facts >> strip_tac >>
  `expr_val_rel cx (EL i ltys) (EL i vs) (EL i elems) s` by
    (irule tuple_place_pointer_value_rel >>
     metis_tac[]) >>
  `EL i ltys = EL i tys` by
    metis_tac[typedMemoryCopyTheory.typed_copy_word_widening] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (`EL i ltvs = EL i tvs` by gvs[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL,
        listTheory.LIST_REL_EL_EQN] >>
     qpat_x_assum `!n. _ ==> value_has_type _ _` (qspec_then `i` mp_tac) >> simp[]) >>
  irule tuple_place_word_run_frame >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  simp[] >> qexists `EL i vs` >> metis_tac[arithmeticTheory.ADD_COMM]
QED
