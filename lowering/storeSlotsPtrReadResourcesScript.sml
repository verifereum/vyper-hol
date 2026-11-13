(* Rounded live read resources for recursive sparse storage stores. *)
Theory storeSlotsPtrReadResources
Ancestors
  storeSlotsPtrInterface bodyPtrIfExpStoreContract typedCopyLayoutPtr
  storeSlotsPtrBytesCount exprSimProps assignBasePtrStorageExtent
  assignBasePtrStorageTypes assignBasePtrStorageDirect valueTypingMemoryProps vyperTyping
  valueEncoding valueEncodingDefs loweringPosts list arithmetic

Theorem store_slots_assignment_rhs_store_resources:
  body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env pre /\
  expr_body_pre cenv cx env e pre /\ supported_expr tops e /\
  supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
  (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
  type_stmt env ret (Assign target e) = SOME env' /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (expr_type e) sa sb es v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ eval_operand op s = SOME w ==>
  ?root. op = Var root /\ lookup_var root s = SOME w /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) /\
    w2n w + type_memory_size tv < dimword (:256)
Proof
  strip_tac >>
  drule_all store_slots_assignment_rhs_resources >> strip_tac >>
  drule_all assign_base_storage_rhs_footprint >> strip_tac >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  drule_all assign_base_typed_assignment_capacity_positive >> strip_tac >>
  `val_footprint tv v <> 0` by metis_tac[NOT_ZERO_LT_ZERO] >>
  fs[] >>
  `?p. op = Var p /\ ptr_covers G tn p s (val_store_size tv v)` by
    (irule ptr_val_ok_store_read_covers >> simp[] >>
     qexistsl_tac [`cx`, `tv`, `expr_type e`, `v`] >> simp[]) >>
  gvs[] >> metis_tac[]
QED

(* This equality includes partial final words: lengths 1, 31 and 33 do
   not require the unused bytes of their final word to be clean. *)
Theorem store_slots_bytestring_store_read_size:
  (val_store_size (BaseTV (BytesT (Dynamic cap))) (BytesV bs) =
     32 * ((LENGTH bs + 63) DIV 32)) /\
  (val_store_size (BaseTV (StringT cap)) (StringV str) =
     32 * ((LENGTH str + 63) DIV 32))
Proof
  simp[val_store_size_def, store_slots_bytestring_count_words, LEFT_ADD_DISTRIB]
QED

(* The offset resource runner accepts these containment bounds directly;
   robust representation is retained for the recursive call's control loads. *)
Theorem store_slots_tuple_child_read_resources:
  values_have_types tvs vs /\ i < LENGTH tvs /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    tuple_in_memory vs tvs addr m) ==>
  SUM (MAP type_memory_size (TAKE i tvs)) +
    val_store_size (EL i tvs) (EL i vs) <= SUM (MAP type_memory_size tvs) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (EL i tvs) (EL i vs)
      (addr + SUM (MAP type_memory_size (TAKE i tvs))) m)
Proof
  strip_tac >> conj_tac
  >- (irule tuple_child_store_size_contained >> simp[]) >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  metis_tac[tuple_in_memory_robust_element]
QED

Theorem store_slots_dynarray_child_read_resources:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  i < LENGTH vs /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) addr m) ==>
  32 + i * type_memory_size tv + val_store_size tv (EL i vs) <=
    val_store_size (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory tv (EL i vs) (addr + 32 + i * type_memory_size tv) m)
Proof
  strip_tac >> reverse conj_tac
  >- metis_tac[dynarray_in_memory_robust_element] >>
  fs[value_has_type_def, all_have_type_EVERY, EVERY_EL] >>
  `value_has_type tv (EL i vs)` by metis_tac[] >>
  `i < cap` by decide_tac >>
  drule_all array_child_store_size_contained >>
  disch_then (qspec_then `32` mp_tac) >>
  simp[val_store_size_def, type_memory_size_def]
QED

Theorem store_slots_sarray_child_read_resources:
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  i < cap /\
  v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) addr m) ==>
  i * type_memory_size tv + val_store_size tv v <=
    val_store_size (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory tv v (addr + i * type_memory_size tv) m)
Proof
  strip_tac >> reverse conj_tac
  >- metis_tac[sarray_in_memory_robust_element] >>
  `value_has_type tv v` by
    (Cases_on `ALOOKUP kvs i` >>
     gvs[value_has_type_def, default_value_well_typed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  drule_all array_child_store_size_contained >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[val_store_size_def, type_memory_size_def]
QED
