(* Semantic interface for word-valued tuple and struct return slots. *)
Theory wordAggregateReturnSemantics
Ancestors stmtSimReturn assignTuplePtrLoadStep exprSimHypsDefs exprSimHyps
  valueEncodingProofs valueEncodingTyping tupleTypedLoad tupleMemoryLayout
  vyperTyping vyperTypeABI compileEnv valueEncoding vyperValue list bodyPtrDefs

Theorem word_aggregate_normalize[local]:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\ ets <> [] /\ value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v a m) ==>
  ?tenv tvs vs.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ets tvs /\
    values_have_types tvs vs /\
    type_memory_size tv = type_memory_size_list tvs /\
    (!m. mem_agree_outside tn.t_mem mem m ==> tuple_in_memory vs tvs a m) /\
    intret_vals_match tv v
      (MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs)))
Proof
  rpt strip_tac >> Cases_on `ty` >> gvs[]
  >~ [`TupleT tys`] >-
    (drule_all tuple_type_value >> strip_tac >> gvs[] >>
     qexistsl_tac [`get_tenv cx`, `tvs`, `vs`] >>
     simp[type_memory_size_def, val_in_memory_def, intret_vals_match_def] >>
     gvs[val_in_memory_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `struct_has_type _ vals` >>
  drule struct_has_type_values_have_types >> strip_tac >>
  qexistsl_tac [`get_tenv cx \\ p`, `tvs`, `MAP SND vals`] >>
  gvs[get_struct_fields_def, MAP_ZIP, type_memory_size_def,
      struct_layout_size_zip, intret_vals_match_def,
      val_in_memory_def, fields_in_memory_tuple]
QED

Theorem word_aggregate_return_words_match:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\ ets <> [] /\ EVERY is_word_type ets /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v (w2n bw) m) /\
  w2n bw + type_memory_size tv < dimword (:256) ==>
  intret_vals_match tv v (tuple_words ce bw ets 0 mem)
Proof
  strip_tac >> drule_all word_aggregate_normalize >> strip_tac >>
  `type_memory_size_list tvs = 32 * LENGTH ets` by
    metis_tac[word_tuple_size] >>
  `tuple_in_memory vs tvs (w2n bw) mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `tuple_words ce bw ets 0 mem =
    MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
    (irule tuple_words_typed >>
     conj_tac >- decide_tac >> simp[] >>
     qexists_tac `tenv` >> gvs[]) >>
  simp[]
QED

Theorem word_aggregate_return_ranges_clean:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\ ets <> [] /\ EVERY is_word_type ets /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v (w2n bw) m) /\
  w2n bw + type_memory_size tv < dimword (:256) ==>
  !i. i < LENGTH ets ==>
    w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 <= dimword (:256) /\
    (!j. w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) <= j /\
      j < w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 ==>
      j NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all word_aggregate_normalize >> strip_tac >>
  `LIST_REL (\t tv. type_memory_bytes ce t = type_memory_size tv) ets tvs` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     metis_tac[word_type_sizes]) >>
  gen_tac >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) (TAKE i ets)) =
   SUM (MAP type_memory_size (TAKE i tvs))` by
    metis_tac[tuple_prefix_sizes] >>
  `i < LENGTH tvs /\ is_word_type (EL i ets) /\
   evaluate_type tenv (EL i ets) = SOME (EL i tvs)` by
    fs[LIST_REL_EL_EQN, EVERY_EL] >>
  `type_memory_size (EL i tvs) = 32` by metis_tac[word_type_sizes] >>
  conj_tac
  >- (drule tuple_element_interval >>
      fs[type_memory_size_list_sum] >> decide_tac) >>
  metis_tac[tuple_word_member_clean]
QED

Theorem word_aggregate_return_extent:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\ ets <> [] /\ EVERY is_word_type ets /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v a m) ==>
  !i. i < LENGTH ets ==>
    SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 <= type_memory_size tv
Proof
  strip_tac >> drule_all word_aggregate_normalize >> strip_tac >>
  `LIST_REL (\t tv. type_memory_bytes ce t = type_memory_size tv) ets tvs` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     metis_tac[word_type_sizes]) >>
  gen_tac >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) (TAKE i ets)) =
   SUM (MAP type_memory_size (TAKE i tvs))` by
    metis_tac[tuple_prefix_sizes] >>
  `i < LENGTH tvs /\ is_word_type (EL i ets) /\
   evaluate_type tenv (EL i ets) = SOME (EL i tvs)` by
    fs[LIST_REL_EL_EQN, EVERY_EL] >>
  `type_memory_size (EL i tvs) = 32` by metis_tac[word_type_sizes] >>
  drule tuple_element_interval >>
  fs[type_memory_size_list_sum] >> decide_tac
QED
