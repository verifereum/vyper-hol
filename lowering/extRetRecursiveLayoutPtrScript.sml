Theory extRetRecursiveLayoutPtr
Ancestors
  extRetRobustSourceChildrenPtr abiEncoderInput abiDecoderArraySlice
  valueEncoding valueEncodingProofs vyperValue vyperTyping vyperValueOperation
  vyperTypeABI vyperTypeDefaults
  ptrDiscipline list rich_list arithmetic words

(* Offset and capacity facts are about evaluated layouts.  No positive
   stride or exclusion of NoneTV is needed. *)
Theorem encoder_child_capacity:
  k+n <= cap /\ b+cap < dimword(:256) ==>
  b+k+n < dimword(:256) /\ n <= cap-k
Proof
  decide_tac
QED

Theorem encoder_tuple_source_window:
  LENGTH vs = LENGTH tvs /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem') /\
  i < LENGTH tvs ==>
  (sb+SUM (MAP type_memory_size (TAKE i tvs))) +
    type_memory_size (EL i tvs) <= sb+type_memory_size (TupleTV tvs) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem')
Proof
  strip_tac >> conj_tac >-
    (drule abi_encoder_prefix_sum_bound >>
     disch_then (qspec_then `type_memory_size` mp_tac) >>
     simp[type_memory_size_def, type_memory_size_list_sum]) >>
  metis_tac[robust_tuple_source_child]
QED

Theorem encoder_struct_source_window:
  LENGTH fields = LENGTH fts /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (StructTV fts) (StructV fields) sb mem') /\
  i < LENGTH fts ==>
  (sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))) +
    type_memory_size (EL i (MAP SND fts)) <= sb+type_memory_size (StructTV fts) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (EL i (MAP SND fts)) (EL i (MAP SND fields))
      (sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))) mem')
Proof
  strip_tac >> conj_tac >-
    (`i < LENGTH (MAP SND fts)` by simp[] >>
     drule abi_encoder_prefix_sum_bound >>
     disch_then (qspec_then `type_memory_size` mp_tac) >>
     simp[type_memory_size_def, type_memory_size_fields_sum, MAP_MAP_o]) >>
  metis_tac[robust_struct_source_child]
QED

Theorem encoder_dense_source_window:
  (!mem'. mem_agree_outside m mem mem' ==> elems_in_memory vs sb tv mem') /\
  i < LENGTH vs ==>
  sb+i*type_memory_size tv+type_memory_size tv <= sb+LENGTH vs*type_memory_size tv /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv (EL i vs) (sb+i*type_memory_size tv) mem')
Proof
  strip_tac >> conj_tac >-
    (`i*type_memory_size tv+type_memory_size tv <= LENGTH vs*type_memory_size tv`
       by (irule abi_decoder_array_cell_capacity >> simp[]) >> decide_tac) >>
  metis_tac[robust_dense_source_child]
QED

Theorem encoder_dynamic_source_window:
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) sb mem') /\
  i < LENGTH vs ==>
  sb+32+i*type_memory_size tv+type_memory_size tv <=
    sb+type_memory_size (ArrayTV tv (Dynamic n)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem')
Proof
  strip_tac >> conj_tac >-
    (`i < n` by fs[value_has_type_def] >>
     `i*type_memory_size tv+type_memory_size tv <= n*type_memory_size tv`
       by (irule abi_decoder_array_cell_capacity >> simp[]) >>
     simp[type_memory_size_def] >> decide_tac) >>
  metis_tac[robust_dynamic_source_child]
QED

Theorem encoder_sparse_source_window:
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) sb mem') /\
  i < n ==>
  sb+i*type_memory_size tv+type_memory_size tv <=
    sb+type_memory_size (ArrayTV tv (Fixed n)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv
      (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (sb+i*type_memory_size tv) mem')
Proof
  strip_tac >> conj_tac >-
    (`i*type_memory_size tv+type_memory_size tv <= n*type_memory_size tv`
       by (irule abi_decoder_array_cell_capacity >> simp[]) >>
     simp[type_memory_size_def] >> decide_tac) >>
  metis_tac[robust_sparse_source_child]
QED

Theorem encoder_evaluated_tuple_child:
  evaluate_type env (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem') /\
  i < LENGTH tys ==>
  evaluate_type env (EL i tys) = SOME (EL i tvs) /\
  value_has_type (EL i tvs) (EL i vs) /\
  sb+SUM (MAP type_memory_size (TAKE i tvs))+type_memory_size (EL i tvs) <=
    sb+type_memory_size (TupleTV tvs) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem')
Proof
  strip_tac >>
  `evaluate_types env tys [] = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `values_have_types tvs vs` by fs[value_has_type_def] >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `i < LENGTH tvs` by simp[] >>
  drule_all encoder_tuple_source_window >> simp[]
QED

Theorem encoder_layout_none_regressions:
  type_memory_size (TupleTV []) = 0 /\
  type_memory_size (StructTV []) = 0 /\
  type_memory_size (ArrayTV NoneTV (Fixed 3)) = 0 /\
  type_memory_size (ArrayTV NoneTV (Dynamic 3)) = 32 /\
  SUM (MAP type_memory_size (TAKE 1 [NoneTV; BaseTV (UintT 256)])) = 0 /\
  type_memory_size (TupleTV [NoneTV; BaseTV (UintT 256)]) = 32
Proof
  EVAL_TAC
QED

Theorem encoder_evaluated_struct_children:
  evaluate_type env (StructT nsid) = SOME (StructTV fts) /\
  value_has_type (StructTV fts) (StructV fields) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (StructTV fts) (StructV fields) sb mem') ==>
  ?args.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    LENGTH args = LENGTH fts /\ LENGTH fields = LENGTH fts /\
    !i. i < LENGTH fts ==>
      evaluate_type (env \\ nsid) (EL i (MAP SND args)) =
        SOME (EL i (MAP SND fts)) /\
      value_has_type (EL i (MAP SND fts)) (EL i (MAP SND fields)) /\
      sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))+
        type_memory_size (EL i (MAP SND fts)) <= sb+type_memory_size (StructTV fts) /\
      (!mem'. mem_agree_outside m mem mem' ==>
        val_in_memory (EL i (MAP SND fts)) (EL i (MAP SND fields))
          (sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))) mem')
Proof
  strip_tac >>
  `?args tvs. FLOOKUP env nsid = SOME (StructArgs args) /\
     evaluate_types (env \\ nsid) (MAP SND args) [] = SOME tvs /\
     fts = ZIP (MAP FST args,tvs)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> simp[LIST_REL_EL_EQN] >> strip_tac >>
  `MAP SND fts = tvs /\ LENGTH fts = LENGTH args` by
    simp[MAP_ZIP, LENGTH_ZIP] >>
  `values_have_types (MAP SND fts) (MAP SND fields)` by
    (irule struct_has_type_values_have_types >> fs[value_has_type_def]) >>
  `LENGTH fields = LENGTH fts` by
    (drule values_have_types_length >> simp[]) >>
  simp[GSYM MAP_ZIP] >> rpt strip_tac >>
  `i < LENGTH fts` by simp[] >>
  `value_has_type (EL i (MAP SND fts)) (EL i (MAP SND fields))` by
    fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  drule_all encoder_struct_source_window >> gvs[MAP_ZIP]
QED
