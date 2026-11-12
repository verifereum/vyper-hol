Theory extRetRobustSourceChildrenPtr
Ancestors abiEncoderSourceTransport representationCleanPtr valueEncoding valueEncodingProofs
  vyperValueOperation ptrDiscipline list rich_list arithmetic

(* These boundaries keep the Vyper child fixed.  They neither choose an ABI
   representative nor assert ownership of a fresh child allocation. *)
Theorem robust_dense_source_child:
  (!mem'. mem_agree_outside m mem mem' ==>
    elems_in_memory vs sb tv mem') /\ i < LENGTH vs ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv (EL i vs) (sb+i*type_memory_size tv) mem'
Proof
  rpt strip_tac >> irule abi_encoder_elems_memory >> simp[]
QED

Theorem robust_dynamic_source_child:
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) sb mem') /\
  i < LENGTH vs ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem'
Proof
  simp[val_in_memory_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule abi_encoder_elems_memory >>
  disch_then (qspec_then `i` mp_tac) >> simp[AC ADD_COMM ADD_ASSOC]
QED

Theorem robust_dynamic_source_length:
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) sb mem') ==>
  !mem'. mem_agree_outside m mem mem' ==>
    mem_word_at sb mem' = n2w (LENGTH vs)
Proof
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem robust_tuple_source_child:
  LENGTH vs = LENGTH tvs /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem') /\
  i < LENGTH tvs ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem'
Proof
  simp[val_in_memory_def] >> rpt strip_tac >>
  irule abi_encoder_tuple_memory >> simp[]
QED

Theorem robust_struct_source_child:
  LENGTH fields = LENGTH fts /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (StructTV fts) (StructV fields) sb mem') /\
  i < LENGTH fts ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (EL i (MAP SND fts)) (EL i (MAP SND fields))
      (sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))) mem'
Proof
  simp[val_in_memory_def, fields_in_memory_tuple] >> rpt strip_tac >>
  irule abi_encoder_tuple_memory >> simp[]
QED

Theorem robust_sparse_source_child:
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) sb mem') /\
  i < n ==>
  !mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv
      (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (sb+i*type_memory_size tv) mem'
Proof
  simp[val_in_memory_def, array_elements_def] >> rpt strip_tac >>
  Cases_on `ALOOKUP kvs i` >> gvs[] >>
  irule kvs_in_memory_lookup >> goal_assum (drule_at Any) >> simp[]
QED

Theorem robust_dynamic_source_length_clean:
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) sb mem') ==>
  !i. sb <= i /\ i < sb+32 ==> i NOTIN m
Proof
  strip_tac >> drule robust_dynamic_source_length >>
  disch_tac >> drule robust_mem_word_at_clean >> simp[]
QED
