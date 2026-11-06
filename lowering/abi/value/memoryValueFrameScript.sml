(* TOP-LEVEL: complete memory layouts are stable under disjoint writes.
   Helpers: default values fit their type's memory footprint, including
   defaults represented by omitted fixed-array entries. *)
Theory memoryValueFrame
Ancestors
  memoryValueDefs valueEncoding valueEncodingProps valueEncodingProofs
  memoryReadProps venomState venomExecSemantics vyperValue list alist arithmetic pair
  typeValueInduction

Theorem default_base_val_wf:
  !bt. val_wf (BaseTV bt) (default_value (BaseTV bt))
Proof
  Cases_on `bt` >> simp[default_value_def, val_wf_def, type_memory_size_def] >>
  rename1 `val_wf (BaseTV (BytesT byte_bound)) _` >> Cases_on `byte_bound` >>
  simp[default_value_def, val_wf_def, type_memory_size_def]
QED

Theorem default_array_val_wf:
  !tv array_bound. val_wf (ArrayTV tv array_bound) (default_value (ArrayTV tv array_bound))
Proof
  rpt gen_tac >> Cases_on `array_bound` >> simp[default_value_def, val_wf_def]
QED

Theorem default_value_val_wf:
  (!tv. val_wf tv (default_value tv)) /\
  (!tvs. fields_val_wf (MAP (\(name,tv). (name,default_value tv)) tvs) tvs) /\
  (!p:string # type_value. val_wf (SND p) (default_value (SND p))) /\
  (!tvs. tuple_val_wf (MAP default_value tvs) tvs)
Proof
  ho_match_mp_tac type_value_mutual_induction >>
  simp[default_base_val_wf, default_array_val_wf,
    default_value_def, default_value_struct_MAP, default_value_tuple_MAP,
    val_wf_def, type_memory_size_def] >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `val_wf (SND field_entry) _` >>
  PairCases_on `field_entry` >> fs[val_wf_def]
QED

Theorem sparse_slot_val_wf:
  !sparse tv array_bound i.
    kvs_val_wf sparse tv array_bound ==>
    val_wf tv (case ALOOKUP sparse i of NONE => default_value tv | SOME v => v)
Proof
  Induct_on `sparse` >- simp[CONJUNCT1 default_value_val_wf] >>
  rpt gen_tac >> rename1 `kvs_val_wf (entry::rest) _ _` >>
  PairCases_on `entry` >> rw[val_wf_def, ALOOKUP_def] >>
  first_x_assum (qspecl_then [`tv`, `array_bound`, `i`] mp_tac) >> simp[]
QED

Theorem elems_val_wf_every:
  !vs tv. elems_val_wf vs tv <=> EVERY (val_wf tv) vs
Proof
  Induct_on `vs` >> simp[val_wf_def]
QED

Theorem memory_array_slot_agree:
  !offset header array_bound elem_size i mem mem'.
    i < array_bound /\
    mem_bytes_at offset (header + array_bound * elem_size) mem =
      mem_bytes_at offset (header + array_bound * elem_size) mem' ==>
    mem_bytes_at (offset + header + i * elem_size) elem_size mem =
      mem_bytes_at (offset + header + i * elem_size) elem_size mem'
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `header + array_bound * elem_size`, `mem`, `mem'`]
    mem_bytes_at_agree_window) >> impl_tac >- fs[] >> strip_tac >>
  `mem_bytes_at (offset + header) (array_bound * elem_size) mem' =
    mem_bytes_at (offset + header) (array_bound * elem_size) mem` by
    (qpat_x_assum `!off2 len2. _` (qspecl_then [`offset + header`, `array_bound * elem_size`] mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  mp_tac (Q.SPECL [`offset + header`, `array_bound`, `elem_size`, `i`, `mem'`, `mem`]
    mem_bytes_at_agree_slot) >> impl_tac >- fs[] >> simp[]
QED

Definition memory_value_frame_def:
  memory_value_frame tv <=>
    !v offset mem mem'.
      memory_value_rel tv v offset mem /\ val_wf tv v /\
      mem_bytes_at offset (type_memory_size tv) mem =
        mem_bytes_at offset (type_memory_size tv) mem' ==>
      memory_value_rel tv v offset mem'
End

Definition memory_fields_frame_def:
  memory_fields_frame tvs <=>
    !vs offset mem mem'.
      memory_fields_rel tvs vs offset mem /\ fields_val_wf vs tvs /\
      mem_bytes_at offset (type_memory_size_fields tvs) mem =
        mem_bytes_at offset (type_memory_size_fields tvs) mem' ==>
      memory_fields_rel tvs vs offset mem'
End

Definition memory_tuple_frame_def:
  memory_tuple_frame tvs <=>
    !vs offset mem mem'.
      memory_tuple_rel tvs vs offset mem /\ tuple_val_wf vs tvs /\
      mem_bytes_at offset (type_memory_size_list tvs) mem =
        mem_bytes_at offset (type_memory_size_list tvs) mem' ==>
      memory_tuple_rel tvs vs offset mem'
End

Theorem memory_value_frame_base:
  !bt. memory_value_frame (BaseTV bt)
Proof
  simp_tac bool_ss [memory_value_frame_def, memory_value_rel_def] >>
  rpt gen_tac >> DISCH_TAC >> irule (CONJUNCT1 val_in_memory_mem_agree_proof) >>
  conj_tac >- fs[] >> qexists_tac `mem` >> fs[]
QED

Theorem memory_value_frame_flag:
  !flag_width. memory_value_frame (FlagTV flag_width)
Proof
  simp_tac bool_ss [memory_value_frame_def, memory_value_rel_def] >>
  rpt gen_tac >> DISCH_TAC >> irule (CONJUNCT1 val_in_memory_mem_agree_proof) >>
  conj_tac >- fs[] >> qexists_tac `mem` >> fs[]
QED

Theorem memory_value_frame_none:
  memory_value_frame NoneTV
Proof
  simp_tac bool_ss [memory_value_frame_def] >>
  Cases_on `v` >> simp[memory_value_rel_def]
QED

Theorem memory_value_frame_fixed_array:
  !tv array_bound.
    memory_value_frame tv ==> memory_value_frame (ArrayTV tv (Fixed array_bound))
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_value_frame_def] >>
  rpt gen_tac >> Cases_on `v` >> simp[memory_value_rel_def] >>
  rename1 `memory_value_rel _ (ArrayV array_value) _ _` >>
  Cases_on `array_value` >> simp[memory_value_rel_def] >>
  rename1 `ALOOKUP sparse _` >> rpt strip_tac >>
  rename1 `i < array_bound` >>
  `val_wf tv (case ALOOKUP sparse i of NONE => default_value tv | SOME value => value)` by
    (mp_tac (Q.SPECL [`sparse`, `tv`, `array_bound`, `i`] sparse_slot_val_wf) >>
     fs[val_wf_def]) >>
  `mem_bytes_at (offset + i * type_memory_size tv) (type_memory_size tv) mem =
    mem_bytes_at (offset + i * type_memory_size tv) (type_memory_size tv) mem'` by
    (mp_tac (Q.SPECL [`offset`, `0`, `array_bound`, `type_memory_size tv`, `i`, `mem`, `mem'`]
       memory_array_slot_agree) >> impl_tac >- fs[type_memory_size_def] >> simp[]) >>
  qpat_x_assum `memory_value_frame tv`
    (mp_tac o REWRITE_RULE [memory_value_frame_def]) >>
  disch_then (qspecl_then
    [`case ALOOKUP sparse i of NONE => default_value tv | SOME value => value`,
     `offset + i * type_memory_size tv`, `mem`, `mem'`] mp_tac) >>
  impl_tac >- fs[memory_value_rel_def] >> simp[]
QED

Theorem memory_word_agree:
  !offset whole_len mem mem'.
    32 <= whole_len /\ mem_bytes_at offset whole_len mem = mem_bytes_at offset whole_len mem' ==>
    mem_word_at offset mem = mem_word_at offset mem'
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `whole_len`, `mem'`, `mem`] mem_bytes_at_agree_window) >>
  impl_tac >- fs[] >> strip_tac >>
  qpat_x_assum `!off2. _` (qspec_then `offset` mp_tac) >>
  impl_tac >- (fs[] >> decide_tac) >> simp[]
QED

Theorem memory_value_frame_dynamic_array:
  !tv array_bound.
    memory_value_frame tv ==> memory_value_frame (ArrayTV tv (Dynamic array_bound))
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_value_frame_def] >>
  rpt gen_tac >> Cases_on `v` >> simp[memory_value_rel_def] >>
  rename1 `memory_value_rel _ (ArrayV array_value) _ _` >>
  Cases_on `array_value` >> simp[memory_value_rel_def] >>
  rename1 `LENGTH vs` >> DISCH_TAC >> conj_tac
  >- (mp_tac (Q.SPECL [`offset`, `32 + array_bound * type_memory_size tv`, `mem`, `mem'`]
        memory_word_agree) >> impl_tac >- fs[type_memory_size_def] >>
      DISCH_TAC >> fs[]) >>
  qx_gen_tac `i` >> DISCH_TAC >>
  `val_wf tv (EL i vs)` by fs[val_wf_def, elems_val_wf_every, EVERY_EL] >>
  `mem_bytes_at (offset + 32 + i * type_memory_size tv) (type_memory_size tv) mem =
    mem_bytes_at (offset + 32 + i * type_memory_size tv) (type_memory_size tv) mem'` by
    (mp_tac (Q.SPECL [`offset`, `32`, `array_bound`, `type_memory_size tv`, `i`, `mem`, `mem'`]
       memory_array_slot_agree) >>
     impl_tac >- (fs[val_wf_def, type_memory_size_def] >> decide_tac) >> simp[]) >>
  qpat_x_assum `memory_value_frame tv`
    (mp_tac o REWRITE_RULE [memory_value_frame_def]) >>
  disch_then (qspecl_then [`EL i vs`, `offset + 32 + i * type_memory_size tv`, `mem`, `mem'`] mp_tac) >>
  impl_tac >- fs[memory_value_rel_def] >> simp[]
QED

Theorem memory_pair_agree:
  !offset left_len right_len mem mem'.
    mem_bytes_at offset (left_len + right_len) mem =
      mem_bytes_at offset (left_len + right_len) mem' ==>
    mem_bytes_at offset left_len mem = mem_bytes_at offset left_len mem' /\
    mem_bytes_at (offset + left_len) right_len mem = mem_bytes_at (offset + left_len) right_len mem'
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `left_len + right_len`, `mem'`, `mem`]
    mem_bytes_at_agree_window) >> impl_tac >- fs[] >> strip_tac >> conj_tac
  >- (qpat_x_assum `!off2 len2. _` (qspecl_then [`offset`, `left_len`] mp_tac) >>
      impl_tac >- decide_tac >> simp[]) >>
  qpat_x_assum `!off2 len2. _` (qspecl_then [`offset + left_len`, `right_len`] mp_tac) >>
  impl_tac >- decide_tac >> simp[]
QED

Theorem memory_value_frame_struct:
  !tvs. memory_fields_frame tvs ==> memory_value_frame (StructTV tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_value_frame_def] >>
  rpt gen_tac >> Cases_on `v` >>
  simp[memory_value_rel_def, val_wf_def, type_memory_size_def] >>
  rename1 `memory_fields_rel tvs fields _ _` >> DISCH_TAC >>
  qpat_x_assum `memory_fields_frame tvs`
    (mp_tac o REWRITE_RULE [memory_fields_frame_def]) >>
  disch_then (qspecl_then [`fields`, `offset`, `mem`, `mem'`] mp_tac) >>
  impl_tac >- fs[] >> simp[]
QED

Theorem memory_value_frame_tuple:
  !tvs. memory_tuple_frame tvs ==> memory_value_frame (TupleTV tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_value_frame_def] >>
  rpt gen_tac >> Cases_on `v` >> simp[memory_value_rel_def] >>
  rename1 `memory_value_rel _ (ArrayV array_value) _ _` >>
  Cases_on `array_value` >>
  simp[memory_value_rel_def, val_wf_def, type_memory_size_def] >>
  rename1 `memory_tuple_rel tvs vs _ _` >> DISCH_TAC >>
  qpat_x_assum `memory_tuple_frame tvs`
    (mp_tac o REWRITE_RULE [memory_tuple_frame_def]) >>
  disch_then (qspecl_then [`vs`, `offset`, `mem`, `mem'`] mp_tac) >>
  impl_tac >- fs[] >> simp[]
QED

Theorem memory_fields_frame_nil:
  memory_fields_frame []
Proof
  simp_tac bool_ss [memory_fields_frame_def] >>
  Cases_on `vs` >> simp[memory_value_rel_def]
QED

Theorem memory_tuple_frame_nil:
  memory_tuple_frame []
Proof
  simp_tac bool_ss [memory_tuple_frame_def] >>
  Cases_on `vs` >> simp[memory_value_rel_def]
QED

Theorem memory_fields_frame_cons:
  !field_name tv tvs.
    memory_value_frame tv /\ memory_fields_frame tvs ==>
    memory_fields_frame ((field_name,tv)::tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_fields_frame_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[memory_value_rel_def] >>
  rename1 `memory_fields_rel _ (entry::rest) _ _` >> PairCases_on `entry` >>
  simp[memory_value_rel_def, val_wf_def, type_memory_size_def] >>
  rename1 `memory_value_rel tv field_value offset _` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `type_memory_size tv`, `type_memory_size_fields tvs`, `mem`, `mem'`]
    memory_pair_agree) >> impl_tac >- fs[] >> strip_tac >>
  `memory_value_rel tv field_value offset mem'` by
    (qpat_x_assum `memory_value_frame tv /\ _`
       (mp_tac o REWRITE_RULE [memory_value_frame_def] o CONJUNCT1) >>
     disch_then (qspecl_then [`field_value`, `offset`, `mem`, `mem'`] mp_tac) >>
     impl_tac >- fs[] >> simp[]) >>
  `memory_fields_rel tvs rest (offset + type_memory_size tv) mem'` by
    (qpat_x_assum `_ /\ memory_fields_frame tvs`
       (mp_tac o REWRITE_RULE [memory_fields_frame_def] o CONJUNCT2) >>
     disch_then (qspecl_then [`rest`, `offset + type_memory_size tv`, `mem`, `mem'`] mp_tac) >>
     impl_tac >- fs[] >> simp[]) >>
  fs[]
QED

Theorem memory_tuple_frame_cons:
  !tv tvs.
    memory_value_frame tv /\ memory_tuple_frame tvs ==>
    memory_tuple_frame (tv::tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [memory_tuple_frame_def] >>
  rpt gen_tac >> Cases_on `vs` >>
  simp[memory_value_rel_def, val_wf_def, type_memory_size_def] >>
  rename1 `memory_value_rel tv value offset _` >>
  rename1 `memory_tuple_rel tvs rest _ _` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `type_memory_size tv`, `type_memory_size_list tvs`, `mem`, `mem'`]
    memory_pair_agree) >> impl_tac >- fs[] >> strip_tac >>
  `memory_value_rel tv value offset mem'` by
    (qpat_x_assum `memory_value_frame tv /\ _`
       (mp_tac o REWRITE_RULE [memory_value_frame_def] o CONJUNCT1) >>
     disch_then (qspecl_then [`value`, `offset`, `mem`, `mem'`] mp_tac) >>
     impl_tac >- fs[] >> simp[]) >>
  `memory_tuple_rel tvs rest (offset + type_memory_size tv) mem'` by
    (qpat_x_assum `_ /\ memory_tuple_frame tvs`
       (mp_tac o REWRITE_RULE [memory_tuple_frame_def] o CONJUNCT2) >>
     disch_then (qspecl_then [`rest`, `offset + type_memory_size tv`, `mem`, `mem'`] mp_tac) >>
     impl_tac >- fs[] >> simp[]) >>
  fs[]
QED

Theorem memory_value_frame_array:
  !tv array_bound.
    memory_value_frame tv ==> memory_value_frame (ArrayTV tv array_bound)
Proof
  rpt gen_tac >> Cases_on `array_bound` >>
  simp[memory_value_frame_fixed_array, memory_value_frame_dynamic_array]
QED

Theorem memory_value_frames:
  (!tv. memory_value_frame tv) /\
  (!tvs. memory_fields_frame tvs) /\
  (!p:string # type_value. memory_value_frame (SND p)) /\
  (!tvs. memory_tuple_frame tvs)
Proof
  ho_match_mp_tac type_value_mutual_induction >>
  simp[memory_value_frame_base, memory_value_frame_flag, memory_value_frame_none,
    memory_value_frame_array, memory_value_frame_struct, memory_value_frame_tuple,
    memory_fields_frame_nil, memory_fields_frame_cons,
    memory_tuple_frame_nil, memory_tuple_frame_cons] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `memory_value_frame (SND field_entry)` >>
  PairCases_on `field_entry` >> fs[memory_fields_frame_cons]
QED

Theorem memory_value_rel_mem_agree =
  CONJUNCT1 memory_value_frames |> REWRITE_RULE [memory_value_frame_def];

Theorem memory_fields_rel_mem_agree =
  CONJUNCT1 (CONJUNCT2 memory_value_frames) |> REWRITE_RULE [memory_fields_frame_def];

Theorem memory_tuple_rel_mem_agree =
  CONJUNCT2 (CONJUNCT2 (CONJUNCT2 memory_value_frames)) |>
    REWRITE_RULE [memory_tuple_frame_def];

Theorem memory_value_rel_mem_agree_region:
  !tv v offset len mem mem'.
    memory_value_rel tv v offset mem /\ val_wf tv v /\
    type_memory_size tv <= len /\
    mem_bytes_at offset len mem = mem_bytes_at offset len mem' ==>
    memory_value_rel tv v offset mem'
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`offset`, `len`, `mem'`, `mem`] mem_bytes_at_agree_window) >>
  impl_tac >- fs[] >> strip_tac >>
  `mem_bytes_at offset (type_memory_size tv) mem =
    mem_bytes_at offset (type_memory_size tv) mem'` by
    (qpat_x_assum `!off2 len2. _`
       (qspecl_then [`offset`, `type_memory_size tv`] mp_tac) >>
     impl_tac >- (fs[] >> decide_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `mem`, `mem'`] memory_value_rel_mem_agree) >>
  impl_tac >- fs[] >> simp[]
QED

Theorem mstore_preserves_memory_value_rel:
  !tv v offset dst value ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= dst \/ dst + 32 <= offset) ==>
    memory_value_rel tv v offset (mstore dst value ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  `mem_bytes_at offset (type_memory_size tv) ss.vs_memory =
    mem_bytes_at offset (type_memory_size tv) (mstore dst value ss).vs_memory` by
    (sym_tac >> irule mstore_mem_bytes_at_disjoint >> fs[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `ss.vs_memory`, `(mstore dst value ss).vs_memory`]
    memory_value_rel_mem_agree) >> impl_tac >- fs[] >> simp[]
QED

Theorem mcopy_preserves_memory_value_rel:
  !tv v offset dst src copied_count ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (copied_count = 0 \/ offset + type_memory_size tv <= dst \/
      dst + copied_count <= offset) ==>
    memory_value_rel tv v offset (mcopy dst src copied_count ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory offset (type_memory_size tv) (mcopy dst src copied_count ss) =
    read_memory offset (type_memory_size tv) ss` by
    (irule read_memory_mcopy_frame >> fs[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `offset`, `ss.vs_memory`,
    `(mcopy dst src copied_count ss).vs_memory`] memory_value_rel_mem_agree) >>
  impl_tac >- fs[read_memory_eq_mem_bytes_at] >> simp[]
QED
