(* TOP-LEVEL: complete fixed-array layouts contain their source ABI bytes
   when the element type has a static ABI layout. The element theorem is
   reusable for dynamic-array payloads. Helpers: total byte-window splitting. *)
Theory memoryValueAbiArray
Ancestors
  sourceAbiArray memoryValueDefs memoryReadProps valueEncoding valueEncodingProofs
  vyperABI vyperValueOperation vyperValue vyperTyping vyperTypeDefaults
  vyperAssignPreservesType contractABI venomState
  list rich_list option alist arithmetic words

Theorem mem_bytes_at_split:
  !offset left_count right_count mem.
    mem_bytes_at offset (left_count + right_count) mem =
      mem_bytes_at offset left_count mem ++
      mem_bytes_at (offset + left_count) right_count mem
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`offset`, `left_count`, `right_count`,
    `(ARB:venom_state) with vs_memory := mem`] read_memory_split) >>
  simp[read_memory_eq_mem_bytes_at]
QED

Theorem mem_bytes_at_word:
  !offset mem.
    mem_bytes_at offset 32 mem = word_to_bytes (mem_word_at offset mem) T
Proof
  rpt gen_tac >> mp_tac (Q.SPECL [`offset`,
    `(ARB:venom_state) with vs_memory := mem`] read_memory_word) >>
  simp[read_memory_eq_mem_bytes_at, GSYM mem_word_at_eq_mload_proof]
QED

Theorem mem_bytes_at_chunks:
  !elem_count offset stride mem.
    mem_bytes_at offset (elem_count * stride) mem =
      FLAT (GENLIST (\i. mem_bytes_at (offset + i * stride) stride mem) elem_count)
Proof
  Induct_on `elem_count` >- simp[mem_bytes_at_def] >> rpt gen_tac >>
  `SUC elem_count * stride = elem_count * stride + stride` by
    simp[MULT_CLAUSES, ADD_COMM, MULT_COMM] >>
  qpat_x_assum `SUC elem_count * stride = _` (fn th => PURE_REWRITE_TAC [th]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [mem_bytes_at_split])) >>
  simp[GENLIST, FLAT_SNOC]
QED

Theorem memory_array_elements_bytes:
  !elem_type vs offset stride mem.
    (!i. i < LENGTH vs ==>
      mem_bytes_at (offset + i * stride) stride mem = enc elem_type (EL i vs)) ==>
    mem_bytes_at offset (LENGTH vs * stride) mem =
      FLAT (MAP (enc elem_type) vs)
Proof
  rpt strip_tac >> simp[mem_bytes_at_chunks] >>
  AP_TERM_TAC >> irule LIST_EQ >> simp[EL_GENLIST, EL_MAP]
QED

Theorem memory_array_elements_abi:
  !elem_type vs bound offset stride mem.
    ~is_dynamic elem_type /\
    (!i. i < LENGTH vs ==>
      mem_bytes_at (offset + i * stride) stride mem = enc elem_type (EL i vs)) ==>
    mem_bytes_at offset (LENGTH vs * stride) mem =
      enc (Array (SOME bound) elem_type) (ListV vs)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`elem_type`, `vs`, `offset`, `stride`, `mem`]
    memory_array_elements_bytes) >> impl_tac >- simp[] >>
  simp[enc_array_static_values]
QED

Definition memory_value_abi_def:
  memory_value_abi env ty tv <=>
    !v av offset mem.
      memory_value_rel tv v offset mem /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
      mem_bytes_at offset (type_memory_size tv) mem = enc (vyper_to_abi_type env ty) av
End

Theorem sparse_slot_has_type:
  !env ty tv sparse array_bound i.
    evaluate_type env ty = SOME tv /\ sparse_has_type tv array_bound sparse ==>
    value_has_type tv
      (case ALOOKUP sparse i of NONE => default_value tv | SOME v => v)
Proof
  rpt strip_tac >>
  `value_has_type tv (default_value tv)` by
    (drule default_value_has_type_thm >> simp[]) >>
  Cases_on `ALOOKUP sparse i` >> simp[] >>
  drule_all ALOOKUP_sparse_has_type >> simp[]
QED

Theorem memory_fixed_array_element_abi:
  !env ty tv sparse array_bound avs offset mem i.
    evaluate_type env ty = SOME tv /\ memory_value_abi env ty tv /\
    memory_value_rel (ArrayTV tv (Fixed array_bound)) (ArrayV (SArrayV sparse)) offset mem /\
    sparse_has_type tv array_bound sparse /\
    vyper_to_abi_sparse env ty tv array_bound sparse = SOME avs /\
    ~is_dynamic (vyper_to_abi_type env ty) /\ i < array_bound ==>
    LENGTH avs = array_bound /\
    mem_bytes_at (offset + i * type_memory_size tv) (type_memory_size tv) mem =
      enc (vyper_to_abi_type env ty) (EL i avs)
Proof
  rpt strip_tac >>
  `vyper_to_abi_same env ty
    (array_elements (ArrayTV tv (Fixed array_bound)) (SArrayV sparse)) = SOME avs` by
    (drule_then (qspecl_then [`array_bound`, `sparse`] mp_tac)
       vyper_to_abi_sparse_elements >> simp[]) >>
  drule vyper_to_abi_same_EL >>
  simp[array_elements_def] >> strip_tac >>
  `value_has_type tv
    (case ALOOKUP sparse i of NONE => default_value tv | SOME v => v)` by
    (mp_tac (Q.SPECL [`env`, `ty`, `tv`, `sparse`, `array_bound`, `i`]
       sparse_slot_has_type) >> impl_tac >- simp[] >> simp[]) >>
  qpat_x_assum `memory_value_abi env ty tv`
    (mp_tac o REWRITE_RULE [memory_value_abi_def]) >>
  disch_then (qspecl_then
    [`case ALOOKUP sparse i of NONE => default_value tv | SOME v => v`,
     `EL i avs`, `offset + i * type_memory_size tv`, `mem`] mp_tac) >>
  impl_tac >- fs[memory_value_rel_def] >> simp[]
QED

Theorem memory_fixed_array_abi:
  !env ty tv sparse array_bound avs offset mem.
    evaluate_type env ty = SOME tv /\ memory_value_abi env ty tv /\
    memory_value_rel (ArrayTV tv (Fixed array_bound)) (ArrayV (SArrayV sparse)) offset mem /\
    sparse_has_type tv array_bound sparse /\
    vyper_to_abi_sparse env ty tv array_bound sparse = SOME avs /\
    ~is_dynamic (vyper_to_abi_type env ty) ==>
    mem_bytes_at offset (array_bound * type_memory_size tv) mem =
      enc (Array (SOME array_bound) (vyper_to_abi_type env ty)) (ListV avs)
Proof
  rpt strip_tac >>
  `LENGTH avs = array_bound` by
    (`vyper_to_abi_same env ty
       (array_elements (ArrayTV tv (Fixed array_bound)) (SArrayV sparse)) = SOME avs` by
       (drule_then (qspecl_then [`array_bound`, `sparse`] mp_tac)
          vyper_to_abi_sparse_elements >> simp[]) >>
     drule vyper_to_abi_same_EL >> simp[array_elements_def]) >>
  mp_tac (Q.SPECL [`vyper_to_abi_type env ty`, `avs`, `array_bound`, `offset`,
    `type_memory_size tv`, `mem`] memory_array_elements_abi) >>
  impl_tac >- (simp[] >> rpt strip_tac >> drule_all memory_fixed_array_element_abi >> simp[]) >>
  simp[]
QED

Theorem memory_value_abi_fixed_array:
  !env ty tv array_bound.
    evaluate_type env ty = SOME tv /\ memory_value_abi env ty tv ==>
    memory_value_abi env (ArrayT ty (Fixed array_bound)) (ArrayTV tv (Fixed array_bound))
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [memory_value_abi_def] >> rpt gen_tac >>
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV array_value` >> Cases_on `array_value` >>
  simp[value_has_type_def, AllCaseEqs(), type_memory_size_def] >>
  rpt strip_tac >> drule_all memory_fixed_array_abi >> gvs[]
QED

Theorem memory_value_abi_array:
  !env ty tv array_bound.
    evaluate_type env ty = SOME tv /\ memory_value_abi env ty tv ==>
    memory_value_abi env (ArrayT ty array_bound) (ArrayTV tv array_bound)
Proof
  rpt strip_tac >> Cases_on `array_bound` >>
  FIRST [irule memory_value_abi_fixed_array >> simp[], simp[memory_value_abi_def]]
QED

Theorem memory_dynamic_array_element_abi:
  !env ty tv vs array_bound avs offset mem i.
    memory_value_abi env ty tv /\
    memory_value_rel (ArrayTV tv (Dynamic array_bound)) (ArrayV (DynArrayV vs)) offset mem /\
    all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs /\
    ~is_dynamic (vyper_to_abi_type env ty) /\ i < LENGTH vs ==>
    LENGTH avs = LENGTH vs /\
    mem_bytes_at (offset + 32 + i * type_memory_size tv) (type_memory_size tv) mem =
      enc (vyper_to_abi_type env ty) (EL i avs)
Proof
  rpt strip_tac >> drule vyper_to_abi_same_EL >> strip_tac >> simp[] >>
  qpat_x_assum `memory_value_abi env ty tv`
    (mp_tac o REWRITE_RULE [memory_value_abi_def]) >>
  disch_then (qspecl_then [`EL i vs`, `EL i avs`,
    `offset + 32 + i * type_memory_size tv`, `mem`] mp_tac) >>
  impl_tac >- fs[memory_value_rel_def, all_have_type_EVERY, EVERY_EL] >> simp[]
QED

Theorem memory_dynamic_array_abi:
  !env ty tv vs array_bound avs offset mem.
    memory_value_abi env ty tv /\
    memory_value_rel (ArrayTV tv (Dynamic array_bound)) (ArrayV (DynArrayV vs)) offset mem /\
    all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs /\
    ~is_dynamic (vyper_to_abi_type env ty) ==>
    mem_bytes_at offset (32 + LENGTH vs * type_memory_size tv) mem =
      enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)
Proof
  rpt strip_tac >>
  `LENGTH avs = LENGTH vs` by (drule vyper_to_abi_same_EL >> simp[]) >>
  `mem_bytes_at (offset + 32) (LENGTH avs * type_memory_size tv) mem =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)` by
    (irule memory_array_elements_bytes >> simp[] >> rpt strip_tac >>
     drule_all memory_dynamic_array_element_abi >> simp[]) >>
  `mem_word_at offset mem = n2w (LENGTH vs)` by fs[memory_value_rel_def] >>
  fs[enc_array_static_values, enc_dynamic_array_static_values,
    mem_bytes_at_split, mem_bytes_at_word] >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory/ABI array theorem: " ^ name)
  end) (DB.thms "memoryValueAbiArray")
