(* TOP-LEVEL: physical aggregate layout has separate head and tail windows.
   Exact cons and append rules compose completed fields and suffix traversal;
   a complete layout yields the contiguous source ABI encoding. *)
Theory abiFieldMemory
Ancestors
  abiFieldLayoutDefs abiFieldSource abiMemoryFrame memoryReadProps
  compileEnv venomState list pair rich_list words arithmetic

Definition abi_fields_layout_def:
  abi_fields_layout fields base head_offset tail_offset (ss:venom_state) <=>
    read_memory (base + head_offset) (abi_field_head_size fields) ss = abi_field_heads tail_offset fields /\
    read_memory (base + tail_offset) (abi_field_tail_size fields) ss = abi_field_tails fields
End

Theorem abi_fields_layout_memory:
  !fields base head_offset tail_offset before after.
    after.vs_memory = before.vs_memory ==>
    (abi_fields_layout fields base head_offset tail_offset after =
      abi_fields_layout fields base head_offset tail_offset before)
Proof
  simp[abi_fields_layout_def, read_memory_def]
QED

Theorem abi_fields_layout_nil[simp]:
  !base head_offset tail_offset ss. abi_fields_layout [] base head_offset tail_offset ss
Proof
  simp[abi_fields_layout_def, abi_field_head_size_def, abi_field_heads_def, abi_field_tails_def,
    read_memory_def]
QED

Theorem abi_fields_layout_cons:
  !is_dyn payload fields base head_offset tail_offset ss.
    abi_fields_layout ((is_dyn,payload)::fields) base head_offset tail_offset ss <=>
    read_memory (base + head_offset) (LENGTH (abi_field_head tail_offset is_dyn payload)) ss =
      abi_field_head tail_offset is_dyn payload /\
    read_memory (base + tail_offset) (LENGTH (abi_field_tail is_dyn payload)) ss = abi_field_tail is_dyn payload /\
    abi_fields_layout fields base
      (head_offset + LENGTH (abi_field_head tail_offset is_dyn payload))
      (tail_offset + LENGTH (abi_field_tail is_dyn payload)) ss
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_fields_layout_def, abi_field_head_size_def,
    abi_field_heads_def, abi_field_tails_def, read_memory_split, ADD_ASSOC,
    APPEND_11_LENGTH, abi_field_tail_size_def] >>
  metis_tac[]
QED

Theorem abi_fields_layout_append:
  !left right base head_offset tail_offset ss.
    abi_fields_layout (left ++ right) base head_offset tail_offset ss <=>
    abi_fields_layout left base head_offset tail_offset ss /\
    abi_fields_layout right base (head_offset + abi_field_head_size left)
      (tail_offset + abi_field_tail_size left) ss
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_fields_layout_def, abi_field_head_size_append,
    abi_field_tail_size_append, abi_field_heads_append, abi_field_tails_append,
    read_memory_split, ADD_ASSOC, APPEND_11_LENGTH, abi_field_tail_size_def] >>
  metis_tac[]
QED

Theorem abi_fields_layout_contiguous:
  !fields base ss.
    abi_fields_layout fields base 0 (abi_field_head_size fields) ss ==>
    read_memory base (LENGTH (abi_field_bytes (abi_field_head_size fields) fields)) ss =
      abi_field_bytes (abi_field_head_size fields) fields
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_fields_layout_def, abi_field_bytes_def,
    abi_field_tail_size_def] >> strip_tac >>
  asm_simp_tac (srw_ss()) [read_memory_split]
QED

Theorem abi_fields_layout_source_tuple:
  !tys vs base ss.
    LIST_REL (\ty v. ~contractABI$is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) tys vs /\
    abi_fields_layout (MAP2 (\ty v. (contractABI$is_dynamic ty, enc ty v)) tys vs) base 0
      (abi_field_head_size (MAP2 (\ty v. (contractABI$is_dynamic ty, enc ty v)) tys vs)) ss ==>
    read_memory base (LENGTH (enc (Tuple tys) (ListV vs))) ss = enc (Tuple tys) (ListV vs)
Proof
  rpt gen_tac >> strip_tac >> drule_all enc_tuple_head_size >> DISCH_TAC >>
  drule_all abi_fields_layout_contiguous >> simp[]
QED

Theorem abi_fields_layout_frame:
  !fields base head_offset tail_offset writes before after.
    abi_fields_layout fields base head_offset tail_offset before /\ abi_memory_frame writes before after /\
    EVERY (\(offset,byte_count). abi_window_separated (base + head_offset) (abi_field_head_size fields)
      offset byte_count) writes /\
    EVERY (\(offset,byte_count). abi_window_separated (base + tail_offset) (abi_field_tail_size fields)
      offset byte_count) writes ==>
    abi_fields_layout fields base head_offset tail_offset after
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `abi_fields_layout fields arena head_offset tail_offset before` >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `arena + head_offset`, `abi_field_head_size fields`]
    abi_memory_frame_read) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `arena + tail_offset`, `abi_field_tail_size fields`]
    abi_memory_frame_read) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  fs[abi_fields_layout_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed physical ABI field composition: " ^ name)
  end) (DB.thms "abiFieldMemory")
