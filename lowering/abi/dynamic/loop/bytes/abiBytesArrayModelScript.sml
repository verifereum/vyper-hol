(* TOP-LEVEL: byte/string array prefixes have one dynamic head per element
   and an accumulated tail size. These are the payloads used by the source ABI. *)
Theory abiBytesArrayModel
Ancestors
  abiDynamicArrayLayout abiFieldLayoutDefs contractABI list rich_list pair words arithmetic

Definition abi_bytes_array_fields_def:
  abi_bytes_array_fields bss = MAP (\bs. (T,enc (Bytes NONE) (contractABI$BytesV bs))) bss
End

Definition abi_bytes_array_tail_size_def:
  abi_bytes_array_tail_size bss = abi_field_tail_size (abi_bytes_array_fields bss)
End

Definition abi_bytes_array_data_size_def:
  abi_bytes_array_data_size bss = 32 * LENGTH bss + abi_bytes_array_tail_size bss
End

Theorem abi_bytes_array_fields_source:
  !bss. abi_bytes_array_fields bss = abi_dynamic_array_fields (Bytes NONE) (MAP contractABI$BytesV bss)
Proof
  simp[abi_bytes_array_fields_def, abi_dynamic_array_fields_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem abi_bytes_array_head_size:
  !bss. abi_field_head_size (abi_bytes_array_fields bss) = 32 * LENGTH bss
Proof
  simp[abi_bytes_array_fields_source, abi_dynamic_array_fields_head_size]
QED

Theorem abi_bytes_array_tail_nil[simp]:
  abi_bytes_array_tail_size [] = 0
Proof
  simp[abi_bytes_array_tail_size_def, abi_bytes_array_fields_def]
QED

Theorem abi_bytes_array_tail_cons:
  !bs bss.
    abi_bytes_array_tail_size (bs::bss) =
      LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) + abi_bytes_array_tail_size bss
Proof
  simp[abi_bytes_array_tail_size_def, abi_bytes_array_fields_def, abi_field_tail_def]
QED

Theorem abi_bytes_array_fields_prefix:
  !bss index. index < LENGTH bss ==>
    abi_bytes_array_fields (TAKE (SUC index) bss) =
      abi_bytes_array_fields (TAKE index bss) ++ [(T,enc (Bytes NONE) (contractABI$BytesV (EL index bss)))]
Proof
  rpt gen_tac >> DISCH_TAC >>
  `TAKE (SUC index) bss = SNOC (EL index bss) (TAKE index bss)` by
    (irule TAKE_SUC_BY_TAKE >> first_assum MATCH_ACCEPT_TAC) >>
  simp[SNOC_APPEND, abi_bytes_array_fields_def, MAP_APPEND]
QED

Theorem abi_bytes_array_tail_prefix:
  !bss index. index < LENGTH bss ==>
    abi_bytes_array_tail_size (TAKE (SUC index) bss) =
      abi_bytes_array_tail_size (TAKE index bss) +
      LENGTH (enc (Bytes NONE) (contractABI$BytesV (EL index bss)))
Proof
  rpt gen_tac >> DISCH_TAC >> drule abi_bytes_array_fields_prefix >> DISCH_TAC >>
  asm_simp_tac (srw_ss()) [abi_bytes_array_tail_size_def, abi_field_tail_size_append,
    abi_field_tail_def, abi_field_tails_def]
QED

Theorem abi_bytes_array_tail_take_bound:
  !bss index. abi_bytes_array_tail_size (TAKE index bss) <= abi_bytes_array_tail_size bss
Proof
  Induct_on `bss` >- simp[] >> Cases_on `index` >> simp[abi_bytes_array_tail_cons]
QED

Theorem abi_bytes_array_payload_bound:
  !bss index. index < LENGTH bss ==>
    abi_bytes_array_tail_size (TAKE index bss) +
      LENGTH (enc (Bytes NONE) (contractABI$BytesV (EL index bss))) <= abi_bytes_array_tail_size bss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`bss`, `SUC index`] abi_bytes_array_tail_take_bound) >>
  simp[abi_bytes_array_tail_prefix]
QED
