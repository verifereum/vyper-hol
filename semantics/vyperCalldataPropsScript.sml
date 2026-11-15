Theory vyperCalldataProps
Ancestors vyperCalldata arithmetic list

Theorem cd_decode_list_append:
  !ts us ofs. cd_decode_list nat cd (ts ++ us) base ofs =
    case cd_decode_list nat cd ts base ofs of
      NONE => NONE
    | SOME xs =>
      case cd_decode_list nat cd us base (ofs + SUM (MAP tv_abi_size ts)) of
        NONE => NONE
      | SOME ys => SOME (xs ++ ys)
Proof
  Induct >- (simp[cd_decode_def] >> rpt gen_tac >>
    Cases_on `cd_decode_list nat cd us base ofs` >> simp[]) >>
  simp[cd_decode_def] >> rpt gen_tac >>
  Cases_on `cd_decode nat cd h (cd_member_ptr nat cd h base ofs)` >>
  simp[] >>
  Cases_on `cd_decode_list nat cd ts base (ofs + tv_abi_size h)` >>
  simp[] >>
  Cases_on `cd_decode_list nat cd us base (ofs + (tv_abi_size h + SUM (MAP tv_abi_size ts)))` >>
  gvs[]
QED

Theorem cd_decode_elems_add:
  !n i k. cd_decode_elems nat cd t base i (n + k) =
    case cd_decode_elems nat cd t base i n of
      NONE => NONE
    | SOME xs =>
      case cd_decode_elems nat cd t base (i + n) k of
        NONE => NONE
      | SOME ys => SOME (xs ++ ys)
Proof
  Induct >- (simp[cd_decode_def] >> rpt gen_tac >>
    Cases_on `cd_decode_elems nat cd t base i k` >> simp[]) >>
  simp[cd_decode_def, ADD_CLAUSES] >> rpt gen_tac >>
  Cases_on `cd_decode nat cd t (cd_member_ptr nat cd t base (i * tv_abi_size t))` >>
  simp[] >>
  Cases_on `cd_decode_elems nat cd t base (i + 1) n` >>
  simp[ADD_CLAUSES, ADD_ASSOC] >>
  Cases_on `cd_decode_elems nat cd t base (i + SUC n) k` >> gvs[SUC_ONE_ADD]
QED

Theorem tv_abi_dynamic_list_exists:
  !ts. tv_abi_dynamic_list ts = EXISTS tv_abi_dynamic ts
Proof
  Induct >> simp[tv_abi_dynamic_def]
QED

Theorem tv_abi_dynamic_fields_map:
  !fs. tv_abi_dynamic_fields fs = tv_abi_dynamic_list (MAP SND fs)
Proof
  Induct >> simp[tv_abi_dynamic_def] >>
  Cases_on `h` >> simp[tv_abi_dynamic_def]
QED

Theorem tv_needs_clamp_list_exists:
  !ts. tv_needs_clamp_list ts = EXISTS tv_needs_clamp ts
Proof
  Induct >> simp[tv_needs_clamp_def]
QED

Theorem tv_needs_clamp_fields_map:
  !fs. tv_needs_clamp_fields fs = tv_needs_clamp_list (MAP SND fs)
Proof
  Induct >> simp[tv_needs_clamp_def] >>
  Cases_on `h` >> simp[tv_needs_clamp_def]
QED
