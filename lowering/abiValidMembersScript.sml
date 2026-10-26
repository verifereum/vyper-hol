(* Source-valid member views, shared by tuples, structs and both array kinds.
   TOP-LEVEL: abi_valid_members_view, abi_valid_members_suffix.
   Helpers: actual member slices and accumulator-independent decoded lists. *)
Theory abiValidMembers
Ancestors
  abiDecodeRanges vyperABI contractABI words list rich_list arithmetic

Definition abi_decode_member_bytes_def:
  abi_decode_member_bytes at base hds =
    if is_dynamic at then DROP (abi_head_word hds) base else TAKE (static_length at) hds
End

Definition abi_decode_members_def:
  abi_decode_members [] base hds = [] /\
  abi_decode_members (at::ats) base hds =
    dec at (abi_decode_member_bytes at base hds) ::
      abi_decode_members ats base (DROP (abi_member_head_size at) hds)
End

Theorem abi_decode_members_length[simp]:
  !ats base hds. LENGTH (abi_decode_members ats base hds) = LENGTH ats
Proof
  Induct >> simp[abi_decode_members_def]
QED

Theorem abi_decode_members_value:
  !ats base hds acc.
  dec_tuple ats base hds acc = ListV (REVERSE acc ++ abi_decode_members ats base hds)
Proof
  Induct >- simp[Once dec_def, abi_decode_members_def] >>
  qx_gen_tac `at` >> rpt gen_tac >>
  simp_tac bool_ss [Once dec_def, abi_decode_members_def, LET_THM] >>
  Cases_on `is_dynamic at` >>
  asm_simp_tac bool_ss [abi_decode_member_bytes_def, abi_member_head_size_def,
    GSYM abi_head_word_def, LET_THM, REVERSE_DEF, GSYM APPEND_ASSOC, APPEND]
QED

Theorem abi_decode_members_append:
  !pre ats base hds.
  abi_decode_members (pre ++ ats) base hds =
    abi_decode_members pre base hds ++
      abi_decode_members ats base (DROP (SUM (MAP abi_member_head_size pre)) hds)
Proof
  Induct >- simp[abi_decode_members_def, Excl "dec_def"] >> rpt gen_tac >>
  asm_simp_tac bool_ss [abi_decode_members_def, APPEND, MAP, SUM, DROP_DROP_T, ADD_COMM]
QED

Theorem abi_valid_member_cons:
  valid_enc_tuple (at::ats) base hds ==>
  abi_member_head_size at <= LENGTH hds /\
  valid_enc at (abi_decode_member_bytes at base hds) /\
  valid_enc_tuple ats base (DROP (abi_member_head_size at) hds)
Proof
  Cases_on `is_dynamic at` >>
  asm_simp_tac bool_ss [Once valid_enc_def, abi_decode_member_bytes_def,
    abi_member_head_size_def, GSYM abi_head_word_def, LET_THM] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_members_view:
  !ats base hds. valid_enc_tuple ats base hds ==>
  SUM (MAP abi_member_head_size ats) <= LENGTH hds /\
  has_types ats (abi_decode_members ats base hds)
Proof
  Induct >- simp[Once valid_enc_def, abi_decode_members_def, Once has_type_def] >>
  rpt gen_tac >> strip_tac >> drule abi_valid_member_cons >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all (cj 1 dec_has_type) >> strip_tac >>
  conj_tac >- (fs[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_decode_members_def, Once has_type_def]
QED

Theorem abi_valid_members_suffix:
  !pre ats base hds. valid_enc_tuple (pre ++ ats) base hds ==>
  SUM (MAP abi_member_head_size pre) <= LENGTH hds /\
  valid_enc_tuple ats base (DROP (SUM (MAP abi_member_head_size pre)) hds)
Proof
  Induct >- simp[] >> rpt gen_tac >> simp_tac bool_ss [APPEND] >> strip_tac >>
  drule abi_valid_member_cons >> strip_tac >> first_x_assum drule >> strip_tac >>
  asm_simp_tac (srw_ss()) [DROP_DROP_T, ADD_COMM, Excl "valid_enc_def"] >>
  fs[LENGTH_DROP, DROP_DROP_T, Excl "valid_enc_def", Excl "dec_def", Excl "enc_def"] >> decide_tac
QED

Theorem abi_valid_tuple_view:
  valid_enc (Tuple ats) bs ==>
  dec (Tuple ats) bs = ListV (abi_decode_members ats bs bs) /\
  LENGTH (abi_decode_members ats bs bs) = LENGTH ats /\
  has_types ats (abi_decode_members ats bs bs) /\
  SUM (MAP abi_member_head_size ats) <= LENGTH bs
Proof
  simp_tac bool_ss [Once valid_enc_def] >> strip_tac >>
  drule abi_valid_members_view >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once dec_def, abi_decode_members_value,
    Excl "dec_def", Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_MEMBERS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid member views not kernel closed: " ^ n)
  end) (DB.thms "abiValidMembers");
