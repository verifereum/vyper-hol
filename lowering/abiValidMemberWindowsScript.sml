(* Actual source loads and bounded child windows for noncanonical members. *)
Theory abiValidMemberWindows
Ancestors
  abiValidMembers abiValidAggregateHeads abiCanonicalLoad abiCanonicalArrayLoad
  abiDecodeRanges abiDecoderContract vyperABI contractABI valueEncoding
  venomState words list rich_list arithmetic

Definition abi_decode_member_offset_def:
  abi_decode_member_offset at bs ao =
    if is_dynamic at then abi_head_word (DROP ao bs) else ao
End

Theorem abi_head_word_bytes:
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (abi_head_word bs)
Proof
  simp[abi_head_word_def, dec_number_def, dest_NumV_def]
QED

Theorem abi_valid_member_head:
  valid_enc_tuple (pre ++ at::ats) bs bs ==>
  let ao = SUM (MAP abi_member_head_size pre) in
  ao + abi_member_head_size at <= LENGTH bs /\
  valid_enc at (abi_decode_member_bytes at bs (DROP ao bs)) /\
  valid_enc_tuple ats bs (DROP (ao + abi_member_head_size at) bs)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_valid_members_suffix >> strip_tac >>
  drule abi_valid_member_cons >> strip_tac >>
  asm_simp_tac (srw_ss()) [DROP_DROP_T, ADD_COMM, Excl "valid_enc_def"] >>
  fs[LENGTH_DROP, DROP_DROP_T, Excl "valid_enc_def"] >> decide_tac
QED

Theorem abi_valid_static_member_window:
  ~is_dynamic at /\ ao + static_length at <= LENGTH bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  ao + LENGTH (abi_decode_member_bytes at bs (DROP ao bs)) <= LENGTH bs /\
  sb + ao < dimword (:256) /\
  mem_bytes_at (sb + ao) (LENGTH (abi_decode_member_bytes at bs (DROP ao bs)))
    (abi_decode_source opc s) = abi_decode_member_bytes at bs (DROP ao bs)
Proof
  strip_tac >> `static_length at <= LENGTH (DROP ao bs)` by (simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac (srw_ss()) [abi_decode_member_bytes_def, LENGTH_TAKE_EQ] >> conj_tac
  >- decide_tac >>
  mp_tac (Q.INST [`off` |-> `ao:num`, `n` |-> `static_length at`] abi_decode_source_window) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_valid_dynamic_member_window:
  is_dynamic at /\ ao + 32 <= LENGTH bs /\
  valid_enc at (DROP (abi_head_word (DROP ao bs)) bs) /\
  (!elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_head_word (DROP ao bs) + 32 <= LENGTH bs /\
  sb + abi_head_word (DROP ao bs) < dimword (:256) /\
  abi_decode_load opc (n2w (sb + ao):bytes32) s = n2w (abi_head_word (DROP ao bs)) /\
  mem_bytes_at (sb + abi_head_word (DROP ao bs))
    (LENGTH (DROP (abi_head_word (DROP ao bs)) bs)) (abi_decode_source opc s) =
    DROP (abi_head_word (DROP ao bs)) bs
Proof
  strip_tac >> drule_all abi_valid_dynamic_head_min >> strip_tac >>
  `abi_head_word (DROP ao bs) + 32 <= LENGTH bs` by (fs[LENGTH_DROP] >> decide_tac) >>
  `sb + ao < dimword (:256) /\ sb + abi_head_word (DROP ao bs) < dimword (:256)` by decide_tac >>
  `mem_bytes_at (sb + ao) 32 (abi_decode_source opc s) = TAKE 32 (DROP ao bs)` by
    (mp_tac (Q.INST [`off` |-> `ao:num`, `n` |-> `32`] abi_decode_source_window) >> simp[]) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes, abi_head_word_bytes] >>
  mp_tac (Q.INST [`off` |-> `abi_head_word (DROP ao bs)`,
    `n` |-> `LENGTH (DROP (abi_head_word (DROP ao bs)) bs)`] abi_decode_source_window) >>
  simp[LENGTH_DROP]
QED

Theorem abi_valid_member_window:
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  let ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      data = abi_decode_member_bytes at bs (DROP ao bs) in
  valid_enc at data /\ off + LENGTH data <= LENGTH bs /\ sb + off < dimword (:256) /\
  mem_bytes_at (sb + off) (LENGTH data) (abi_decode_source opc s) = data /\
  (is_dynamic at ==> abi_decode_load opc (n2w (sb + ao):bytes32) s = n2w off)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic at`
  >- (qpat_assum `is_dynamic at` (fn th =>
        RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, abi_decode_member_bytes_def, abi_member_head_size_def]) >>
        assume_tac th) >>
      drule_all abi_valid_dynamic_member_window >> strip_tac >>
      asm_simp_tac (srw_ss()) [abi_decode_member_offset_def, abi_decode_member_bytes_def,
        abi_member_head_size_def, LENGTH_DROP, Excl "valid_enc_def"] >>
      fs[LENGTH_DROP, Excl "valid_enc_def", Excl "dec_def", Excl "enc_def"] >> decide_tac) >>
  `SUM (MAP abi_member_head_size pre) + static_length at <= LENGTH bs` by
    (qpat_x_assum `_ + abi_member_head_size at <= _` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  drule_all abi_valid_static_member_window >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_member_offset_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_MEMBER_WINDOWS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid member windows not kernel closed: " ^ n)
  end) (DB.thms "abiValidMemberWindows");
