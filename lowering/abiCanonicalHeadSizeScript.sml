(* Minimum canonical dynamic heads; a zero-length fixed array is explicit. *)
Theory abiCanonicalHeadSize
Ancestors
  abiDecodeRanges abiCanonicalArrays contractABI byte words list arithmetic

Theorem abi_head_size_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem canonical_dynamic_head_sum:
  !ts. any_dynamic ts ==> 32 <= SUM (MAP abi_member_head_size ts)
Proof
  Induct >> simp[is_dynamic_def] >> qx_gen_tac `head` >>
  Cases_on `is_dynamic head` >> simp[abi_member_head_size_def] >>
  strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem canonical_dynamic_tuple_head_min:
  has_type (Tuple ts) av /\ any_dynamic ts ==>
  32 <= LENGTH (enc (Tuple ts) av)
Proof
  Cases_on `av` >> simp_tac bool_ss [has_type_def] >> strip_tac >>
  drule canonical_tuple_length >> strip_tac >>
  drule canonical_dynamic_head_sum >> strip_tac >> decide_tac
QED

Theorem canonical_dynamic_array_list_head_min[local]:
  has_type (Array bound ty) (ListV vs) /\
  is_dynamic (Array bound ty) /\ bound <> SOME 0 ==>
  32 <= LENGTH (enc (Array bound ty) (ListV vs))
Proof
  strip_tac >> drule canonical_array_length >> strip_tac >>
  Cases_on `bound` >>
  gvs[is_dynamic_def, abi_member_head_size_def, Excl "enc_def"] >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >> decide_tac
QED

Theorem canonical_dynamic_array_head_min:
  has_type (Array bound ty) av /\
  is_dynamic (Array bound ty) /\ bound <> SOME 0 ==>
  32 <= LENGTH (enc (Array bound ty) av)
Proof
  Cases_on `av` >> simp_tac bool_ss [has_type_def] >> rpt strip_tac >>
  irule canonical_dynamic_array_list_head_min >> simp[has_type_def]
QED

Theorem canonical_dynamic_encoding_head_min:
  has_type aty av /\ is_dynamic aty /\
  (!elem. aty <> Array (SOME 0) elem) ==>
  32 <= LENGTH (enc aty av)
Proof
  Cases_on `aty` >> simp_tac bool_ss [is_dynamic_def] >|
  [rename1 `has_type (Bytes bound) av` >>
   Cases_on `bound` >> Cases_on `av` >>
   simp[has_type_def, is_dynamic_def, enc_def, enc_number_def, LENGTH_word_to_bytes],
   Cases_on `av` >>
   simp[has_type_def, enc_def, enc_number_def, LENGTH_word_to_bytes],
   rename1 `has_type (Array bound elem) av` >> rpt strip_tac >>
   `bound <> SOME 0` by
     (strip_tac >> qpat_x_assum `!child. _` (qspec_then `elem` mp_tac) >> simp[]) >>
   irule canonical_dynamic_array_head_min >> asm_simp_tac bool_ss [is_dynamic_def],
   rpt strip_tac >> irule canonical_dynamic_tuple_head_min >> asm_simp_tac bool_ss []]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CANONICAL_HEAD_SIZE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical head size not kernel closed: " ^ n)
  end) (DB.thms "abiCanonicalHeadSize");
