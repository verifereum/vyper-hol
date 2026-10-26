(* Canonical child slices for either ABI array representation and any child type. *)
Theory abiDecoderArraySlice
Ancestors
  abiCanonicalArrayLoad abiDecodeRanges abiDecoderContract
  contractABI venomState words list rich_list arithmetic
Libs
  Omega

Definition abi_array_child_offset_def:
  abi_array_child_offset (bound:num option) aty avs j =
    let data = if bound = NONE then 32 else 0 in
    if is_dynamic aty then
      data + LENGTH avs * abi_member_head_size aty +
        SUM (MAP (abi_member_tail_size aty) (TAKE j avs))
    else data + j * abi_member_head_size aty
End

Theorem abi_array_child_offset_append:
  abi_array_child_offset bound aty (pre ++ av::post) (LENGTH pre) =
    if is_dynamic aty then
      (if bound = NONE then 32 else 0) + LENGTH (pre ++ av::post) * abi_member_head_size aty +
        SUM (MAP (abi_member_tail_size aty) pre)
    else (if bound = NONE then 32 else 0) + LENGTH pre * abi_member_head_size aty
Proof
  simp[abi_array_child_offset_def, TAKE_LENGTH_APPEND]
QED

Theorem abi_array_child_offset_ranges:
  has_type (Array bound aty) (ListV (pre ++ av::post)) ==>
  (if bound = NONE then 32 else 0) + LENGTH pre * abi_member_head_size aty +
    abi_member_head_size aty <= LENGTH (enc (Array bound aty) (ListV (pre ++ av::post))) /\
  abi_array_child_offset bound aty (pre ++ av::post) (LENGTH pre) + LENGTH (enc aty av) <=
    LENGTH (enc (Array bound aty) (ListV (pre ++ av::post))) /\
  (if bound = NONE then 32 else 0) <=
    abi_array_child_offset bound aty (pre ++ av::post) (LENGTH pre)
Proof
  strip_tac >> drule canonical_array_member_ranges >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic aty` >> gvs[abi_array_child_offset_append, Excl "enc_def"] >>
  Cases_on `bound = NONE` >> simp[]
QED

Theorem abi_array_child_offset_source:
  has_type (Array bound aty) (ListV (pre ++ av::post)) /\
  mem_bytes_at sb (LENGTH (enc (Array bound aty) (ListV (pre ++ av::post))))
    (abi_decode_source opc s) = enc (Array bound aty) (ListV (pre ++ av::post)) ==>
  has_type aty av /\
  mem_bytes_at (sb + abi_array_child_offset bound aty (pre ++ av::post) (LENGTH pre))
    (LENGTH (enc aty av)) (abi_decode_source opc s) = enc aty av
Proof
  strip_tac >> drule canonical_array_member_type >> strip_tac >>
  Cases_on `is_dynamic aty`
  >- (drule_all canonical_array_dynamic_child_source >>
      asm_simp_tac bool_ss [abi_array_child_offset_append]) >>
  drule_all canonical_array_static_child_source >>
  asm_simp_tac bool_ss [abi_array_child_offset_append]
QED

Theorem abi_decoder_array_cell_capacity:
  !i cap sz:num. i < cap ==> i * sz + sz <= cap * sz
Proof
  rpt strip_tac >> `SUC i <= cap` by decide_tac >>
  `SUC i * sz <= cap * sz` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `SUC i * sz <= cap * sz` mp_tac >>
  simp_tac bool_ss [MULT_CLAUSES, ADD_COMM]
QED

Theorem abi_decoder_array_cell_arithmetic:
  !d used sz capacity limit:num.
  used + sz <= capacity /\ d + (32 + capacity) < limit ==>
  d + 32 + used < limit /\ d + 32 + used + sz <= d + (32 + capacity)
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_array_cell_window:
  !i cap sz d limit:num. i < cap /\ d + (32 + cap * sz) < limit ==>
  d + 32 + i * sz < limit /\ d + 32 + i * sz + sz <= d + (32 + cap * sz)
Proof
  rpt gen_tac >> strip_tac >>
  `i * sz + sz <= cap * sz` by simp[abi_decoder_array_cell_capacity] >>
  irule abi_decoder_array_cell_arithmetic >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_SLICE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array child slice not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArraySlice");
