(* A processed array prefix occupies only the enclosing ABI output window.
   TOP-LEVEL: prefix capacity and preservation across disjoint scratch writes. *)
Theory abiEncoderArrayFrame
Ancestors
  abiEncoderArrayPrefix abiEncoderArrayLayout abiEncoderInputLayout abiCanonicalArrays abiDecodeRanges
  abiDecoderFrame abiDecoderContract valueEncoding contractABI venomState list arithmetic

Theorem abi_footprint_disjoint_subwindow:
  abi_footprint_disjoint outer outer_sz fp /\ outer <= inner /\
  inner+inner_sz <= outer+outer_sz ==>
  abi_footprint_disjoint inner inner_sz fp
Proof
  simp_tac bool_ss [abi_footprint_disjoint_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> qx_genl_tac [`p`, `n`] >> strip_tac >>
  qpat_x_assum `!d sz. _` (qspecl_then [`p`, `n`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_array_prefix_capacity:
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  32 <= output_size /\ j*abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty /\
  LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <= output_size-32
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <=
    SUM (MAP (abi_member_tail_size ty) avs)` by
    (Cases_on `j = LENGTH avs` >- simp[] >> `j < LENGTH avs` by decide_tac >>
     mp_tac (Q.ISPECL [`abi_member_tail_size ty`, `avs:abi_value list`, `j:num`]
       abi_encoder_prefix_sum_bound) >>
     impl_tac >- asm_simp_tac bool_ss [] >> decide_tac) >>
  `j*abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty` by simp[LE_MULT_RCANCEL] >>
  drule canonical_array_length >> strip_tac >> full_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_array_prefix_output_frame:
  has_type (Array NONE ty) (ListV avs) /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\ abi_footprint_disjoint d output_size fp ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all abi_encoder_array_prefix_capacity >> strip_tac >>
  drule_all abi_encoder_array_prefix_sizes >> strip_tac >>
  irule abi_encoder_array_prefix_frame >> qexistsl_tac [`fp`, `initial`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >>
  irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`, `output_size`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_FRAME_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array frame not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayFrame");
