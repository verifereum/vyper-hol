(* The next encoded child fits between the array's head and tail frontiers. *)
Theory abiEncoderArrayBounds
Ancestors
  abiEncoderArrayLayout abiCanonicalWindows abiDecodeRanges abiDecoderArraySlice
  valueEncoding contractABI list rich_list arithmetic

Theorem abi_encoder_array_child_bounds:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  32 <= output_size /\ has_type ty (EL j avs) /\
  j*abi_member_head_size ty+abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty /\
  LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <= output_size-32 /\
  (is_dynamic ty ==>
    j*abi_member_head_size ty+32 <= LENGTH avs*abi_member_head_size ty /\
    LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
      LENGTH (enc ty (EL j avs)) <= output_size-32) /\
  (~is_dynamic ty ==>
    j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <= LENGTH avs*abi_member_head_size ty)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `TAKE j avs++EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  qpat_assum `has_type (Array NONE ty) (ListV avs)`
    (assume_tac o SIMP_RULE (srw_ss()) [Once has_type_def, abi_encoder_have_type_every]) >>
  `has_type ty (EL j avs)` by fs[EVERY_EL] >>
  mp_tac (Q.SPECL [`j:num`, `LENGTH (avs:abi_value list)`, `abi_member_head_size ty`]
    abi_decoder_array_cell_capacity) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  drule canonical_array_length >> strip_tac >>
  `SUM (MAP (abi_member_tail_size ty) avs) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+abi_member_tail_size ty (EL j avs)+
      SUM (MAP (abi_member_tail_size ty) (DROP (SUC j) avs))` by
    (qpat_assum `TAKE j avs++_ = avs`
      (mp_tac o AP_TERM ``\xs. SUM (MAP (abi_member_tail_size ty) xs)``) >>
     simp_tac bool_ss [MAP_APPEND, SUM_APPEND, MAP, SUM] >> decide_tac) >>
  mp_tac (Q.INST [`bound` |-> `NONE:num option`, `pre` |-> `TAKE j (avs:abi_value list)`,
    `v` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`]
    canonical_array_member_ranges) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  `~is_dynamic ty ==> LENGTH (enc ty (EL j avs)) = abi_member_head_size ty` by
    (strip_tac >> drule_all (cj 1 enc_has_static_length) >> simp[abi_member_head_size_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `is_dynamic ty` >>
  full_simp_tac (srw_ss()) [abi_member_head_size_def, Excl "enc_def"] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_BOUNDS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array child bounds not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayBounds");
