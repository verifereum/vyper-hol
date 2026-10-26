(* Uniform semantic layout and complete source slots for dynamic-array encoding. *)
Theory abiEncoderArrayLayout
Ancestors
  abiEncoderInput abiEncoderInputLayout abiCanonicalWindows abiCanonicalArrays abiDecodeRanges
  valueEncoding contractABI words list rich_list arithmetic

Theorem abi_encoder_have_type_every:
  !vs ty. have_type ty vs = EVERY (has_type ty) vs
Proof
  Induct >> simp_tac bool_ss [has_type_def, EVERY_DEF] >> rpt gen_tac >> simp[]
QED

Theorem abi_encoder_array_prefix_types:
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs ==>
  has_types (REPLICATE j ty) (TAKE j avs) /\ LENGTH (TAKE j avs) = j /\ LENGTH avs < dimword (:256)
Proof
  simp_tac (srw_ss()) [Once has_type_def, valid_length_def, LET_THM, abi_encoder_have_type_every] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (TAKE j avs) = j` by simp[] >> asm_simp_tac bool_ss [] >>
  `has_types (REPLICATE (LENGTH (TAKE j avs)) ty) (TAKE j avs)` by
    simp[GSYM have_type_has_types_REPLICATE, abi_encoder_have_type_every, EVERY_TAKE] >>
  qpat_assum `LENGTH (TAKE j avs) = j`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, LET_THM]) >> PURE_REWRITE_TAC [th, LET_THM]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_uniform_sizes:
  !vs ty. SUM (MAP abi_member_head_size (REPLICATE (LENGTH vs) ty)) =
    LENGTH vs * abi_member_head_size ty /\
    MAP2 abi_member_tail_size (REPLICATE (LENGTH vs) ty) vs =
    MAP (abi_member_tail_size ty) vs
Proof
  Induct >> simp[REPLICATE, MULT_CLAUSES]
QED

Theorem abi_encoder_array_prefix_sizes:
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs ==>
  LENGTH (FLAT (abi_tuple_heads hl 0 (REPLICATE j ty) (TAKE j avs))) =
    j * abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))
Proof
  strip_tac >> drule_all abi_encoder_array_prefix_types >> strip_tac >>
  mp_tac (Q.SPECL [`TAKE j avs`, `ty`] abi_encoder_uniform_sizes) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_tuple_heads_length, abi_tuple_tails_length]
QED

Theorem abi_encoder_array_selected_input:
  abi_encoder_input (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs) sb capacity mem /\
  j < LENGTH avs ==>
  abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz mem /\
  has_type ty (EL j avs) /\ asz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  32+j*msz+msz <= capacity
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  gvs[] >> rename1 `has_types (REPLICATE (LENGTH avs) ty) avs` >>
  `abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz mem` by simp[] >>
  drule abi_encoder_input_typed >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `j:num`, `ncount` |-> `LENGTH (avs:abi_value list)`,
    `cap` |-> `capacity:num`, `mem_sz` |-> `msz:num`] abi_encoder_array_slot_bound) >>
  impl_tac >- (full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM]) >>
  asm_simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_array_encoding_bound:
  has_type (Array NONE ty) (ListV avs) ==>
  32+LENGTH avs*abi_member_head_size ty <= LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >> drule canonical_array_length >> simp[]
QED

Theorem abi_encoder_array_static_size:
  has_type (Array NONE ty) (ListV avs) /\ ~is_dynamic ty ==>
  LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*abi_member_head_size ty
Proof
  strip_tac >> drule canonical_array_length >>
  `SUM (MAP (abi_member_tail_size ty) avs) = 0` by
    (Induct_on `avs` >> simp[abi_member_tail_size_def]) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array layout not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayLayout");
