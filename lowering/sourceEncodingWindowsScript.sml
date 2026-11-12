(* Canonical windows require aligned static lengths, not ABI typing. *)
Theory sourceEncodingWindows
Ancestors abiEncoderOpenInput abiCanonicalHeadSize abiDecoderMemberSlice
  abiCanonicalWindows abiDecodeRanges contractABI list rich_list arithmetic byte words

Theorem structural_member_head_window:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  TAKE (abi_member_head_size ty)
    (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) =
    (if is_dynamic ty then enc_number (Uint 256)
      (NumV (head_lengths (pre ++ ty::post) 0 +
        SUM (MAP2 abi_member_tail_size pre pvs))) else enc ty v)
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\
   abi_encoder_layout_valid ty v /\
   LIST_REL abi_encoder_layout_valid post rest` by
    (gvs[LIST_REL_APPEND_EQ, abi_encoder_layout_valid_def,
      abi_member_head_size_def, LIST_REL_EL_EQN]) >>
  irule abi_window_from_parts >>
  conj_tac
  >- (Cases_on `is_dynamic ty` >>
      gvs[abi_encoder_layout_valid_def, abi_member_head_size_def]) >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs)`,
     `FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
       (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
       post rest) ++ FLAT (abi_tuple_tails pre pvs) ++
       (if is_dynamic ty then enc ty v else []) ++
       FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      irule (SIMP_RULE pureSimps.pure_ss [LET_THM] canonical_member_parts) >>
      simp[]) >>
  simp[abi_encoder_open_heads_length]
QED

Theorem structural_member_tail_window:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\
   abi_encoder_layout_valid ty v /\
   LIST_REL abi_encoder_layout_valid post rest` by
    (gvs[LIST_REL_APPEND_EQ, abi_encoder_layout_valid_def,
      abi_member_head_size_def, LIST_REL_EL_EQN]) >>
  `LENGTH post = LENGTH rest` by metis_tac[LIST_REL_LENGTH] >>
  irule abi_window_from_parts >>
  conj_tac >- REFL_TAC >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs) ++
      enc_number (Uint 256)
        (NumV (head_lengths (pre ++ ty::post) 0 +
               SUM (MAP2 abi_member_tail_size pre pvs))) ++
      FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
        (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
        post rest) ++ FLAT (abi_tuple_tails pre pvs)`,
     `FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      qpat_x_assum `is_dynamic ty` (fn dyn =>
        irule (SIMP_RULE bool_ss [LET_THM,dyn] canonical_member_parts)) >>
      simp[]) >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length,
       head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
  decide_tac
QED

Theorem structural_tuple_child_ranges:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  SUM (MAP abi_member_head_size pre) + abi_member_head_size ty <=
    LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) /\
  abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre) +
    LENGTH (enc ty v) <=
    LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\
   abi_encoder_layout_valid ty v /\
   LIST_REL abi_encoder_layout_valid post rest` by
    (gvs[LIST_REL_APPEND_EQ, abi_encoder_layout_valid_def,
      abi_member_head_size_def, LIST_REL_EL_EQN]) >>
  `LIST_REL abi_encoder_layout_valid (pre ++ ty::post) (pvs ++ v::rest)` by
    simp[LIST_REL_APPEND_EQ] >>
  drule abi_encoder_open_tuple_length >>
  simp[abi_tuple_child_offset_append, TAKE_LENGTH_APPEND,
    head_lengths_acc, MAP_APPEND, SUM_APPEND, MAP2_APPEND] >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_encoder_layout_valid_def, abi_member_head_size_def,
      abi_member_tail_size_def, Excl "enc_def"]
QED

Theorem structural_tuple_child_window:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  TAKE (LENGTH (enc ty v))
    (DROP (abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >>
  pure_rewrite_tac[abi_tuple_child_offset_append] >>
  `TAKE (LENGTH pre) (pvs ++ v::rest) = pvs` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  Cases_on `is_dynamic ty`
  >- (drule_all structural_member_tail_window >> asm_simp_tac bool_ss []) >>
  `LENGTH (enc ty v) = abi_member_head_size ty` by
    gvs[LIST_REL_APPEND_EQ] >>
  drule_all structural_member_head_window >> asm_simp_tac bool_ss []
QED

Theorem structural_tuple_child_source:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))
    source = enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) ==>
  mem_bytes_at (sb + abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre))
    (LENGTH (enc ty v)) source = enc ty v
Proof
  strip_tac >> drule_all structural_tuple_child_ranges >> strip_tac >>
  drule_all structural_tuple_child_window >>
  qpat_x_assum `mem_bytes_at sb _ source = _`
    (fn th => pure_once_rewrite_tac [GSYM th]) >>
  drule mem_bytes_at_window >> simp[]
QED

Theorem structural_tuple_indexed_source:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty) tys avs /\
  i < LENGTH tys /\
  mem_bytes_at sb (LENGTH (enc (Tuple tys) (ListV avs))) source =
    enc (Tuple tys) (ListV avs) ==>
  abi_tuple_child_offset tys avs i + LENGTH (enc (EL i tys) (EL i avs)) <=
    LENGTH (enc (Tuple tys) (ListV avs)) /\
  mem_bytes_at (sb + abi_tuple_child_offset tys avs i)
    (LENGTH (enc (EL i tys) (EL i avs))) source = enc (EL i tys) (EL i avs)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `i < LENGTH avs` by decide_tac >>
  `tys = TAKE i tys ++ EL i tys::DROP (SUC i) tys /\
   avs = TAKE i avs ++ EL i avs::DROP (SUC i) avs` by
    metis_tac[TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  `LENGTH (TAKE i tys) = i /\ LENGTH (TAKE i avs) = i` by simp[] >>
  `LIST_REL (\ty av. ~is_dynamic ty ==>
      LENGTH (enc ty av) = abi_member_head_size ty)
     (TAKE i tys ++ EL i tys::DROP (SUC i) tys)
     (TAKE i avs ++ EL i avs::DROP (SUC i) avs)` by metis_tac[] >>
  `LENGTH (TAKE i tys) = LENGTH (TAKE i avs)` by simp[] >>
  `mem_bytes_at sb
     (LENGTH (enc (Tuple (TAKE i tys ++ EL i tys::DROP (SUC i) tys))
       (ListV (TAKE i avs ++ EL i avs::DROP (SUC i) avs)))) source =
     enc (Tuple (TAKE i tys ++ EL i tys::DROP (SUC i) tys))
       (ListV (TAKE i avs ++ EL i avs::DROP (SUC i) avs))` by metis_tac[] >>
  drule_all structural_tuple_child_ranges >> strip_tac >>
  drule_all structural_tuple_child_source >> metis_tac[]
QED

Theorem structural_array_indexed_source:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (REPLICATE (LENGTH avs) ty) avs /\ i < LENGTH avs /\
  mem_bytes_at sb (LENGTH (enc (Array bound ty) (ListV avs))) source =
    enc (Array bound ty) (ListV avs) ==>
  (if bound = NONE then 32 else 0) +
    abi_tuple_child_offset (REPLICATE (LENGTH avs) ty) avs i +
    LENGTH (enc ty (EL i avs)) <= LENGTH (enc (Array bound ty) (ListV avs)) /\
  mem_bytes_at (sb + (if bound = NONE then 32 else 0) +
    abi_tuple_child_offset (REPLICATE (LENGTH avs) ty) avs i)
    (LENGTH (enc ty (EL i avs))) source = enc ty (EL i avs)
Proof
  strip_tac >>
  `mem_bytes_at (sb + (if bound = NONE then 32 else 0))
     (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs))) source =
     enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs)` by
    (`(if bound = NONE then 32 else 0) +
       LENGTH (enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs)) <=
       LENGTH (enc (Array bound ty) (ListV avs))` by
       (pure_rewrite_tac[canonical_array_tuple] >>
        Cases_on `bound` >> simp[Excl "enc_def"]) >>
     drule mem_bytes_at_window >>
     disch_then (qspecl_then [`sb`, `source`] mp_tac) >>
     asm_simp_tac bool_ss [] >>
     pure_rewrite_tac[canonical_array_drop_count] >>
     simp[Excl "enc_def"]) >>
  `i < LENGTH (REPLICATE (LENGTH avs) ty)` by simp[] >>
  drule_all structural_tuple_indexed_source >>
  pure_rewrite_tac[canonical_array_tuple] >>
  Cases_on `bound` >> simp[EL_REPLICATE, Excl "enc_def"]
QED

Theorem structural_empty_encoding_probe[local]:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty) [] [] /\
  enc (Tuple []) (ListV []) = [] /\
  enc (Array (SOME 0) (Tuple [])) (ListV []) = []
Proof
  EVAL_TAC
QED

Theorem structural_zero_width_child_probe[local]:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    [Tuple []] [ListV []] /\
  abi_tuple_child_offset [Tuple []] [ListV []] 0 = 0 /\
  LENGTH (enc (Tuple []) (ListV [])) = 0
Proof
  EVAL_TAC
QED
