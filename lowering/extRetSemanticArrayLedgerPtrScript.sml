Theory extRetSemanticArrayLedgerPtr
Ancestors
  extRetSemanticLedgerProbePtr extRetRecursiveLayoutPtr
  abiEncoderSourceTransport abiCanonicalHeadSize abiDecodeRanges
  abiTypeBoundProps abiEncoderInput vyperTypeABI vyperABI vyperTyping
  vyperValue valueEncoding contractABI byte list rich_list arithmetic

(* Uniform encodings need no ABI cardinality validity hypothesis.  In the
   static case enc_tuple concatenates the actual child encodings, even for
   empty/zero-sized children. *)
Theorem encoder_uniform_tuple_length[local]:
  !vs hl tl hds tls.
    LENGTH (enc_tuple hl tl (REPLICATE (LENGTH vs) ty) vs hds tls) =
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      (if is_dynamic ty then 32 * LENGTH vs else 0) +
      SUM (MAP (\v. LENGTH (enc ty v)) vs)
Proof
  Induct >> simp[REPLICATE, Once enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
                 MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  rpt gen_tac >> Cases_on `is_dynamic ty` >>
  simp[Once enc_def, LENGTH_word_to_bytes, MULT_CLAUSES]
QED

Theorem encoder_uniform_dynamic_array_length:
  LENGTH (enc (Array NONE ty) (ListV avs)) =
    32 + (if is_dynamic ty then 32 * LENGTH avs else 0) +
      SUM (MAP (\av. LENGTH (enc ty av)) avs)
Proof
  simp[canonical_array_tuple, LENGTH_enc_number, Once enc_def,
       encoder_uniform_tuple_length]
QED

Theorem encoder_semantic_array_length_ledger:
  evaluate_type env (ArrayT ty (Dynamic cap)) =
    SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) ==>
  ?avs ns.
    evaluate_type env ty = SOME tv /\
    vyper_to_abi_same env ty vs = SOME avs /\
    vyper_to_abi env (ArrayT ty (Dynamic cap)) (ArrayV (DynArrayV vs)) =
      SOME (ListV avs) /\
    ns = MAP (\av. LENGTH (enc (vyper_to_abi_type env ty) av)) avs /\
    LENGTH avs = LENGTH vs /\ LENGTH ns = LENGTH vs /\
    (!i. i < LENGTH vs ==>
      value_has_type tv (EL i vs) /\
      vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
      EL i ns = LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) /\
      EL i ns <= vyper_abi_size_bound env ty) /\
    LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) (ListV avs)) =
      32 + (if is_dynamic (vyper_to_abi_type env ty)
            then 32 * LENGTH vs else 0) + SUM ns /\
    32 + (if is_dynamic (vyper_to_abi_type env ty)
          then 32 * LENGTH vs else 0) + SUM ns <=
      vyper_abi_size_bound env (ArrayT ty (Dynamic cap))
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `all_have_type tv vs` by fs[value_has_type_def] >>
  drule_all (cj 3 vyper_to_abi_total) >> strip_tac >>
  drule abi_encoder_same_conversion >> strip_tac >>
  `vyper_to_abi env (ArrayT ty (Dynamic cap)) (ArrayV (DynArrayV vs)) =
     SOME (ListV avs)` by simp[] >>
  `LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) (ListV avs)) <=
     vyper_abi_size_bound env (ArrayT ty (Dynamic cap))` by
    (irule (cj 1 vyper_to_abi_enc_length_bound) >>
     qexistsl [`ArrayTV tv (Dynamic cap)`, `ArrayV (DynArrayV vs)`] >> simp[]) >>
  `!i. i < LENGTH vs ==>
     value_has_type tv (EL i vs) /\
     LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <=
       vyper_abi_size_bound env ty` by
    (rpt strip_tac >- fs[all_have_type_EVERY, EVERY_EL] >>
     irule (cj 1 vyper_to_abi_enc_length_bound) >>
     qexistsl [`tv`, `EL i vs`] >>
     fs[all_have_type_EVERY, EVERY_EL]) >>
  qexistsl [`avs`, `MAP (\av. LENGTH (enc (vyper_to_abi_type env ty) av)) avs`] >>
  fs[Excl "enc_def", vyper_to_abi_type_def,
     encoder_uniform_dynamic_array_length, EL_MAP] >> gvs[]
QED

Theorem encoder_semantic_array_child_coordinates:
  evaluate_type env (ArrayT ty (Dynamic cap)) =
    SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  vyper_to_abi_same env ty vs = SOME avs /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) sb mem') /\
  i < LENGTH vs ==>
  evaluate_type env ty = SOME tv /\
  value_has_type tv (EL i vs) /\
  vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
  LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <=
    vyper_abi_size_bound env ty /\
  sb+32+i*type_memory_size tv+type_memory_size tv <=
    sb+type_memory_size (ArrayTV tv (Dynamic cap)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem')
Proof
  strip_tac >>
  drule_all encoder_dynamic_source_window >> strip_tac >>
  drule_all encoder_semantic_array_length_ledger >> strip_tac >>
  qpat_x_assum `vyper_to_abi_same env ty vs = SOME _` mp_tac >>
  simp[] >> strip_tac >> gvs[EL_MAP, Excl "enc_def"]
QED

(* No positive stride or nonempty array is needed by the ledger. *)
Theorem encoder_semantic_array_zero_regressions:
  LENGTH (enc (Array NONE (Tuple [])) (ListV [])) = 32 /\
  LENGTH (enc (Array NONE (Tuple [])) (ListV [ListV []; ListV []])) = 32 /\
  LENGTH (enc (Array NONE (Array NONE (Tuple []))) (ListV [])) = 32 /\
  type_memory_size NoneTV = 0
Proof
  EVAL_TAC >> simp[]
QED
