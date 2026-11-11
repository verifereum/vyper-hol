Theory extRetSemanticLedgerProbePtr
Ancestors
  extRetRecursiveLayoutPtr abiEncoderSourceAggregate abiEncoderSourceTransport
  abiTypeBoundProps abiEncoderInput vyperTypeABI vyperABI vyperTyping
  vyperValue valueEncoding contractABI dfHelperProps list rich_list arithmetic
  retAbiPlanProps compileEnv finite_map

(* Totality is an existing checked semantic interface, not a new premise on
   the encoder callback.  Lengths below index actual converted source values. *)
Theorem encoder_semantic_dynamic_array_ledger:
  evaluate_type env (ArrayT ty (Dynamic cap)) =
    SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  vyper_is_dynamic env ty ==>
  ?avs ns.
    vyper_to_abi_same env ty vs = SOME avs /\
    ns = MAP (\av. LENGTH (enc (vyper_to_abi_type env ty) av)) avs /\
    LENGTH ns = LENGTH vs /\
    (!i. i < LENGTH vs ==>
      vyper_to_abi env ty (EL i vs) = SOME (EL i avs) /\
      EL i ns <= vyper_abi_size_bound env ty) /\
    32 + 32 * LENGTH vs + SUM ns <=
      vyper_abi_size_bound env (ArrayT ty (Dynamic cap))
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `all_have_type tv vs /\ LENGTH vs <= cap` by fs[value_has_type_def] >>
  drule_all (cj 3 vyper_to_abi_total) >> strip_tac >>
  drule abi_encoder_same_conversion >> strip_tac >>
  qexistsl [`avs`, `MAP (\av. LENGTH (enc (vyper_to_abi_type env ty) av)) avs`] >>
  simp[] >>
  `!i. i < LENGTH vs ==>
     LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <=
       vyper_abi_size_bound env ty` by
    (rpt strip_tac >> irule (cj 1 vyper_to_abi_enc_length_bound) >>
     qexistsl [`tv`, `EL i vs`] >>
     fs[all_have_type_EVERY, EVERY_EL]) >>
  conj_tac >- simp[EL_MAP] >>
  `SUM (MAP (\av. LENGTH (enc (vyper_to_abi_type env ty) av)) avs) <=
     vyper_abi_size_bound env ty * LENGTH avs` by
    (irule sum_map_bounded >> simp[EVERY_EL]) >>
  `LENGTH vs * (32 + vyper_abi_size_bound env ty) <=
     cap * (32 + vyper_abi_size_bound env ty)` by simp[] >>
  simp[vyper_abi_size_bound_def] >>
  qpat_x_assum `SUM _ <= _` mp_tac >>
  qpat_x_assum `LENGTH vs * (32 + _) <= _` mp_tac >>
  pure_rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  `vyper_abi_size_bound env ty * LENGTH avs =
     LENGTH vs * vyper_abi_size_bound env ty` by simp[MULT_COMM] >>
  `LENGTH vs * 32 = 32 * LENGTH vs` by metis_tac[MULT_COMM] >>
  decide_tac
QED

Theorem encoder_semantic_zero_regressions:
  vyper_to_abi env NoneT NoneV = SOME (ListV []) /\
  vyper_to_abi env (TupleT []) (ArrayV (TupleV [])) = SOME (ListV []) /\
  vyper_abi_size_bound env NoneT = 0 /\
  vyper_abi_size_bound env (TupleT []) = 0 /\
  type_memory_size (ArrayTV NoneTV (Fixed 3)) = 0 /\
  type_memory_size (ArrayTV NoneTV (Dynamic 3)) = 32 /\
  enc (Tuple []) (ListV []) = []
Proof
  simp[vyper_abi_size_bound_def, type_memory_size_def, enc_def, REV_DEF]
QED

(* These are the metadata coordinates of the actual evaluated source child.
   In particular struct children are interpreted in the reduced environment;
   compiler memory/head metadata may still refer to the outer environment. *)
Theorem encoder_semantic_tuple_child_coordinates:
  env SUBMAP tenv /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type env (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem') /\
  i < LENGTH tys ==>
  ?av. vyper_to_abi env (EL i tys) (EL i vs) = SOME av /\
    LENGTH (enc (vyper_to_abi_type env (EL i tys)) av) <=
      vyper_abi_size_bound env (EL i tys) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    abi_embedded_static_size cenv.ce_struct_fields (EL i tys) =
      (if is_dynamic (vyper_to_abi_type env (EL i tys)) then 32
       else static_length (vyper_to_abi_type env (EL i tys))) /\
    (!mem'. mem_agree_outside m mem mem' ==>
      val_in_memory (EL i tvs) (EL i vs)
        (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem')
Proof
  strip_tac >> drule_all encoder_evaluated_tuple_child >> strip_tac >>
  drule_all abi_elem_props >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >> strip_tac >>
  qexists `av` >> simp[]
QED

Theorem encoder_semantic_struct_child_coordinates:
  env SUBMAP tenv /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type env (StructT nsid) = SOME (StructTV fts) /\
  value_has_type (StructTV fts) (StructV fields) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    val_in_memory (StructTV fts) (StructV fields) sb mem') ==>
  ?args. FLOOKUP env nsid = SOME (StructArgs args) /\
    LENGTH args = LENGTH fts /\ LENGTH fields = LENGTH fts /\
    !i. i < LENGTH fts ==>
      ?av. vyper_to_abi (env \\ nsid) (EL i (MAP SND args))
             (EL i (MAP SND fields)) = SOME av /\
        LENGTH (enc (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args))) av) <=
          vyper_abi_size_bound (env \\ nsid) (EL i (MAP SND args)) /\
        type_memory_bytes cenv (EL i (MAP SND args)) =
          type_memory_size (EL i (MAP SND fts)) /\
        abi_embedded_static_size cenv.ce_struct_fields (EL i (MAP SND args)) =
          (if is_dynamic (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args)))
           then 32 else static_length
             (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args)))) /\
        (!mem'. mem_agree_outside m mem mem' ==>
          val_in_memory (EL i (MAP SND fts)) (EL i (MAP SND fields))
            (sb+SUM (MAP type_memory_size (TAKE i (MAP SND fts)))) mem')
Proof
  strip_tac >> drule_all encoder_evaluated_struct_children >> strip_tac >>
  qexists `args` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH fts ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  `env \\ nsid SUBMAP tenv` by
    fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  drule_all abi_elem_props >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >> strip_tac >>
  qexists `av` >> simp[]
QED

Theorem encoder_semantic_empty_struct_regression:
  FLOOKUP env nsid = SOME (StructArgs []) ==>
  evaluate_type env (StructT nsid) = SOME (StructTV []) /\
  vyper_to_abi env (StructT nsid) (StructV []) = SOME (ListV []) /\
  vyper_abi_size_bound env (StructT nsid) = 0 /\
  type_memory_size (StructTV []) = 0
Proof
  simp[evaluate_type_def, vyper_abi_size_bound_def, type_memory_size_def,
       type_slot_size_def]
QED
