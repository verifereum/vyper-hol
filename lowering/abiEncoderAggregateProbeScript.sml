(* Checked aggregate interface diagnostics for the source encoder bridge. *)
Theory abiEncoderAggregateProbe
Ancestors
  abiEncoderSourceBridge abiEncoderInput abiEncoderProps vyperValue vyperTyping valueEncoding vyperABI
  contractABI compileEnv venomMemDefs words list rich_list
Libs
  dep_rewrite

Theorem encoder_array_requires_positive_slots:
  evaluate_type env (ArrayT ty bd) = SOME atv ==>
  ?tv. evaluate_type env ty = SOME tv /\
       atv = ArrayTV tv bd /\ 0 < type_slot_size tv
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem encoder_empty_tuple_array_rejected:
  evaluate_type env (ArrayT (TupleT []) bd) = NONE
Proof
  simp[evaluate_type_def, type_slot_size_def]
QED

Theorem encoder_tuple_abi_type_probe:
  has_type (Tuple tys) (ListV avs) <=>
  valid_length NONE avs /\ has_types tys avs
Proof
  simp[has_type_def]
QED

Theorem encoder_zero_tuple_evaluate_members:
  !n acc. evaluate_types env (REPLICATE n (TupleT [])) acc =
    SOME (REVERSE acc ++ REPLICATE n (TupleTV []))
Proof
  Induct >> simp[evaluate_type_def, type_slot_size_def, REPLICATE] >>
  simp[GSYM APPEND_ASSOC]
QED

Theorem encoder_zero_tuple_slot_members:
  !n. type_slot_size_list (REPLICATE n (TupleTV [])) = 0 /\
      type_memory_size_list (REPLICATE n (TupleTV [])) = 0
Proof
  Induct >> simp[REPLICATE, type_slot_size_def, type_memory_size_def]
QED

Theorem encoder_zero_tuple_value_members:
  !n. values_have_types (REPLICATE n (TupleTV []))
    (REPLICATE n (ArrayV (TupleV [])))
Proof
  Induct >> simp[REPLICATE, value_has_type_def]
QED

Theorem encoder_zero_tuple_convert_members:
  !n. vyper_to_abi_list env (REPLICATE n (TupleT []))
    (REPLICATE n (ArrayV (TupleV []))) =
    SOME (REPLICATE n (ListV []))
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_def]
QED

Theorem encoder_zero_tuple_abi_members:
  !n. vyper_to_abi_types env (REPLICATE n (TupleT [])) =
    REPLICATE n (Tuple [])
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_type_def]
QED

(* Source type evaluation and capacity do not bound tuple cardinality. *)
Theorem encoder_zero_tuple_source_diagnostic:
  !n. evaluate_type env (TupleT (REPLICATE n (TupleT []))) =
        SOME (TupleTV (REPLICATE n (TupleTV []))) /\
      value_has_type (TupleTV (REPLICATE n (TupleTV [])))
        (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) /\
      type_memory_size (TupleTV (REPLICATE n (TupleTV []))) = 0 /\
      vyper_to_abi env (TupleT (REPLICATE n (TupleT [])))
        (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) =
        SOME (ListV (REPLICATE n (ListV [])))
Proof
  simp[evaluate_type_def, encoder_zero_tuple_evaluate_members,
       encoder_zero_tuple_slot_members, type_slot_size_def, value_has_type_def,
       encoder_zero_tuple_value_members, type_memory_size_def,
       vyper_to_abi_def, encoder_zero_tuple_convert_members]
QED

Theorem encoder_zero_tuple_abi_cardinality_diagnostic:
  ~has_type (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV [])))
Proof
  simp[vyper_to_abi_type_def, encoder_zero_tuple_abi_members,
       has_type_def, valid_length_def]
QED

Theorem encoder_zero_tuple_memory_members:
  !n. tuple_in_memory (REPLICATE n (ArrayV (TupleV [])))
    (REPLICATE n (TupleTV [])) sb mem
Proof
  Induct >> simp[REPLICATE, val_in_memory_def, type_memory_size_def]
QED

Theorem encoder_zero_tuple_memory_diagnostic:
  val_in_memory (TupleTV (REPLICATE n (TupleTV [])))
    (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) sb mem
Proof
  simp[val_in_memory_def, encoder_zero_tuple_memory_members]
QED

Theorem encoder_zero_tuple_input_unavailable:
  ~abi_encoder_input ei (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV []))) sb cap mem
Proof
  strip_tac >> drule abi_encoder_input_typed >>
  simp[encoder_zero_tuple_abi_cardinality_diagnostic]
QED

Theorem encoder_zero_tuple_static_members:
  !n. ~any_dynamic (REPLICATE n (Tuple []))
Proof
  Induct >> simp[REPLICATE, is_dynamic_def]
QED

Theorem encoder_zero_tuple_plan:
  abi_enc_plan env (TupleT (REPLICATE n (TupleT []))) (AbiCopy 0)
Proof
  `abi_enc_plan env (TupleT (REPLICATE n (TupleT [])))
     (AbiCopy (type_memory_size (TupleTV (REPLICATE n (TupleTV [])))))`
    suffices_by simp[type_memory_size_def, encoder_zero_tuple_slot_members] >>
  irule abi_enc_plan_copy >>
  simp[encoder_zero_tuple_source_diagnostic, vyper_to_abi_type_def,
       encoder_zero_tuple_abi_members, is_dynamic_def,
       encoder_zero_tuple_static_members]
QED

Theorem encoder_zero_tuple_pre:
  enc_pre st st' ops lo top (TupleTV (REPLICATE n (TupleTV [])))
    (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) sb [(db,0)] s <=>
  ((!y. MEM (Var y) ops ==> not_fresh_at st y) /\ sb <= lo /\ db <= lo /\
   enc_scratch (frag_ids st st') lo top s)
Proof
  simp[enc_pre_def, encoder_zero_tuple_memory_diagnostic,
       type_memory_size_def, encoder_zero_tuple_slot_members,
       venomMemDefsTheory.regions_disjoint_def]
QED

Theorem encoder_zero_tuple_typed_members:
  !n. has_types (REPLICATE n (Tuple [])) (REPLICATE n (ListV []))
Proof
  Induct >> simp[REPLICATE, has_type_def, valid_length_def]
QED

Theorem encoder_zero_tuple_flat_encoding:
  !n. FLAT (MAP2 enc (REPLICATE n (Tuple []))
    (REPLICATE n (ListV []))) = []
Proof
  Induct >> simp[REPLICATE, enc_def, REV_DEF]
QED

Theorem encoder_zero_tuple_encoding:
  enc (vyper_to_abi_type env (TupleT (REPLICATE n (TupleT []))))
    (ListV (REPLICATE n (ListV []))) = []
Proof
  pure_rewrite_tac[vyper_to_abi_type_def, encoder_zero_tuple_abi_members] >>
  DEP_REWRITE_TAC[enc_tuple_static] >>
  simp[encoder_zero_tuple_typed_members, encoder_zero_tuple_static_members,
       encoder_zero_tuple_flat_encoding]
QED

Theorem encoder_zero_tuple_giant_diagnostic:
  abi_enc_plan env (TupleT (REPLICATE (dimword (:256)) (TupleT []))) (AbiCopy 0) /\
  enc (vyper_to_abi_type env (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV []))) = [] /\
  ~abi_encoder_input ei (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV []))) sb cap mem
Proof
  simp[encoder_zero_tuple_plan, encoder_zero_tuple_encoding,
       encoder_zero_tuple_input_unavailable]
QED

Theorem encoder_zero_copy_representative:
  !sb cap mem. abi_encoder_input (AbiCopy 0) (Tuple []) (ListV []) sb cap mem
Proof
  simp[abi_encoder_input_copy_iff, has_type_def, valid_length_def,
       is_dynamic_def, static_length_def, enc_def, REV_DEF, mem_bytes_at_def]
QED

Theorem encoder_zero_copy_encoding_correspondence:
  enc (Tuple []) (ListV []) =
  enc (vyper_to_abi_type env (TupleT (REPLICATE n (TupleT []))))
    (ListV (REPLICATE n (ListV [])))
Proof
  simp[encoder_zero_tuple_encoding, enc_def, REV_DEF]
QED

Theorem encoder_dynamic_tuple_evaluate_members:
  !n acc. evaluate_types env
    (REPLICATE n (TupleT []) ++ [BaseT (BytesT (Dynamic 0))]) acc =
    SOME (REVERSE acc ++ REPLICATE n (TupleTV []) ++
      [BaseTV (BytesT (Dynamic 0))])
Proof
  Induct >> simp[REPLICATE, evaluate_type_def, type_slot_size_def,
                 vfmConstantsTheory.word_size_def, dimword_def] >>
  simp[GSYM APPEND_ASSOC]
QED

Theorem encoder_dynamic_tuple_value_members:
  !n. values_have_types
    (REPLICATE n (TupleTV []) ++ [BaseTV (BytesT (Dynamic 0))])
    (REPLICATE n (ArrayV (TupleV [])) ++ [vyperValue$BytesV []])
Proof
  Induct >> simp[REPLICATE, value_has_type_def]
QED

Theorem encoder_dynamic_tuple_convert_members:
  !n. vyper_to_abi_list env
    (REPLICATE n (TupleT []) ++ [BaseT (BytesT (Dynamic 0))])
    (REPLICATE n (ArrayV (TupleV [])) ++ [vyperValue$BytesV []]) =
    SOME (REPLICATE n (ListV []) ++ [contractABI$BytesV []])
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_def]
QED

Theorem encoder_dynamic_tuple_abi_members:
  !n. vyper_to_abi_types env
    (REPLICATE n (TupleT []) ++ [BaseT (BytesT (Dynamic 0))]) =
    REPLICATE n (Tuple []) ++ [Bytes NONE]
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_type_def]
QED

Theorem encoder_dynamic_tuple_slot_members:
  !n. type_slot_size_list
    (REPLICATE n (TupleTV []) ++ [BaseTV (BytesT (Dynamic 0))]) = 1
Proof
  Induct >> simp[REPLICATE, type_slot_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem encoder_dynamic_tuple_source_diagnostic:
  evaluate_type env
    (TupleT (REPLICATE n (TupleT []) ++ [BaseT (BytesT (Dynamic 0))])) =
    SOME (TupleTV (REPLICATE n (TupleTV []) ++ [BaseTV (BytesT (Dynamic 0))])) /\
  value_has_type
    (TupleTV (REPLICATE n (TupleTV []) ++ [BaseTV (BytesT (Dynamic 0))]))
    (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV [])) ++ [vyperValue$BytesV []]))) /\
  vyper_to_abi env
    (TupleT (REPLICATE n (TupleT []) ++ [BaseT (BytesT (Dynamic 0))]))
    (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV [])) ++ [vyperValue$BytesV []]))) =
    SOME (ListV (REPLICATE n (ListV []) ++ [contractABI$BytesV []]))
Proof
  simp[evaluate_type_def, encoder_dynamic_tuple_evaluate_members,
       type_slot_size_def, encoder_dynamic_tuple_slot_members, dimword_def,
       value_has_type_def, encoder_dynamic_tuple_value_members,
       vyper_to_abi_def, encoder_dynamic_tuple_convert_members]
QED

Theorem encoder_dynamic_tuple_abi_cardinality_diagnostic:
  ~has_type (vyper_to_abi_type env
    (TupleT (REPLICATE (dimword (:256)) (TupleT []) ++
      [BaseT (BytesT (Dynamic 0))])))
    (ListV (REPLICATE (dimword (:256)) (ListV []) ++ [contractABI$BytesV []]))
Proof
  simp[vyper_to_abi_type_def, encoder_dynamic_tuple_abi_members,
       has_type_def, valid_length_def]
QED

Theorem encoder_dynamic_tuple_zero_prefix_span:
  !n. type_memory_size_list
    (REPLICATE n (TupleTV []) ++ [BaseTV (BytesT (Dynamic 0))]) =
    type_memory_size (BaseTV (BytesT (Dynamic 0))) /\
    type_memory_size_list (REPLICATE n (TupleTV [])) = 0
Proof
  Induct >> simp[REPLICATE, type_memory_size_def]
QED

(* The member runners do not yet expose a cardinality-free entry interface:
   abiEncoderMembersDefs.abi_encoder_members_pre_def (lines 8-19) and
   abiScratchMembers.abi_scratch_members_pre_def (lines 17-30) both require
   abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs).
   abi_encoder_complex_input_iff requires outer has_type and equal lengths.
   Thus changing each static child representative cannot remove this bound.
   abi_encoder_members_run returns one state carrying the final member
   invariant, abi_decoder_effect and abi_decode_sim; abi_scratch_members_run
   instead returns abi_scratch_effect at that same state. Their invariants
   already expose head_lengths, abi_encoder_tuple_prefix and tuple tails,
   but their entry preconditions still contain the outer typing restriction.
   Reuse therefore needs an ADDITIVE cardinality-free member input/runner
   generalization, not merely a pure source producer for the current runner.
   No existing core statement or definition is changed by these diagnostics.
   Generated theorem indexes were not available in this build layout; a
   transitive oracle/dependency audit is still required before final reuse. *)
Theorem encoder_complex_input_cardinality_bound:
  abi_encoder_input (AbiComplex infos) at av sb cap mem ==>
  LENGTH infos < dimword (:256)
Proof
  simp[abi_encoder_complex_input_iff] >> rpt strip_tac >>
  gvs[abi_encoder_tuple_type_def, has_type_def, valid_length_def]
QED

Theorem encoder_dynamic_tuple_no_same_shape_representative:
  LENGTH infos = dimword (:256) + 1 ==>
  ~abi_encoder_input (AbiComplex infos) at av sb cap mem
Proof
  strip_tac >> strip_tac >> drule encoder_complex_input_cardinality_bound >> simp[]
QED
