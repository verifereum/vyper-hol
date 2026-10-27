(* Representation boundary for relational encoding plans. *)
Theory abiEncoderSourceBridge
Ancestors
  abiEncoderProps abiEncoderAdmissible abiEncoderInput vyperABI contractABI
  compileEnv valueEncoding valueEncodingProps valueEncodingTyping
  vyperValue vyperTyping vyperMisc words list

Theorem abi_enc_plan_static_leaf:
  (!env ty ei. abi_enc_plan env ty ei ==>
     ~is_dynamic (vyper_to_abi_type env ty) ==> abi_encoder_static_leaf ei) /\
  (!env ts elems. abi_enc_plans env ts elems ==> T)
Proof
  ho_match_mp_tac abi_enc_plan_ind >>
  simp[abi_encoder_static_leaf_def, vyper_to_abi_type_def, is_dynamic_def] >>
  rpt strip_tac >> gvs[is_dynamic_def]
QED

Theorem abi_enc_plan_admissible:
  (!env ty ei. abi_enc_plan env ty ei ==> abi_encoder_admissible ei) /\
  (!env ts elems. abi_enc_plans env ts elems ==> abi_encoder_members_admissible elems)
Proof
  ho_match_mp_tac abi_enc_plan_strongind >>
  simp[abi_encoder_admissible_def] >> rpt strip_tac >>
  metis_tac[abi_enc_plan_static_leaf]
QED


Theorem enc_pre_source_end_bound:
  enc_pre st st' ops lo top tv v src outs s ==>
  src + type_memory_size tv < dimword (:256)
Proof
  simp[enc_pre_def, enc_scratch_def] >> rpt strip_tac >> decide_tac
QED

Theorem enc_pre_source_capacity_bound:
  enc_pre st st' ops lo top tv v src outs s ==>
  type_memory_size tv < dimword (:256)
Proof
  strip_tac >> drule enc_pre_source_end_bound >> decide_tac
QED

Theorem abi_enc_plan_bytes_source:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME av /\
  val_in_memory tv v sb mem /\ type_memory_size tv < dimword (:256) ==>
  abi_encoder_input (AbiBytestring n)
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) av sb
    (type_memory_size tv) mem
Proof
  rpt strip_tac >> drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_def,
      vyper_to_abi_type_def, vyper_base_to_abi_type_def, val_wf_def,
      val_in_memory_def, type_memory_size_def, abi_encoder_input_bytes_iff,
      has_type_def, valid_length_def] >> decide_tac
QED

Theorem abi_enc_plan_string_source:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME av /\
  val_in_memory tv v sb mem /\ type_memory_size tv < dimword (:256) ==>
  abi_encoder_input (AbiBytestring n)
    (vyper_to_abi_type env (BaseT (StringT n))) av sb
    (type_memory_size tv) mem
Proof
  `n2w_o_ORD = (n2w o ORD):char -> word8` by
    simp[FUN_EQ_THM, n2w_o_ORD_def] >>
  rpt strip_tac >> drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_def,
      vyper_to_abi_type_def, vyper_base_to_abi_type_def, val_wf_def,
      val_in_memory_def, type_memory_size_def, abi_encoder_input_bytes_iff,
      has_type_def, valid_length_def, n2w_o_ORD_def, combinTheory.o_DEF] >> decide_tac
QED
