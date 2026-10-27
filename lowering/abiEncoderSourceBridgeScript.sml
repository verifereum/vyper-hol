(* Representation boundary for relational encoding plans. *)
Theory abiEncoderSourceBridge
Ancestors
  abiEncoderProps abiEncoderAdmissible abiEncoderInput vyperABI contractABI
  compileEnv valueEncoding valueEncodingProps vyperTyping vyperMisc words list

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
