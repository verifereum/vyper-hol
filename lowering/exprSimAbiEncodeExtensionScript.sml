Theory exprSimAbiEncodeExtension
Ancestors
  abiEncoderExtendSim abiDecoderVarExtend varsExt execEquivParamDefs
  finite_map venomState

Theorem abi_encode_drop_fresh_bounded_extension:
  abi_decoder_vars_extend s.vs_vars (drop_fresh st s) s
Proof
  simp[abi_decoder_vars_extend_def, abi_decoder_var_map_def, drop_fresh_def,
       vsr_frame_def, DRESTRICT_FUNION_SAME,
       Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encode_extend_clean_input:
  abi_encoder_extend_sim ctx fn (drop_fresh st s) u ==>
  ?v. abi_decoder_vars_extend s.vs_vars u v /\ abi_decode_sim ctx fn s v
Proof
  simp_tac bool_ss [abi_encoder_extend_sim_def] >> strip_tac >>
  first_x_assum irule >>
  irule abi_encode_drop_fresh_bounded_extension
QED
