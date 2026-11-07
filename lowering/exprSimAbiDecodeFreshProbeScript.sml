(* The entry-side freshness diagnostic. Multiblock execution lifting is
   deliberately separate from these input/resource preservation facts. *)
Theory exprSimAbiDecodeFreshProbe
Ancestors
  exprSimAbiDecodeBuiltin abiDecoderReentry varsExt actualDecoderSites
  venomMemDefs compileEnv finite_map pred_set arithmetic exprLoweringProps

Theorem abi_decode_pruned_limit_fresh:
  start.cs_next_var <= limit_st.cs_next_var ==>
  fresh_vars_wrt limit_st (abi_decoder_prune_vars start.cs_next_var s)
Proof
  rw[fresh_vars_wrt_def, abi_decoder_prune_vars_def,
     FDOM_DRESTRICT, abi_decoder_older_vars_def] >>
  metis_tac[arithmeticTheory.GREATER_EQ, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem abi_decode_pruned_resources:
  abi_builtin_decode_site_resources ctx fn st last mn mx sz cnt p d
    (abi_decoder_prune_vars next s) <=>
  abi_builtin_decode_site_resources ctx fn st last mn mx sz cnt p d s
Proof
  simp[abi_builtin_decode_site_resources_def, abi_decoder_prune_vars_def,
       decode_site_resources_def, alloca_room_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, fmp_room_def,
       pending_alloca_size_def]
QED

Theorem abi_decode_pruned_input:
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var ==>
  eval_operand data (abi_decoder_prune_vars start.cs_next_var s) =
    eval_operand data s /\
  fresh_vars_wrt limit_st (abi_decoder_prune_vars start.cs_next_var s)
Proof
  strip_tac >> conj_tac >- simp[abi_decoder_prune_eval] >>
  irule abi_decode_pruned_limit_fresh >> simp[]
QED
