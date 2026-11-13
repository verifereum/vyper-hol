(* Checked syntax consumer; semantic resource obligations remain separate. *)
Theory exprSimAbiEncodeSiteBoundary
Ancestors
  exprSimAbiEncodeSiteRecovery exprSimAbiEncodeSiteSyntax
  exprSimAbiEncodeSiteEncoder exprSimAbiEncodeProducerExecution
  exprSimAbiEncodeSourceMetadata compileEnv context venomInst list

Theorem abi_encode_nonword_body_sites:
  compile_abi_encode_to_buf (SND ops) op
    (type_to_abi_enc_info sf ce (expr_type e)) ready = (len,body_end) ==>
  site_step ready body_end
Proof
  metis_tac[abi_encode_body_site_step]
QED
