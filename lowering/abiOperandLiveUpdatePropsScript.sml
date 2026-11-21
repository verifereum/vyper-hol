Theory abiOperandLiveUpdateProps
Ancestors
  abiDecoderReentry ssaOperandFrame venomInst venomState arithmetic

Theorem abi_encode_live_update_open:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  strip_tac >> irule eval_operand_update_var_avoids >>
  Cases_on `op` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  metis_tac[LESS_EQ_REFL]
QED
