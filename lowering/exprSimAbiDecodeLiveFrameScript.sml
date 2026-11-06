Theory exprSimAbiDecodeLiveFrame
Ancestors
  exprSimAbiDecodeConsumerProbe abiDecoderSiteEffect abiDecoderReentry
  compileEnv venomState finite_map pred_set

Theorem abi_decode_old_var_live:
  not_fresh_at st x <=> abi_decoder_operand_live st.cs_next_var (Var x)
Proof
  simp[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def]
QED

Theorem abi_decode_live_operand_closed:
  decode_site_effect ctx fn next writes s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op (t with <|vs_returndata := rd; vs_prev_bb := prev|>) = SOME w
Proof
  strip_tac >> drule_all decode_site_effect_live >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_old_var_frame:
  decode_site_effect ctx fn st.cs_next_var writes s t /\
  not_fresh_at st x /\ lookup_var x s = SOME w ==>
  lookup_var x (t with <|vs_returndata := rd; vs_prev_bb := prev|>) = SOME w
Proof
  strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    simp[GSYM abi_decode_old_var_live] >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all abi_decode_live_operand_closed >> simp[eval_operand_def]
QED

Theorem abi_decode_reserved_local_lookup:
  local_ptrs_reserved ce st /\ local_ptrs_rel func ce scopes s /\
  decode_site_effect ctx fn st.cs_next_var writes s t /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  lookup_var p (t with <|vs_returndata := rd; vs_prev_bb := prev|>) = lookup_var p s
Proof
  strip_tac >>
  `not_fresh_at st p` by metis_tac[local_ptrs_reserved_def] >>
  `?w. lookup_var p s = SOME w` by metis_tac[local_ptrs_rel_def] >>
  drule_all abi_decode_old_var_frame >> simp[]
QED

Theorem abi_decode_reserved_local_region:
  local_ptrs_reserved ce st /\ local_ptrs_rel func ce scopes s /\
  decode_site_effect ctx fn st.cs_next_var writes s t ==>
  (local_region ce scopes (t with <|vs_returndata := rd; vs_prev_bb := prev|>) name lo sz <=>
   local_region ce scopes s name lo sz)
Proof
  strip_tac >> irule abi_decode_local_region_transport >>
  metis_tac[abi_decode_reserved_local_lookup]
QED

Theorem abi_decode_reserved_immutable_operand:
  local_ptrs_reserved ce st /\
  decode_site_effect ctx fn st.cs_next_var writes s t /\
  ce.ce_imm_alloca = SOME op /\ eval_operand op s = SOME w ==>
  eval_operand op (t with <|vs_returndata := rd; vs_prev_bb := prev|>) = SOME w
Proof
  strip_tac >> irule abi_decode_live_operand_closed >>
  qexistsl_tac [`ctx`, `fn`, `st.cs_next_var`, `s`, `writes`] >>
  asm_rewrite_tac [] >>
  Cases_on `op` >> simp[abi_decoder_operand_live_def] >>
  fs[local_ptrs_reserved_def, abi_decoder_older_vars_def, not_fresh_at_def]
QED
