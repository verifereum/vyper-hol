(* The packet's byte bound fits after rounding because the allocation is aligned. *)
Theory bodyAbiEncodeFinishCapacityMods
Ancestors
  bodyAbiEncodePayloadLandingMods exprSimProps exprLowering compileEnv
  vfmConstants arithmetic

Theorem abi_encode_packed_finish_capacity_mods:
  let E = TypeBuiltin ann (AbiEncode ensure mid) target args;
      single = (LENGTH args = 1 /\ ~ensure);
      prefix = abi_encode_method_id_bytes mid;
      k = (case mid of NONE => 0 | SOME _ => 4);
      maxlen = abi_size_bound ce.ce_struct_fields
        (if single then lowered_value_type ce (HD args)
         else TupleT (MAP (lowered_value_type ce) args))
  in
  cap = 32 + 32 * word_size (maxlen + k) /\
  abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
    ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
    (body_end,aid,p,cap,root,len) (bytes,limit,q,Gq,tq) ==>
  val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV (prefix ++ bytes)) <= cap /\
  type_memory_bytes ce (lowered_value_type ce E) <= cap
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  reverse conj_tac
  >- (`type_memory_bytes ce
         (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) = cap` by
        (qpat_assum `cap = _` (pure_once_rewrite_tac o single) >>
         once_rewrite_tac[lowered_value_type_def] >> Cases_on `mid` >>
         simp[NoAsms, type_memory_bytes_def, word_size_def, MULT_COMM]) >>
      simp[]) >>
  `32 + LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= cap` by
    (qhdtm_x_assum `abi_encode_payload_landing_mods`
       (strip_assume_tac o SIMP_RULE bool_ss [abi_encode_payload_landing_mods_def, LET_THM]) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `n = word_size
    (abi_size_bound ce.ce_struct_fields
       (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
        else TupleT (MAP (lowered_value_type ce) args)) +
     (case mid of NONE => 0 | SOME _ => 4))` >>
  `LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= 32 * n` by decide_tac >>
  `word_size (32 * n) = n` by
    (rewrite_tac[word_size_def] >> once_rewrite_tac[MULT_COMM] >>
     irule DIV_MULT >> simp[]) >>
  drule word_size_monotone >> simp[val_store_size_def]
QED
