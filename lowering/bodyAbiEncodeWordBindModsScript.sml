(* Linked word-operand result at the direct ABI-encode packing boundary. *)
Theory bodyAbiEncodeWordBindMods
Ancestors
  bodyTypeBuiltinAbiMods bodyAbiEncodeWordPackMods bodyFullPredsMods
  exprBodyPreTypingProps exprSimHypsDefs exprSimSource
  vyperTypeSystem vyperTypeABI vyperContext vyperAST compileEnv list

Theorem abi_encode_word_from_pack_mods:
  expr_body_pre_mods mods ce cx env
      (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==>
  ?N av.
    ann = BaseT (BytesT (Dynamic N)) /\ ty = TupleT [expr_type e] /\
    well_typed_type_builtin_args (AbiEncode F mid) ty [expr_type e] /\
    vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av =
      word_to_bytes (typed_val_to_w256 tv v) T /\
    LENGTH (abi_encode_method_id_bytes mid ++
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= N /\
    evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] =
      INL (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av))
Proof
  strip_tac >>
  match_mp_tac abi_encode_word_pack_source_mods >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
