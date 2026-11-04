(* Pruning old loop temporaries creates a fresh proof state without changing
   live operands, source bytes, reservations or typed decoder observations. *)
Theory abiDecoderReentry
Ancestors
  abiDecoderVarExtend abiDecoderTypedContract abiDecoderCoherence abiDecoderContract
  abiDecoderFrame emitHelperProps exprLoweringProps compileEnv venomState
  emitHelper abiDecodeRanges valueEncoding finite_map pred_set arithmetic

Definition abi_decoder_older_vars_def:
  abi_decoder_older_vars next =
    {x:string | !n. next <= n ==> x <> STRING #"%" (toString n)}
End

Definition abi_decoder_operand_live_def:
  abi_decoder_operand_live next op <=>
    case op of Var x => x IN abi_decoder_older_vars next | _ => T
End

Definition abi_decoder_prune_vars_def:
  abi_decoder_prune_vars next s =
    s with vs_vars := DRESTRICT s.vs_vars (abi_decoder_older_vars next)
End

Theorem abi_decoder_operand_live_fresh:
  fresh_vars_wrt st s /\ eval_operand op s = SOME v ==>
  abi_decoder_operand_live st.cs_next_var op
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  strip_tac >> rename1 `eval_operand (Var name) s = SOME v` >>
  qx_gen_tac `n` >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `s`, `Var name`, `v`, `name`, `n`]
    fresh_vars_wrt_eval_operand) >> asm_simp_tac (srw_ss()) [GREATER_EQ]
QED

Theorem abi_decoder_operand_live_mono:
  first <= next /\ abi_decoder_operand_live first op ==>
  abi_decoder_operand_live next op
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem abi_decoder_operand_live_emit:
  emit_op opc ops st = (v,st') ==> abi_decoder_operand_live st'.cs_next_var v
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  qx_gen_tac `n` >> strip_tac >> irule fresh_var_distinct >> decide_tac
QED

Theorem abi_decoder_prune_fresh:
  fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)
Proof
  pure_rewrite_tac [fresh_vars_wrt_def, abi_decoder_prune_vars_def] >> rpt strip_tac >>
  fs[FDOM_DRESTRICT, abi_decoder_older_vars_def, GREATER_EQ] >> metis_tac[]
QED

Theorem abi_decoder_prune_extension:
  abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars next s) s
Proof
  `FUNION (DRESTRICT s.vs_vars (abi_decoder_older_vars next)) s.vs_vars = s.vs_vars`
    by simp[GSYM SUBMAP_FUNION_ABSORPTION] >>
  simp[abi_decoder_vars_extend_def, abi_decoder_var_map_def,
       abi_decoder_prune_vars_def, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decoder_prune_eval:
  abi_decoder_operand_live next op ==>
  eval_operand op (abi_decoder_prune_vars next s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_prune_vars_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DRESTRICT]
QED

Theorem abi_decoder_prune_source[simp]:
  abi_decode_source opc (abi_decoder_prune_vars next s) = abi_decode_source opc s
Proof
  simp[abi_decode_source_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_prune_reservation[simp]:
  abi_decoder_reservation first last b cap (abi_decoder_prune_vars next s) <=>
  abi_decoder_reservation first last b cap s
Proof
  simp[abi_decoder_reservation_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_prune_ranges:
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi ==>
  (abi_decoder_ranges opc hi src dst sb len d sz b cap (abi_decoder_prune_vars next s) <=>
   abi_decoder_ranges opc hi src dst sb len d sz b cap s)
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_ranges_def] >>
  asm_simp_tac bool_ss [abi_decoder_prune_eval]
QED

Theorem abi_decoder_pre_prune:
  abi_decoder_metadata ce env ty tv di av v /\
  abi_decoder_reservation st.cs_next_id last b cap s /\
  abi_decoder_ranges opc hi src dst sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    d (type_memory_bytes ce ty) b cap s /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_pre_def] >>
  asm_simp_tac bool_ss [abi_decoder_prune_fresh, abi_decoder_prune_source,
    abi_decoder_prune_reservation, abi_decoder_prune_ranges]
QED
