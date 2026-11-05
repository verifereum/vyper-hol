(* Same-endpoint finite encoder contracts. *)
Theory bodyPtrAbiEncodeBaseContract
Ancestors
  bodyPtrAbiEncodePrimitive abiEncoderWindowLeaves abiEncoderWindowContract
  abiEncoderWindow abiEncoderExtendSim abiEncoderRegisteredEffect
  fragGasPathPtr bodyPtrDefs compileEnv exprLoweringProps ptrDiscipline
  venomState venomExecSemantics valueEncodingProofs valueEncoding valueEncodingProps
  abiEncoder abiEncoderInput abiEncoderOpenInput contractABI
  words finite_map pred_set list arithmetic

Theorem abi_encode_empty_strong_endpoint:
  !B K D.
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en dst src (AbiComplex []) at av B K D s ==>
  en = st /\ out = Lit 0w /\ enc at av = [] /\
  window_strong_result ctx fn st en out at av D s s
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites fn (frag_ids st en) /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
        abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  simp[window_strong_result_def, abi_encoder_window_result_def,
       mem_bytes_at_def, eval_operand_def, abi_encoder_registered_effect_refl,
       abi_encoder_extend_sim_refl, abi_encoder_extend_sim_sim,
       window_alloca_growth_def] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* Stronger than the proposed empty P-to-R instance: only the semantic entry,
   common freshness and retained coverage are needed for this no-step case. *)
Theorem abi_encode_empty_resource_contract:
  !B K D C.
  compile_abi_encode_to_buf (Var dst) src (AbiComplex []) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src (AbiComplex []) at av B K D s /\
  fresh_vars_wrt limit s /\ (0 < C ==> ptr_covers G tn dst s C) ==>
  ?t H un.
    window_strong_result ctx fn st en out at av D s t /\
    gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un (OK t) /\
    op_taint un out = {} /\
    (!q. out = Var q ==> not_fresh_at en q) /\ fresh_vars_wrt limit t /\
    (!q. not_fresh_at st q ==>
       lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
       op_taint un (Var q) = op_taint tn (Var q)) /\
    (0 < C ==> ptr_covers H un dst t C) /\
    (!i. D <= i /\ i < D+LENGTH(enc at av) ==> i NOTIN un.t_mem) /\
    mem_agree_outside
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n})
      s.vs_memory t.vs_memory /\
    (!i. i NOTIN
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n}) ==>
      (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_empty_strong_endpoint >> strip_tac >>
  `~s.vs_halted` by fs[abi_encoder_window_pre_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[gas_path_ptr_rules, op_taint_def, mem_agree_outside_def]
QED
