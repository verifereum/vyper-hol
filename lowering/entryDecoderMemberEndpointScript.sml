(* Same-witness member contracts for entry decoding. *)
Theory entryDecoderMemberEndpoint
Ancestors
  calldataSourceMemberFold calldataMemberResourceFrame
  entryDecoderAtomicEndpoint entryDecoderEndpointValidation entryDecoderStateFrame
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiDecoderFrame
  compileEnv exprLoweringProps venomState venomExecSemantics
  words list finite_map arithmetic

Definition entry_member_child_contract_def:
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv <=>
  !bytes v src dst sb p b reserve_cap oid base_addr cap first last s.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) first = ((),last) /\
    fn_has_code first last fn /\
    (first.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit_st.cs_next_var /\
    (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= p /\ p+type_memory_size tv <= base_addr+cap /\
    p+type_memory_size tv < dimword (:256) /\
    abi_decoder_valid_pre ce env sf ty tv bytes v first src dst
      CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb p b reserve_cap s /\
    fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    calldata_member_own fn first.cs_next_id last.cs_next_id s /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    ~s.vs_halted /\ s.vs_current_bb = first.cs_current_bb /\
    s.vs_inst_idx = LENGTH first.cs_current_insts /\
    fn_inst_ids_distinct fn /\ alloca_history fn s ==>
    ?t scratch. calldata_member_success ctx fn site limit_st first last p
      (type_memory_size tv) tv v s t scratch /\
      entry_decoder_obs s t /\ alloca_history fn t
End

Theorem entry_member_child_contract_apply:
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),last) /\
  fn_has_code first last fn /\
  (first.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  last.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= p /\ p+type_memory_size tv <= base_addr+cap /\
  p+type_memory_size tv < dimword (:256) /\
  abi_decoder_valid_pre ce env sf ty tv bytes v first src dst
    CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb p b reserve_cap s /\
  fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  calldata_member_own fn first.cs_next_id last.cs_next_id s /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  ~s.vs_halted /\ s.vs_current_bb = first.cs_current_bb /\
  s.vs_inst_idx = LENGTH first.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn s ==>
  ?t scratch. calldata_member_success ctx fn site limit_st first last p
    (type_memory_size tv) tv v s t scratch /\
    entry_decoder_obs s t /\ alloca_history fn t
Proof
  rewrite_tac[entry_member_child_contract_def] >> metis_tac[]
QED

Theorem entry_member_word_contract:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  strip_tac >> rewrite_tac[entry_member_child_contract_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [GSYM calldata_member_own_def]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] entry_valid_word_owned_endpoint)))) >>
  strip_tac >> qexistsl_tac [`child`, `[]`] >>
  pure_asm_rewrite_tac[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def, MEM, NOT_CONS_NIL,
    LESS_EQ_REFL] >> rewrite_tac[]
QED


Theorem entry_member_bytes_contract:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  disch_tac >> rewrite_tac[entry_member_child_contract_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [GSYM calldata_member_own_def]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] entry_valid_bytes_owned_endpoint)))) >>
  strip_tac >> qexistsl_tac [`child`, `[]`] >>
  pure_asm_rewrite_tac[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def, MEM, NOT_CONS_NIL,
    LESS_EQ_REFL] >> rewrite_tac[]
QED

(* Word execution inherits entryDecodeProps.compile_abi_clamp_structure via
   entry_valid_word_owned_endpoint; no admission is introduced in this theory.
   Inspect named proof dependencies as well as the transitive tag check. *)
val () = List.app (fn (name,th,allowed) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM" orelse List.exists (fn a => a = tag) allowed) oracles
     then () else raise Fail ("entry member endpoint unexpected admission: " ^ name)
  end) [("apply",entry_member_child_contract_apply, []),
        ("bytes",entry_member_bytes_contract, []),
        ("word",entry_member_word_contract,
         #1 (Tag.dest_tag (Thm.tag entry_valid_word_owned_endpoint)))];
