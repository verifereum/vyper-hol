(* Atomic source-correct entry contracts with one observation/history witness. *)
Theory entryAtomicMemberContracts
Ancestors
  entryDecoderMemberEndpoint entryDecoderAtomicEndpoint abiDecoderCoherence
  calldataSourceMemberFold allocaFrontierBound abiDecoderTypedContract
  calldataMemberResourceFrame compileEnv abiEncoder exprLowering
  words list arithmetic

Theorem entry_bulk_child_contract:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
  entry_member_child_contract ce env sf ctx fn site limit_st
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> rewrite_tac[entry_member_child_contract_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [alloca_frontier_inv_def]) >>
     decide_tac) >>
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
    type_memory_size (ArrayTV tv (Dynamic maxn))` by
    fs[abi_decoder_header_def] >>
  `p + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= base_addr + cap` by simp[] >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [GSYM calldata_member_own_def]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] entry_valid_bulk_owned_endpoint)))) >>
  strip_tac >> qexistsl_tac [`child`,`[]`] >>
  pure_asm_rewrite_tac[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def, MEM, NOT_CONS_NIL,
    LESS_EQ_REFL] >> rewrite_tac[] >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  asm_rewrite_tac[]
QED

Theorem entry_base_child_contract:
  entry_member_child_contract ce env sf ctx fn site limit_st (BaseT bt) (BaseTV bt)
Proof
  Cases_on `bt`
  >~ [`BaseT (BytesT bound)`]
  >- (Cases_on `bound`
      >- (irule entry_member_word_contract >> simp[Once type_to_abi_dec_info_def]) >>
      irule entry_member_bytes_contract >> simp[]) 
  >~ [`BaseT (StringT n)`]
  >- (irule entry_member_bytes_contract >> simp[]) >>
  irule entry_member_word_contract >> simp[Once type_to_abi_dec_info_def]
QED

Theorem entry_flag_child_contract:
  entry_member_child_contract ce env sf ctx fn site limit_st (FlagT nsid) (FlagTV n)
Proof
  irule entry_member_word_contract >> simp[Once type_to_abi_dec_info_def]
QED

(* Base and flag inherit only the already audited primitive word dependency;
   bulk must remain admission-free. *)
val () = List.app (fn (name,th,allowed) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM" orelse List.exists (fn a => a = tag) allowed) oracles
     then () else raise Fail ("entry atomic contract unexpected admission: " ^ name)
  end) [("bulk",entry_bulk_child_contract, []),
        ("base",entry_base_child_contract,
         #1 (Tag.dest_tag (Thm.tag entry_member_word_contract))),
        ("flag",entry_flag_child_contract,
         #1 (Tag.dest_tag (Thm.tag entry_member_word_contract)))];
