(* Uniform source-coherent decoder endpoint with entry observations/history. *)
Theory entryCoherentMemberContract
Ancestors
  entryAtomicMemberContracts entryAggregateMemberEndpoint entryNonbulkMemberContract
  abiDecoderCoherence exprLowering list arithmetic

Theorem entry_coherent_child_contract:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv ==>
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  map_every qid_spec_tac [`tv`,`ty`,`sf`,`env`,`ce`] >>
  ho_match_mp_tac abi_decoder_coherent_strongind >>
  rpt conj_tac
  >- simp[entry_base_child_contract]
  >- simp[entry_flag_child_contract]
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED
Resume entry_coherent_child_contract[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound`
  >- (irule entry_member_fixed_contract >> asm_rewrite_tac[]) >>
  rename1 `Dynamic maxn` >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (irule entry_nonbulk_array_child_contract >>
      asm_rewrite_tac[] >>
      simp[Once abi_decoder_coherent_cases]) >>
  irule entry_bulk_child_contract >>
  asm_rewrite_tac[] >>
  simp[Once type_to_abi_dec_info_def] >>
  gvs[]
QED
Resume entry_coherent_child_contract[tuple]:
  rpt gen_tac >> strip_tac >>
  irule entry_member_tuple_contract >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]
QED
Resume entry_coherent_child_contract[struct]:
  rpt gen_tac >> strip_tac >>
  irule entry_member_struct_contract >>
  fs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
QED
Finalise entry_coherent_child_contract

(* The only inherited admission is the audited shared
   entryDecodeProps.compile_abi_clamp_structure, through
   entry_valid_word_owned_endpoint -> entry_member_word_contract -> base/flag.
   The induction above introduces no admission; this is not a claim of
   transitive admission-freedom. *)
val () = List.app (fn (name, th, allowed) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM" orelse
          List.exists (fn a => a = tag) allowed) oracles
     then () else raise Fail ("entry uniform unexpected admission: " ^ name)
  end)
  [("uniform", entry_coherent_child_contract,
     #1 (Tag.dest_tag (Thm.tag entryDecoderMemberEndpointTheory.entry_member_word_contract))),
   ("bulk", entry_bulk_child_contract, []),
   ("fixed", entry_member_fixed_contract, []),
   ("tuple", entry_member_tuple_contract, []),
   ("struct", entry_member_struct_contract, []),
   ("nonbulk", entry_nonbulk_array_child_contract, []),
   ("induction", abi_decoder_coherent_strongind, []),
   ("cases", abi_decoder_coherent_cases, [])];
