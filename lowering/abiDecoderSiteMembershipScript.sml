(* Actual decoder sites must belong to the running function, not old blocks. *)
Theory abiDecoderSiteMembership
Ancestors
  abiDecoderSiteResources abiDecoderCode fragExec exprLoweringProps
  compileEnv list rich_list

Theorem abi_decoder_new_code_fn_member:
  cs_extends first last /\ fn_has_code first last func /\
  abi_decoder_code_member i last /\
  (!bb. MEM bb first.cs_blocks ==> ~MEM i bb.bb_instructions) ==>
  MEM i (fn_insts func)
Proof
  strip_tac >>
  gvs[cs_extends_def, fn_has_code_def, abi_decoder_code_member_def,
      IS_PREFIX_APPEND]
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      simp[MEM_APPEND])
  >> `emitted_blocks first last = new` by
    metis_tac[emitted_blocks_append] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem abi_decoder_sites_fn_witness:
  cs_extends first last /\ fn_has_code first last func /\
  abi_decoder_code first last /\ abi_decoder_code_ids_below first /\
  id IN abi_decoder_sites first.cs_next_id last.cs_next_id last ==>
  ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
      i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]
Proof
  simp[abi_decoder_sites_member] >> strip_tac >>
  `~abi_decoder_code_member i first` by
    (gvs[abi_decoder_code_ids_below_def] >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  `MEM i (fn_insts func)` by
    (irule abi_decoder_new_code_fn_member >>
     qexistsl_tac [`first`, `last`] >> simp[] >>
     gvs[abi_decoder_code_member_def] >> metis_tac[]) >>
  drule_all abi_decoder_code_alloca >> strip_tac >>
  qexists_tac `i` >> simp[]
QED
