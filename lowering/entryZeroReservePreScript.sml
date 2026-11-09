(* The source-valid child interface needs separation, not a preallocated arena. *)
Theory entryZeroReservePre
Ancestors
  abiDecoderValidContract abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  entryCoherentMemberContract entryDecoderMemberEndpoint
  compileEnv venomState venomExecSemantics words list

Theorem entry_zero_reserve_valid_pre:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type env ty) bytes) nv /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
  (is_dynamic (vyper_to_abi_type env ty) \/
    static_length (vyper_to_abi_type env ty) <= LENGTH bytes) /\
  mem_bytes_at sb (LENGTH bytes) (abi_decode_source CALLDATALOAD ready) = bytes /\
  eval_operand src ready = SOME (n2w sb) /\
  eval_operand dst ready = SOME (n2w p) /\
  sb + LENGTH bytes < dimword (:256) /\
  p + type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live first.cs_next_var src /\
  abi_decoder_operand_live first.cs_next_var dst ==>
  abi_decoder_valid_pre ce env sf ty tv bytes nv first src dst CALLDATALOAD
    (Lit 0w) (Lit 0w) 0 sb p (p + type_memory_bytes ce ty) 0 ready
Proof
  simp[abi_decoder_valid_pre_def, abi_decoder_ranges_def,
    abi_decode_source_opcode_def, abi_decoder_operand_live_def]
QED

Theorem entry_zero_reserve_child_endpoint:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),last) /\
  fn_has_code first last fn /\
  (first.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  last.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= p /\ p + type_memory_size tv <= base_addr + cap /\
  p + type_memory_size tv < dimword (:256) /\
  abi_decoder_valid_pre ce env sf ty tv bytes nv first src dst CALLDATALOAD
    (Lit 0w) (Lit 0w) 0 sb p (p + type_memory_bytes ce ty) 0 ready /\
  fresh_vars_wrt limit_st ready /\ alloca_inv ready /\
  alloca_frontier_inv ctx fn site ready /\
  calldata_member_own fn first.cs_next_id last.cs_next_id ready /\
  FLOOKUP ready.vs_allocas oid = SOME (base_addr,cap) /\
  ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
  ready.vs_inst_idx = LENGTH first.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn ready ==>
  ?out scratch. calldata_member_success ctx fn site limit_st first last p
    (type_memory_size tv) tv nv ready out scratch /\
    entry_decoder_obs ready out /\ alloca_history fn out
Proof
  strip_tac >> drule_all entry_coherent_child_contract >>
  disch_then (qspec_then `site` (qspec_then `limit_st` (qspec_then `fn` assume_tac))) >>
  metis_tac[entry_member_child_contract_apply]
QED

val () =
  let val (base_oracles, _) = Tag.dest_tag (Thm.tag entry_coherent_child_contract)
      fun audit (th, allowed) =
        let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
        in if null axioms andalso null (Thm.hyp th) andalso
              List.all (fn name => name = "DISK_THM" orelse
                List.exists (fn a => a = name) allowed) oracles
           then () else raise Fail "entry zero reserve unexpected admission"
        end
  in audit (entry_zero_reserve_valid_pre, []);
     audit (entry_zero_reserve_child_endpoint, base_oracles)
  end;
