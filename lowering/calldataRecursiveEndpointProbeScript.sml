(* Checked interface instances; not uniform decoder correctness. *)
Theory calldataRecursiveEndpointProbe
Ancestors
  decoderPrefixEdges calldataDynOwned abiDecoderDynamic abiEncoder
  abiDecoderContract venomState venomExecSemantics words list

Theorem terminal_header_pullback_probe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w (LENGTH vs) /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w (LENGTH vs) /\
  LENGTH vs < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block exit_lbl fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to exit_lbl
    (abi_decode_header_state iv cv cmp done (LENGTH vs) (LENGTH vs) s) ==>
  ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL calldata_header_all_fuel_pullback) >>
  goal_assum (drule_at (Pos hd)) >>
  qexistsl_tac [`srcaddr`, `p`, `next_bb`, `LENGTH vs`, `LENGTH vs`] >> simp[]
QED

Theorem empty_dynamic_offset_probe[local]:
  abi_decoder_dynamic (DecComplex T []) /\
  ~dec_info_needs_offset (DecComplex T [])
Proof
  EVAL_TAC
QED

(* Interface audit (not a correctness theorem).

   Proposed uniform contract, with Own and Safe exactly as in
   calldata_valid_bytes_owned_endpoint:

   compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
     (type_to_abi_dec_info sf ce ty) st = ((),last) /\
   fn_has_code st last fn /\
   (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
           phi_prefix_length bb.bb_instructions = 0) /\
   abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD
     (Lit 0w) sb d b cap initial /\
   last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
   alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
   Own st.cs_next_id last.cs_next_id initial /\
   FLOOKUP initial.vs_allocas oid = SOME (base_addr,capacity) /\
   (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
   base_addr <= d /\ d+type_memory_size tv <= base_addr+capacity /\
   d+type_memory_size tv < dimword (:256) /\
   ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
   initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
   ?child scratch.
     ~child.vs_halted /\ child.vs_current_bb = last.cs_current_bb /\
     child.vs_inst_idx = LENGTH last.cs_current_insts /\
     val_wf tv v /\ val_in_memory tv v d child.vs_memory /\
     fresh_vars_wrt limit_st child /\
     child.vs_call_ctx = initial.vs_call_ctx /\
     child.vs_data_section = initial.vs_data_section /\
     alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
     Own st.cs_next_id last.cs_next_id child /\
     initial.vs_alloca_next <= child.vs_alloca_next /\
     (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
       FLOOKUP child.vs_allocas id = SOME (q,k)) /\
     (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
       FLOOKUP child.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (!op. abi_decoder_operand_live st.cs_next_var op ==>
       eval_operand op child = eval_operand op initial) /\
     abi_decode_footprint_frame ((d,type_memory_size tv)::scratch) initial child /\
     (!q k. MEM (q,k) scratch ==> ?id.
       st.cs_next_id <= id /\ id < last.cs_next_id /\
       FLOOKUP child.vs_allocas id = SOME (q,k)) /\
     Safe initial child /\
     ((!fuel. mem_safe_run fuel ctx fn child) ==>
       !fuel. mem_safe_run fuel ctx fn initial).

   This is a candidate to validate, NOT an assertion that its premises suffice.
   In particular the final-block phi premise may need the customary alternative
   st.cs_blocks = last.cs_blocks for straight-line callers.

   Shallow abi_decoder_coherent_ind branch matrix:
   Base and flag: word endpoint, or bytes/string endpoint; scratch=[].
   Array, bulk: bulk endpoint; scratch=[]; no positive-stride premise.
   Array, Dynamic iterative: initialize length and index allocation; induct on
     LENGTH vs-j with H from calldata_valid_owned_header_step. Child receives
     the actual setup endpoint, fixed limit_st and restricted Own. Reassemble
     via calldata_scratch_own_reassemble and outside-ID equality. Terminal
     j=LENGTH vs uses the checked terminal_header_pullback_probe (also j=0).
   Array, Fixed: compile as members, source prefix indexed by source values;
     size zero/length zero must use empty-member handling, not offset loading.
   Tuple: same source-indexed members fold, with positional head/memory sums.
   Struct: same fold, but child env is env \\ nsid and sf is
     sf \\ nsid_to_string nsid, exactly as coherent induction requires.

   Member boundary mismatch:
   calldata_member_address_endpoint returns ep/dp observations, unchanged memory,
   source fields, allocation fields, fixed-limit freshness and both transfers.
   abi_decoder_valid_member_entry instead returns an existential prepared state
   with valid_pre and abi_decode_sim, and assumes the nonempty dynamic-head
   premise. To use validObservations on the ACTUAL endpoint, first derive its
   child source window and the two operand observations. Equality of independent
   existential states is neither provided nor needed. Ordinary member_entry uses
   abi_decoder_dynamic, whereas actual complex members use dec_info_needs_offset.
   The checked empty_dynamic_offset_probe demonstrates the excluded case.
   abiDecoderEmptyMember supplies the separate inline-empty path.

   Loop successor boundary mismatch:
   calldata_valid_owned_header_step already exports source prefix growth,
   allocation persistence, Own, scratch witnesses, frame and fixed freshness,
   but its child premise and final conclusion contain ONLY conditional Safe.
   Strengthening the child premise with unconditional pullback is not by itself
   a proof of the desired strengthened conclusion: retain the actual header,
   setup, child and backedge endpoints in its construction, then compose the
   four implications. decoderPrefixEdges exports both header and backedge
   unconditional pullbacks; member-address and array setup need their own actual
   sequence endpoints. No new per-edge header/backedge theorem is needed.
   Repeated iterations reuse existing Own scratch allocations, not fresh sites.

   Export audit:
   calldata_owned_header_terminal, calldata_header_owned_safe_transfer,
   calldata_backedge_owned_safe_transfer (calldataDynOwned) are exported;
   terminal_apply variants are local. The terminal resource result is disjunctive
   (revert or endpoint) and conditional Safe only. The valid owned header step
   is exported; its prepare/child_reach/backedge/prefix helpers are local.
   calldata_members_fixed_fn_invariant_rule is exported, but permits revert and
   propagates only conditional Safe. It does not establish the uniform contract.
   Source-valued member closure and unconditional loop induction remain missing;
   finite endpoint success does not discharge these obligations.
*)
