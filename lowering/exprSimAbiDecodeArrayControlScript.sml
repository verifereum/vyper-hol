(* Fetched control at the dynamic-array invariant boundaries. *)
Theory exprSimAbiDecodeArrayControl
Ancestors
  exprSimAbiDecodeArrayInvariant exprSimAbiDecodeMemberExecute abiDecoderFiniteControl
  abiDecoderExecution abiDecoderLoopData abiDecoderContract
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover
  exprSimAbiDecodeSiteProvenance abiDecoderIndexInit
  venomMemProofs valueEncodingProps valueEncoding finite_map pred_set
  compileEnv venomState venomInst words list arithmetic

Theorem abi_array_ready_position_ready:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  st.cs_current_insts = [] ==>
  abi_decode_position_loop_ready st.cs_current_bb ip src MLOAD base_op
    B p (n2w slot) n j s
Proof
  strip_tac >> drule abi_array_ready_loop_data >>
  simp_tac bool_ss [abi_array_loop_data_def] >> strip_tac >>
  drule abi_array_ready_entry >>
  simp_tac bool_ss [abi_decode_entry_def] >> strip_tac >>
  irule Lready_position_ready >>
  simp[Lready_def] >> metis_tac[]
QED

Theorem abi_array_ready_header_reach:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  st.cs_current_insts = [] /\
  abi_decode_position_loop_cfg fn st.cs_current_bb body_lbl exit_lbl id ip src MLOAD base_op hv /\
  src <> Var (STRING #"%" (toString hv)) /\
  base_op <> Var (STRING #"%" (toString hv)) ==>
  Dreach ctx fn s
    (jump_to (if j < n then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op hv B p j n s))
Proof
  strip_tac >> drule_all abi_array_ready_position_ready >> strip_tac >>
  drule abi_array_ready_loop_data >>
  simp_tac bool_ss [abi_array_loop_data_def, Ldata_def] >> strip_tac >>
  irule Dreach_position_ready_header >>
  simp[abi_decode_source_opcode_def] >> metis_tac[]
QED

Theorem abi_array_header_memory_prefix:
  abi_array_memory_prefix tv d m k vs s ==>
  abi_array_memory_prefix tv d m k vs
    (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s))
Proof
  Cases_on `base_op = Lit 0w` >>
  simp[abi_array_memory_prefix_def, abi_decode_position_header_state_def,
    jump_to_def, update_var_def]
QED

Theorem abi_array_ready_exit_prefix:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n n vs s ==>
  abi_array_source_prefix env ty bs p n vs /\
  abi_array_memory_prefix tv d (type_memory_bytes ce ty) n vs
    (jump_to exit_lbl (abi_decode_position_header_state base_op hv B p n n s))
Proof
  strip_tac >> drule abi_array_ready_loop_data >>
  simp_tac bool_ss [abi_array_loop_data_def] >> strip_tac >>
  metis_tac[abi_array_header_memory_prefix]
QED

Theorem abi_array_header_exit_entry:
  ~s.vs_halted /\ last.cs_current_bb = exit_lbl /\ last.cs_current_insts = [] ==>
  abi_decode_entry last
    (jump_to exit_lbl (abi_decode_position_header_state base_op hv B p n n s))
Proof
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_entry_def, abi_decode_position_header_state_def,
    jump_to_def, update_var_def]
QED

Theorem abi_array_body_post_backedge_reach:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  j < n /\
  lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = st.cs_current_insts ++
    abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  eval_operand (Var iv) s = SOME(n2w j) /\ ip <> Var nv ==>
  Dreach ctx fn s
    (jump_to hdr (mstore slot (n2w(SUC j)) (update_var nv (n2w(SUC j)) s)))
Proof
  strip_tac >>
  qhdtm_x_assum `abi_array_body_post` mp_tac >>
  simp_tac bool_ss [abi_array_body_post_def, abi_array_loop_data_def,
    Ldata_def, abi_decode_entry_def] >> strip_tac >>
  `w2n(n2w slot:bytes32) = slot` by simp[w2n_n2w] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all Dreach_backedge >> simp[]
QED

Theorem abi_array_owned_slot_cover:
  abi_decode_owned outer scratch d outsz origin /\
  FLOOKUP origin.vs_allocas idx = SOME(slot,32) /\ idx IN outer ==>
  {a | slot <= a /\ a < slot+32} SUBSET scratch
Proof
  simp[abi_decode_owned_def, abi_decode_scratch_cover_def] >> metis_tac[]
QED

Theorem abi_array_body_post_source_slot:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  idx IN outer ==>
  B+LENGTH bs <= slot \/ slot+32 <= B
Proof
  strip_tac >>
  qhdtm_x_assum `abi_array_body_post` mp_tac >>
  simp_tac bool_ss [abi_array_body_post_def, abi_array_loop_data_def] >> strip_tac >>
  ` {a | slot <= a /\ a < slot+32} SUBSET scratch` by
    metis_tac[abi_array_owned_slot_cover] >>
  drule abi_array_runtime_source >> strip_tac >>
  `0 < LENGTH bs` by (fs[abi_array_runtime_context_def] >> decide_tac) >>
  fs[SUBSET_DEF] >>
  Cases_on `B <= slot` >> Cases_on `slot < B+LENGTH bs` >>
  Cases_on `B < slot+32` >> gvs[] >>
  first_x_assum (qspec_then `MAX B slot` mp_tac) >>
  simp[MAX_DEF] >> metis_tac[LESS_EQ_REFL, DECIDE ``!x:num. x < x+32``]
QED

Theorem abi_array_index_outer_site:
  abi_decode_index_init alloc_st = (ip,loop_st) /\
  first.cs_next_id <= alloc_st.cs_next_id /\
  loop_st.cs_next_id <= last.cs_next_id /\
  abi_decode_sites first.cs_next_id last.cs_next_id SUBSET outer ==>
  alloc_st.cs_next_id IN outer
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  fs[abi_decode_sites_def, SUBSET_DEF] >> first_x_assum irule >> simp[]
QED

Theorem abi_array_body_post_store_source:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  idx IN outer ==>
  bs = mem_bytes_at B (LENGTH bs) (mstore slot w s).vs_memory
Proof
  strip_tac >> drule_all abi_array_body_post_source_slot >> strip_tac >>
  `bs = mem_bytes_at B (LENGTH bs) s.vs_memory` by
    (fs[abi_array_body_post_def] >> metis_tac[abi_array_runtime_source]) >>
  metis_tac[mstore_mem_bytes_at_disjoint]
QED
