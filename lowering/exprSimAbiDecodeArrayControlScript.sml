(* Fetched control at the dynamic-array invariant boundaries. *)
Theory exprSimAbiDecodeArrayControl
Ancestors
  exprSimAbiDecodeArrayInvariant exprSimAbiDecodeMemberExecute abiDecoderFiniteControl
  abiDecoderExecution abiDecoderLoopData abiDecoderContract abiDecoderReentryAddress
  abiDecoderSiteEffect abiDecoderReentry abiDecoderLoopRegisters
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeScratchCover
  exprSimAbiDecodeSiteProvenance abiDecoderIndexInit
  abiDecoderArrayInitReentry abiDecoderArrayLoopInit abiDecoderCode
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

(* Control's only memory write is the registered index slot. *)
Theorem abi_array_memory_prefix_store:
  abi_array_memory_prefix tv d m k vs s /\ m = type_memory_size tv /\
  k <= n /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN {a | d <= a /\ a < d+32+n*m}) ==>
  abi_array_memory_prefix tv d m k vs (mstore slot w s)
Proof
  simp_tac bool_ss [abi_array_memory_prefix_def] >> strip_tac >>
  gen_tac >> strip_tac >>
  `val_wf tv (EL k' vs) /\ val_in_memory tv (EL k' vs) (d+32+k'*m) s.vs_memory` by
    metis_tac[] >>
  `k'*m+m <= n*m` by
    (`k'*m+m = SUC k'*m` by simp[MULT_CLAUSES, ADD_COMM] >>
     asm_rewrite_tac [] >> simp[LE_MULT_RCANCEL] >> decide_tac) >>
  irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
  qexistsl_tac [`m`, `s.vs_memory`] >>
  qpat_x_assum `m = _` (fn th => asm_simp_tac bool_ss [GSYM th]) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  Cases_on `m = 0` >- fs[mem_bytes_at_def] >>
  irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
  qpat_x_assum `!a. _` (qspec_then `MAX slot (d+32+k'*m)` mp_tac) >>
  simp[MAX_DEF] >> rpt IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem abi_array_backedge_effect:
  decode_site_resources ctx func s /\ fresh_vars_wrt limit_st s /\
  next < limit_st.cs_next_var /\ first <= next /\
  {a | slot <= a /\ a < slot+32} SUBSET writes ==>
  decode_site_effect ctx func first writes s
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s))) /\
  fresh_vars_wrt limit_st
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `decode_site_effect ctx func first writes s t` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),w) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  reverse conj_tac >- simp[] >>
  simp_tac bool_ss [decode_site_effect_def] >>
  conj_tac
  >- (irule decode_site_resources_fields >> qexists `s` >>
      simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]) >>
  conj_tac >- simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live next op` by metis_tac[abi_decoder_operand_live_mono] >>
      metis_tac[]) >>
  conj_tac
  >- simp[decode_static_frame_def, Abbr `t`, jump_to_def, mstore_def,
          update_var_def, write_memory_with_expansion_def] >>
  `decode_memory_frame writes s (mstore slot w s)` suffices_by
    (simp[decode_memory_frame_def, Abbr `t`, jump_to_def, update_var_def,
      mstore_def, write_memory_with_expansion_def]) >>
  simp_tac bool_ss [decode_memory_frame_def] >> rpt strip_tac >>
  Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
  irule mstore_mem_bytes_at_disjoint >>
  fs[SUBSET_DEF] >>
  Cases_on `p+n <= slot` >- simp[] >>
  Cases_on `slot+32 <= p` >- simp[] >>
  qpat_x_assum `!a. _ ==> a NOTIN writes` (qspec_then `MAX p slot` mp_tac) >>
  qpat_x_assum `!x. _ ==> x IN writes` (qspec_then `MAX p slot` mp_tac) >>
  simp[MAX_DEF] >> rpt IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem abi_array_body_post_backedge_context:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  idx IN outer /\ st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  first <= hdr_st.cs_next_var /\ hdr_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY (abi_decoder_operand_live hdr_st.cs_next_var) [dst;src;base_op;hi] ==>
  abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites hdr_st dst src base_op hi B bs p d n
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s)))
Proof
  strip_tac >>
  `bs = mem_bytes_at B (LENGTH bs) (mstore slot w s).vs_memory` by
    metis_tac[abi_array_body_post_store_source] >>
  qmatch_goalsub_abbrev_tac `abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites hdr_st dst src base_op hi B bs p d n t` >>
  qhdtm_x_assum `abi_array_body_post` mp_tac >>
  simp_tac bool_ss [abi_array_body_post_def, abi_array_runtime_context_def] >> strip_tac >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),w) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `!op. MEM op [dst;src;base_op;hi] ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> first_x_assum irule >>
     irule abi_decoder_operand_live_mono >> qexists `st.cs_next_var` >> fs[EVERY_MEM]) >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_fields >> qexists `s` >>
     simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]) >>
  `t.vs_memory = (mstore slot w s).vs_memory` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [abi_array_runtime_context_def] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  fs[] >> metis_tac[]
QED

Theorem abi_array_body_post_backedge_prefix:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\ j < n ==>
  abi_array_memory_prefix tv d (type_memory_bytes ce ty) (SUC j) vs
    (jump_to hdr (mstore slot w (update_var nv w s)))
Proof
  simp_tac bool_ss [abi_array_body_post_def, abi_array_loop_data_def] >> strip_tac >>
  `abi_array_memory_prefix tv d (type_memory_bytes ce ty) (SUC j) vs (mstore slot w s)` by
    (irule abi_array_memory_prefix_store >> simp_tac bool_ss [] >>
     conj_tac >- (qexists `n` >> simp[] >> decide_tac) >> simp[]) >>
  fs[abi_array_memory_prefix_def, jump_to_def, mstore_def, update_var_def] >>
  metis_tac[]
QED

Theorem abi_array_body_post_backedge_loop_data:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  idx IN outer /\ scratch SUBSET writes /\ j < n /\
  st.cs_next_var <= next /\ next < limit_st.cs_next_var ==>
  abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n (SUC j) env ty tv bs d
    (type_memory_bytes ce ty) (SUC j) vs
    (jump_to hdr (mstore slot (n2w(SUC j))
      (update_var (STRING #"%" (toString next)) (n2w(SUC j)) s)))
Proof
  strip_tac >>
  `B+LENGTH bs <= slot \/ slot+32 <= B` by
    metis_tac[abi_array_body_post_source_slot] >>
  `abi_array_memory_prefix tv d (type_memory_bytes ce ty) (SUC j) vs
    (jump_to hdr (mstore slot (n2w(SUC j))
      (update_var (STRING #"%" (toString next)) (n2w(SUC j)) s)))` by
    metis_tac[abi_array_body_post_backedge_prefix] >>
  qmatch_goalsub_abbrev_tac `abi_array_loop_data ctx func first writes origin outer scratch sites
    idx slot ip src base_op B p n (SUC j) env ty tv bs d
    (type_memory_bytes ce ty) (SUC j) vs t` >>
  qhdtm_x_assum `abi_array_body_post` mp_tac >>
  simp_tac bool_ss [abi_array_body_post_def, abi_array_loop_data_def,
    abi_array_runtime_context_def, Ldata_def] >> strip_tac >>
  `{a | slot <= a /\ a < slot+32} SUBSET writes` by
    metis_tac[abi_array_owned_slot_cover, SUBSET_TRANS] >>
  `decode_site_effect ctx func first writes s t /\ fresh_vars_wrt limit_st t` by
    (unabbrev_all_tac >> irule abi_array_backedge_effect >> simp[] >> decide_tac) >>
  `decode_site_effect ctx func first writes origin t` by
    metis_tac[decode_site_effect_trans, UNION_IDEMPOT] >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),n2w(SUC j)) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  `mload slot t = n2w(SUC j)` by
    simp[Abbr `t`, abi_decode_mload_jump, mload_mstore_same_proof] >>
  `abi_decode_load MLOAD (n2w(B+p):bytes32) t = n2w n` by
    (qpat_x_assum `abi_decode_load MLOAD _ s = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[abi_decode_load_def, w2n_n2w] >>
     `B+p < dimword(:256)` by decide_tac >>
     asm_simp_tac bool_ss [LESS_MOD] >>
     `mem_word_at (B+p) (mstore slot (n2w(SUC j))
        (update_var (STRING #"%" (toString next)) (n2w(SUC j)) s)).vs_memory =
      mem_word_at (B+p) (update_var (STRING #"%" (toString next)) (n2w(SUC j)) s).vs_memory` by
       (irule mstore_mem_word_at_disjoint >> decide_tac) >>
     fs[Abbr `t`, abi_decode_mload_jump, mload_def, mem_word_at_def, update_var_def]) >>
  simp_tac bool_ss [abi_array_loop_data_def, Ldata_def] >>
  fs[abi_decode_alloc_progress_def, EVERY_MEM] >> metis_tac[]
QED

Theorem abi_array_body_post_backedge_ready:
  abi_array_body_post ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  idx IN outer /\ scratch SUBSET writes /\ j < n /\
  st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  first <= hdr_st.cs_next_var /\ hdr_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY (abi_decoder_operand_live hdr_st.cs_next_var) [dst;src;base_op;hi;ip] /\
  hdr_st.cs_current_bb = hdr /\ hdr_st.cs_current_insts = [] ==>
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip hdr_st dst src base_op hi B bs p d n (SUC j) vs
    (jump_to hdr (mstore slot (n2w(SUC j))
      (update_var (STRING #"%" (toString next)) (n2w(SUC j)) s)))
Proof
  strip_tac >> simp_tac bool_ss [abi_array_ready_def] >>
  conj_tac
  >- (irule abi_array_body_post_backedge_context >> fs[] >> metis_tac[]) >>
  conj_tac >- metis_tac[abi_array_body_post_backedge_loop_data] >>
  conj_tac >- fs[] >>
  fs[abi_array_body_post_def, abi_decode_entry_def, jump_to_def,
    mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem abi_array_header_effect:
  decode_site_resources ctx func s /\ fresh_vars_wrt limit_st s /\
  first <= hv /\ hv+4+abi_decode_position_header_delta base_op <= limit_st.cs_next_var ==>
  decode_site_effect ctx func first writes s
    (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s)) /\
  fresh_vars_wrt limit_st
    (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s)) /\
  (!op. abi_decoder_operand_live hv op ==>
    eval_operand op (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s)) =
    eval_operand op s)
Proof
  strip_tac >> drule_all abi_decoder_position_header_registers >> strip_tac >>
  qmatch_goalsub_abbrev_tac `decode_site_effect ctx func first writes s t` >>
  `!op. abi_decoder_operand_live hv op ==> eval_operand op t = eval_operand op s` by
    simp[Abbr `t`, abi_decoder_operand_jump] >>
  `fresh_vars_wrt limit_st t` by simp[Abbr `t`] >>
  simp_tac bool_ss [] >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_fields >> qexists `s` >>
     Cases_on `base_op = Lit 0w` >>
     simp[Abbr `t`, abi_decode_position_header_state_def, jump_to_def, update_var_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ decode_static_frame s t` by
    (Cases_on `base_op = Lit 0w` >>
     simp[decode_static_frame_def, Abbr `t`, abi_decode_position_header_state_def,
       jump_to_def, update_var_def] >> simp[venom_state_component_equality]) >>
  asm_simp_tac bool_ss [decode_site_effect_def, decode_memory_frame_def, LESS_EQ_REFL] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_array_ready_header_transport:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  st.cs_next_var <= hv /\
  hv+4+abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  first <= target.cs_next_var /\ target.cs_next_var <= limit_st.cs_next_var /\
  EVERY (abi_decoder_operand_live target.cs_next_var) [dst;src;base_op;hi;ip] /\
  target.cs_current_bb = lbl /\ target.cs_current_insts = [] ==>
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip target dst src base_op hi B bs p d n j vs
    (jump_to lbl (abi_decode_position_header_state base_op hv B p j n s))
Proof
  strip_tac >>
  qhdtm_x_assum `abi_array_ready` mp_tac >>
  simp_tac bool_ss [abi_array_ready_def, abi_array_runtime_context_def,
    abi_array_loop_data_def, Ldata_def, abi_decode_entry_def] >> strip_tac >>
  `first <= hv` by decide_tac >>
  drule_all abi_array_header_effect >> strip_tac >>
  qabbrev_tac `t = jump_to lbl (abi_decode_position_header_state base_op hv B p j n s)` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
   t.vs_current_bb = lbl /\ t.vs_inst_idx = 0` by
    simp[Abbr `t`, abi_decode_position_header_state_def, jump_to_def, update_var_def] >>
  `decode_site_effect ctx func first writes origin t` by
    metis_tac[decode_site_effect_trans, UNION_IDEMPOT] >>
  `decode_site_resources ctx func t` by metis_tac[decode_site_effect_resources] >>
  `fresh_vars_wrt limit_st t` by
    (simp[Abbr `t`] >> metis_tac[]) >>
  `B+p < dimword(:256)` by decide_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    metis_tac[abi_decoder_operand_live_mono] >>
  asm_simp_tac bool_ss [abi_array_ready_def, abi_array_runtime_context_def,
    abi_array_loop_data_def, Ldata_def, abi_decode_entry_def,
    abi_decode_alloc_progress_def, abi_array_memory_prefix_def, LENGTH, EVERY_DEF] >>
  fs[EVERY_MEM, abi_array_memory_prefix_def, abi_decode_alloc_progress_def,
    abi_decode_load_def, mload_def] >> rpt conj_tac >> metis_tac[]
QED

(* The slot is an outer decoder site, although it is not a child-body site. *)
Theorem abi_array_compiled_index_outer_site:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  compile_abi_decode_dyn_loop dst src opc base_op hi ei abi_sz mem_sz
    (FST setup) (SND setup) loop_st = ((),last) /\
  abi_decode_source_opcode opc /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET outer ==>
  loop_st.cs_next_id - 2 IN outer
Proof
  strip_tac >> drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_decoder_dyn_loop_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  fs[abi_decode_sites_def, SUBSET_DEF] >> first_x_assum irule >> decide_tac
QED

Theorem abi_array_ready_exit_observations:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip last dst src base_op hi B bs p d n n vs t ==>
  abi_array_source_prefix env ty bs p n vs /\
  abi_array_memory_prefix tv d (type_memory_bytes ce ty) n vs t /\
  eval_operand dst t = SOME(n2w d) /\ fresh_vars_wrt limit_st t /\
  decode_site_effect ctx func first writes origin t /\
  abi_decode_alloc_progress sites origin t /\
  bs = mem_bytes_at B (LENGTH bs) t.vs_memory /\
  ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
  t.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  simp_tac bool_ss [abi_array_ready_def, abi_array_runtime_context_def,
    abi_array_loop_data_def, Ldata_def, abi_decode_entry_def] >> metis_tac[]
QED
