Theory ctorDeployMemoryRunPtrPrefixEntryPreparedSizes
Ancestors
  ctorDeployMemoryRunPtrPrefixEntryRegisterListSizes
  ctorDeployMemoryRunPtrPrefixEntryPrepared

Theorem deploy_ptr_entry_register_prepared_sizes:
  ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
  has_types (vyper_to_abi_types (type_env tops) (MAP SND fargs)) avs /\
  t.vs_data_section = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND fargs))) (ListV avs) /\
  LENGTH t.vs_data_section < dimword (:256) /\
  mem_bytes_at 0 (LENGTH t.vs_data_section) t.vs_data_section = t.vs_data_section /\
  EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
  EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
  (!j. j < LENGTH fargs ==>
    ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
      val_wf entry.type entry.value /\
      type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
      abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
        (SND (EL j fargs)) entry.type /\
      abi_decoder_metadata ce0 (type_env tops) (SND (EL j fargs)) entry.type
        (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
        (EL j avs) entry.value) /\
  compile_register_constructor_args ce0 (build_positional_args ce0 fargs) 0 0 st = (ce,st') /\
  local_ptrs_rel func ce0 [scope] t /\ fresh_vars_wrt st t /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv t /\
  (!site. alloca_frontier_inv_from (imm_len tops) ctx func site t) /\
  imm_len tops + unit_alloca_budget ctx < dimword (:256) /\
  (!aid. st.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
  ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
  t.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from (imm_len tops) t /\ t.vs_alloca_next = imm_len tops /\
  ~ctx_has_dalloca ctx /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  ?actual H qt.
    (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
    local_ptrs_rel func ce [scope] actual /\
    abi_encoder_registered_effect (frag_ids st st') [] t actual /\
    alloca_inv actual /\
    (!site. alloca_frontier_inv_from (imm_len tops) ctx func site actual) /\
    fresh_vars_wrt st' actual /\
    (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    actual.vs_data_section = t.vs_data_section /\
    actual.vs_call_ctx = t.vs_call_ctx /\ actual.vs_labels = t.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x t = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func t actual /\
    allocas_from (imm_len tops) actual /\ imm_len tops <= actual.vs_alloca_next /\
    t.vs_alloca_next <= actual.vs_alloca_next /\
    actual.vs_code = t.vs_code /\ actual.vs_outcomes = t.vs_outcomes /\
    actual.vs_tx_ctx = t.vs_tx_ctx /\ actual.vs_block_ctx = t.vs_block_ctx /\
    actual.vs_gas_readings = t.vs_gas_readings /\
    (!a. a < imm_len tops ==> read_byte a actual.vs_memory = read_byte a t.vs_memory) /\
    qt.t_mem SUBSET (tn.t_mem UNION
      {j | t.vs_alloca_next <= j /\ j < actual.vs_alloca_next}) /\
    (!j. j < t.vs_alloca_next /\ j IN qt.t_mem ==> j IN tn.t_mem) /\
    (!C. (!j. j IN C ==> j < t.vs_alloca_next) /\ DISJOINT C tn.t_mem ==>
      DISJOINT C qt.t_mem) /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel ctx func [] H qt actual) ==>
      !fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
        fuel ctx func [] G tn t) /\
    (!j. j < LENGTH fargs ==>
      ?entry d B.
        lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
        local_region ce [scope] actual (FST (EL j fargs)) d
          (type_memory_bytes ce0 (SND (EL j fargs))) /\
        FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce0 (SND (EL j fargs)))] /\
        DISJOINT B qt.t_mem /\ (!a. a IN B ==> a < actual.vs_alloca_next) /\
        (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
          val_in_memory entry.type entry.value d mem))
Proof
  strip_tac >>
  mp_tac (prefix_entry_register_suffix_sizes |> Q.ISPEC `fargs:(string # type) list` |>
    Q.SPECL [`ce0`,`ce0.ce_vars`,`type_env tops`,`fargs`,`avs`,
      `vyper_to_abi_types (type_env tops) (MAP SND (fargs:(string # type) list))`,
      `t.vs_data_section`,`scope`,`0`] |> SPEC_ALL |>
    Q.INST [`initial` |-> `t`, `site` |-> `ARB:instruction`,
      `k` |-> `imm_len tops`, `lo` |-> `imm_len tops`,
      `PG` |-> `[]`, `D` |-> `deploy_dead tops runtime_bc am tx`] |>
    SRULE []) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  strip_tac >> qexistsl [`actual`,`H`,`qt`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> asm_rewrite_tac[] >>
  (conj_tac >- (drule prefix_entry_frontier_all_sites >> simp[])) >>
  fs[]
QED
