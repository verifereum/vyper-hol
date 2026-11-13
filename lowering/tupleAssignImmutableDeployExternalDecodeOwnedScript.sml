(* Recursive source-valid decoding into an already allocated external result.
   No Bytes header, canonical encoding, or whole-call resource synthesis is assumed. *)
Theory tupleAssignImmutableDeployExternalDecodeOwned
Ancestors
  abiDecoderValidRecursive abiDecoderAppend exprSimAbiGasBridge
  abiDecoderEffect abiDecoderReentry abiDecoderValidContract abiDecodeRanges
  abiDecoderAllocation abiDecoderFrame abiDecoderTypedContract exprSimProps loweringStateRelDefs
  compileEnv venomState words finite_map

Theorem tuple_immutable_external_decode_owned_path:
  compile_abi_decode_to_buf dst src opc base_op hi
    (type_to_abi_dec_info sf ce ty) start = ((),final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  frag_gas_free start final /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf ty tv bs v start src dst opc base_op hi
    B sb d b cap initial /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_budget first last b cap initial /\
  first <= abi_decoder_entry_floor start /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  FLOOKUP initial.vs_allocas aid = SOME (d,sz) /\
  origin.cs_next_id <= aid /\ aid < start.cs_next_id /\
  type_memory_bytes ce ty <= sz /\
  local_ptrs_rel func ce scopes initial /\ local_ptrs_reserved ce start /\
  (!name lb len. local_region ce scopes initial name lb len ==>
    d + sz <= lb \/ lb + len <= d) ==>
  ?actual. gas_marked_path F ctx func initial 0 (OK actual) /\
    val_in_memory tv v d actual.vs_memory /\
    eval_operand dst actual = SOME (n2w d) /\
    abi_decoder_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    FLOOKUP actual.vs_allocas aid = SOME (d,sz) /\
    origin.cs_next_id <= aid /\ aid < start.cs_next_id /\
    type_memory_bytes ce ty <= sz /\
    (!name lb len. local_region ce scopes actual name lb len ==>
      d + sz <= lb \/ lb + len <= d) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule cs_extends_abi_decode >> strip_tac >>
  qspec_then
    `\actual. val_in_memory tv v d actual.vs_memory /\
      abi_decoder_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
        limit_st d (type_memory_bytes ce ty) b cap initial actual`
    mp_tac (Q.SPECL [`ctx`, `start`, `final`] abi_decode_sim_gas_path) >>
  disch_then (qspecl_then [`func`, `initial`] mp_tac) >>
  (impl_tac >-
    (asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >>
         mp_tac (Q.INST [`func` |-> `fn'`, `end_st` |-> `final`] abi_decoder_valid_decode) >>
         (impl_tac >- asm_simp_tac bool_ss []) >> metis_tac[]) >>
     rpt gen_tac >>
     `!op. eval_operand op (t with vs_returndata := rd) = eval_operand op t` by
       (Cases >> simp[eval_operand_def, lookup_var_def]) >>
     qpat_x_assum `!op. eval_operand op _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     pure_rewrite_tac [abi_decoder_effect_def, fresh_vars_wrt_def,
       abi_decoder_budget_def, abi_decoder_missing_def,
       abi_decoder_scratch_frame_def, abi_decode_footprint_frame_def, mload_def] >>
     asm_rewrite_tac [venom_state_accfupds] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_rewrite_tac [])) >>
  strip_tac >> fs[] >> qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  `FLOOKUP t.vs_allocas aid = SOME (d,sz)` by
    (fs[abi_decoder_effect_def, abi_decoder_scratch_frame_def] >> metis_tac[]) >>
  `eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live start.cs_next_var dst` by
    fs[abi_decoder_valid_pre_def, abi_decoder_ranges_def] >>
  `eval_operand dst t = SOME (n2w d)` by
    (fs[abi_decoder_effect_def] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `local_region ce scopes initial name lb len` by
    (irule local_region_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`start`, `scopes`, `t`] >> simp[] >>
     rpt strip_tac >>
     `abi_decoder_operand_live start.cs_next_var (Var x)` by
       fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     fs[abi_decoder_effect_def] >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def]) >>
  metis_tac[]
QED
