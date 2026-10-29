(* Actual ABI-encode results become ordinary tuple sources. Allocation credit
   and the incoming bump-pointer invariant establish physical ownership. *)
Theory abiBuiltinEncodeProducer
Ancestors
  abiBuiltinEncodeRun abiBuiltinEncodeInput abiBuiltinEncodeResources abiBuiltinEncodeCode
  abiBuiltinEncodeContext abiBuiltinEncodeEffect abiBuiltinAllocation abiTupleEncodeOwnedBytes
  abiTupleEncodeInput abiDecoderReentry abiDecoderAllocation abiDecoderFootprint abiDecoderLoop
  abiDecoderContract abiEncoderCounters compileEnv builtinAbi exprLowering exprLoweringProps
  valueEncoding vyperABI venomMemDefs venomState venomExecSemantics finite_map words list
  arithmetic

Theorem abi_builtin_encode_output_live:
  lower_abi_encode ensure method_id src info maxlen st = (out,final) ==>
  abi_decoder_operand_live final.cs_next_var out
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >> gvs[] >>
  irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> simp[]
QED

Theorem abi_builtin_allocate_frontier:
  alloca_next_valid s /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  p+outsz <= (abi_builtin_allocate_state site outsz s).vs_alloca_next
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def] >>
  qpat_x_assum `alloca_next_valid s`
    (mp_tac o PURE_REWRITE_RULE [alloca_next_valid_def]) >>
  disch_then (qspecl_then [`site`, `p`, `outsz`] mp_tac) >> simp[]
QED

Theorem abi_builtin_encode_output_bounds:
  abi_builtin_encode_resources st method_id sb source_cap p maxlen first last b cap s /\
  LENGTH (enc at av) <= maxlen ==>
  p < dimword (:256) /\
  maxlen+LENGTH (abi_builtin_encode_prefix method_id) < dimword (:256) /\
  LENGTH (abi_builtin_encode_prefix method_id ++ enc at av) <=
    maxlen+LENGTH (abi_builtin_encode_prefix method_id)
Proof
  simp_tac bool_ss [abi_builtin_encode_resources_def, LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `method_id` >>
  fs[abi_builtin_encode_prefix_def,
     abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length] >> decide_tac
QED

Theorem abi_builtin_encode_output_before_scratch:
  abi_builtin_encode_resources st method_id sb source_cap p maxlen first last b cap s /\
  alloca_next_valid s ==>
  p+32+maxlen+LENGTH (abi_builtin_encode_prefix method_id) <= b
Proof
  simp_tac bool_ss [abi_builtin_encode_resources_def, LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_allocate_frontier >> strip_tac >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  Cases_on `method_id` >>
  fs[abi_builtin_encode_prefix_def,
     abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length] >> decide_tac
QED

Theorem abi_builtin_allocate_next_valid:
  alloca_next_valid s ==>
  alloca_next_valid (abi_builtin_allocate_state site outsz s)
Proof
  strip_tac >> reverse (Cases_on `FLOOKUP s.vs_allocas site = NONE`)
  >- asm_simp_tac (srw_ss()) [abi_builtin_allocate_state_def] >>
  asm_simp_tac (srw_ss()) [abi_builtin_allocate_state_def, alloca_next_valid_def,
    FLOOKUP_UPDATE] >> map_every qx_gen_tac [`id`, `offset`, `extent`] >>
  Cases_on `site = id` >> gvs[] >>
  qpat_x_assum `alloca_next_valid s`
    (mp_tac o PURE_REWRITE_RULE [alloca_next_valid_def]) >>
  disch_then (qspecl_then [`id`, `offset`, `extent`] mp_tac) >> simp[] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem lower_abi_encode_produced_tuple_input:
  let n = maxlen+LENGTH (abi_builtin_encode_prefix method_id) in
  let bytes = abi_builtin_encode_prefix method_id ++ enc at av in
  lower_abi_encode ensure method_id src (type_to_abi_enc_info sf ce ty) maxlen st = (out,final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av st method_id src sb source_cap
    p maxlen first last b cap initial /\ alloca_next_valid initial /\
  type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    FLOOKUP actual.vs_allocas st.cs_next_id =
      SOME (p,maxlen+32+LENGTH (abi_builtin_encode_prefix method_id)) /\
    abi_builtin_encode_effect first last st final limit_st p (maxlen+32+LENGTH
      (abi_builtin_encode_prefix method_id)) (case method_id of NONE => 0 | SOME _ => 32)
      b cap initial actual /\
    (!hi. abi_tuple_encode_input consumer_sf ce (BaseT (BytesT (Dynamic n)))
      (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
      out final.cs_next_var actual.vs_alloca_next hi actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all lower_abi_encode_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_builtin_encode_output_live >> strip_tac >>
  qpat_assum `abi_builtin_encode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_pre_resources]) >>
  drule_all abi_builtin_encode_output_bounds >> strip_tac >>
  drule_all abi_builtin_encode_output_before_scratch >> strip_tac >>
  `b <= actual.vs_alloca_next` by
    (qpat_assum `abi_builtin_encode_effect _ _ _ _ _ _ _ _ _ _ _ _`
       (MP_TAC o CONJUNCT2 o PURE_REWRITE_RULE [abi_builtin_encode_effect_def]) >>
     strip_tac >> drule abi_decoder_budget_frontier >> simp[]) >>
  qexists_tac `actual` >> asm_rewrite_tac[] >> gen_tac >>
  irule abi_tuple_encode_owned_bytes_source_input >> asm_rewrite_tac[] >>
  qexists_tac `n2w p:bytes32` >> fs[w2n_n2w, LENGTH_APPEND] >> decide_tac
QED
