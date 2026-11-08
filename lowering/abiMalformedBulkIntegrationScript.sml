(* Static-window reflection and operational integration for bulk arrays. *)
Theory abiMalformedBulkIntegration
Ancestors
  abiMalformedBulkArray abiMalformedStaticReflection abiMalformedPrefix
  abiValidAggregateHeads abiValidMembers abiVyperAdmissible
  abiDecoderValidArraySetupInputs abiDecodeRanges abiMalformedNavigation
  abiDecoderContract valueEncodingProps
  abiMalformedBytesExecution abiMalformedRecursiveInterface abiMalformedBulkConstructor
  localPtrsProps abiDecoderReentry abiDecoderRange abiDecodeRanges
  abiMalformedConstructorContract abiDecoderComposition abiDecoderDynarrayPrefix
  abiDecoderBulk abiEncoder emitHelper emitHelperProps exprLoweringProps
  abiDecoderBytesBound abiDecoderGuards abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderBulkExecute abiDecoderVarSequence abiDecoderAbortReentry
  abiDecoderReentryPointer abiDecoderVarExtend fragExec freshWrites
  abiStaticLayoutProps compileEnv venomState venomInst venomExecSemantics finite_map pred_set
  abiDecoderCoherence vyperABI vyperValue contractABI list rich_list arithmetic words

Theorem abi_malformed_bulk_static_prefix:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  (n = 0 \/ ?a. has_type (vyper_to_abi_type env ty) a) /\
  n * static_length (vyper_to_abi_type env ty) <= LENGTH bs /\
  (n = 0 \/ static_length (vyper_to_abi_type env ty) < dimword (:256)) ==>
  ?avs. abi_reflected_prefix env ty bs n avs
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `n = 0`
  >- (qexists_tac `[]` >> simp[abi_reflected_prefix_def]) >>
  fs[] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qexists_tac `GENLIST (\k. dec (vyper_to_abi_type env ty)
    (abi_reflected_child (vyper_to_abi_type env ty) bs k)) n` >>
  simp_tac std_ss [abi_reflected_prefix_def, LENGTH_GENLIST] >>
  qx_gen_tac `k` >> strip_tac >> simp[EL_GENLIST] >>
  `static_length (vyper_to_abi_type env ty) * k +
   static_length (vyper_to_abi_type env ty) <= LENGTH bs` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `n * static_length (vyper_to_abi_type env ty)` >>
     simp[] >>
     `SUC k <= n` by decide_tac >>
     metis_tac[LESS_MONO_MULT, MULT_CLAUSES, MULT_COMM]) >>
  `LENGTH (abi_reflected_child (vyper_to_abi_type env ty) bs k) =
     static_length (vyper_to_abi_type env ty)` by
    simp[abi_reflected_child_def, LENGTH_TAKE, LENGTH_DROP] >>
  `abi_reflected_head_ok (vyper_to_abi_type env ty) bs k` by
    simp[abi_reflected_head_ok_def, LENGTH_DROP] >>
  simp[] >> irule abi_unclamped_static_window_reflected >>
  metis_tac[]
QED

Theorem abi_malformed_static_prefix_members:
  abi_reflected_prefix env ty bs n avs /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  avs = abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs bs
Proof
  strip_tac >> irule LIST_EQ >>
  `LENGTH avs = n` by fs[abi_reflected_prefix_def] >>
  simp[] >> qx_gen_tac `k` >> strip_tac >>
  drule_all abi_decode_array_member_EL >> simp[] >>
  disch_then kall_tac >>
  qpat_x_assum `abi_reflected_prefix _ _ _ _ _` mp_tac >>
  simp_tac std_ss [abi_reflected_prefix_def] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  simp[abi_reflected_child_def, abi_decode_member_bytes_def,
       abi_member_head_size_def, Once MULT_COMM]
QED

Theorem abi_malformed_bulk_array_reflected:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  (maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a) /\
  32 <= LENGTH bs /\ abi_head_word bs = n /\
  is_num_value (dec_number (Uint 256) (TAKE 32 bs)) /\
  n <= maxn /\ n < dimword (:256) /\
  n * static_length (vyper_to_abi_type env ty) <= LENGTH (DROP 32 bs) /\
  (n = 0 \/ static_length (vyper_to_abi_type env ty) < dimword (:256)) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) bs /\
  abi_vyper_admissible env (ArrayT ty (Dynamic maxn))
    (dec (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) bs)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?avs. abi_reflected_prefix env ty (DROP 32 bs) n avs` by
    (irule abi_malformed_bulk_static_prefix >> metis_tac[LESS_EQ_0]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  drule_all abi_malformed_static_prefix_members >> strip_tac >>
  drule abi_reflected_prefix_valid >> strip_tac >>
  drule abi_reflected_prefix_admissible >> strip_tac >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    (asm_simp_tac bool_ss [Once vyper_decode_valid_enc_def, LET_THM,
                           GSYM abi_head_word_def] >>
     qpat_x_assum `vyper_decode_valid_enc_array _ _ _ _ _` mp_tac >>
     asm_simp_tac bool_ss []) >>
  conj_tac >- simp[] >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  simp[abi_vyper_admissible_array_iff, compatible_bound_def] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  metis_tac[abi_decode_members_length, LENGTH_REPLICATE]
QED

Theorem abi_malformed_bulk_memory_reflected:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  (maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a) /\
  mem_bytes_at B L s.vs_memory = xs /\ B+L < dimword (:256) /\
  p+32+n*static_length (vyper_to_abi_type env ty) <= L /\
  mload (B+p) s = n2w n /\ n <= maxn /\ n < dimword (:256) /\
  (n = 0 \/ static_length (vyper_to_abi_type env ty) < dimword (:256)) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (DROP p xs) /\
  abi_vyper_admissible env (ArrayT ty (Dynamic maxn))
    (dec (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (DROP p xs))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `p+32 <= L /\ B+p < dimword (:256)` by decide_tac >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s =
      n2w (abi_head_word (DROP p xs)) /\
   abi_head_word (DROP p xs) < dimword (:256)` by
    (irule abi_checked_offset_load >> simp[abi_decode_source_def] >> metis_tac[]) >>
  `abi_head_word (DROP p xs) = n` by
    (fs[abi_decode_load_def, w2n_n2w, LESS_MOD] >>
     metis_tac[w2n_n2w, LESS_MOD]) >>
  `LENGTH xs = L` by metis_tac[LENGTH_mem_bytes_at] >>
  irule abi_malformed_bulk_array_reflected >>
  simp[LENGTH_DROP, DROP_DROP_T, abi_head_word_def, dec_number_def,
       is_num_value_def] >>
  metis_tac[]
QED

Theorem abi_malformed_dynarray_prefix_resource:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn stride st = (addr,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >> drule_all abi_malformed_dynarray_prefix_exact >> strip_tac >>
  irule abi_malformed_resource_register_update >>
  conj_tac >- fs[abi_malformed_entry_def] >>
  qexists_tac `s` >> simp[lookup_var_def] >>
  irule abi_malformed_resource_refl >> fs[abi_malformed_entry_def]
QED

Theorem abi_malformed_dynarray_prefix_entry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn stride st = (addr,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  abi_malformed_entry ctx func cenv cx es en sites dstid live
    base_op hi src dst B L xs p d outsz t
Proof
  strip_tac >> drule_all abi_malformed_dynarray_prefix_resource >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> fs[abi_malformed_entry_def]) >>
  `EVERY (abi_decoder_operand_live en.cs_next_var) [base_op;hi;src;dst]` by
    (fs[abi_malformed_entry_def] >>
     rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `p < dimword (:256) /\ d+outsz < dimword (:256) /\
   eval_operand dst t = SOME (n2w d) /\ eval_operand src t = SOME (n2w p)` by
    (fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >> metis_tac[]) >>
  irule abi_malformed_child_entry >> simp[] >>
  qexistsl_tac [`d`, `dst`, `outsz`, `p`, `s`, `sites`, `src`, `st`] >> simp[]
QED

Theorem abi_malformed_bulk_fresh_total:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  (maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz /\
  fresh_vars_wrt st s /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    abi_malformed_reflected_post env (ArrayT ty (Dynamic maxn)) (DROP p xs)
      ctx func cenv cx es st.cs_next_var sites dstid s t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `d+outsz < dimword (:256) /\ hi <> Lit 0w /\
   eval_operand src s = SOME (n2w p) /\ p < dimword (:256) /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L) /\ B+L < dimword (:256) /\
   mem_bytes_at B L s.vs_memory = xs` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  `L < dimword (:256)` by decide_tac >>
  drule_all abi_malformed_bulk_capacity >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> disch_tac >> fs[] >>
  qpat_x_assum `(\(addr,cs'). _) _ = _` mp_tac >>
  asm_simp_tac std_ss [] >> disch_tac >>
  `L < dimword (:256) /\ maxn*mem_sz < dimword (:256)` by decide_tac >>
  drule_all abi_malformed_dynarray_prefix_total >> strip_tac
  >- suspend "abort" >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK s1` >>
  `abi_malformed_entry ctx func cenv cx es mid sites dstid live
     base_op hi src dst B L xs p d outsz s1` by
    (drule_all abi_malformed_dynarray_prefix_entry >> simp[]) >>
  `B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
   c*mem_sz < dimword (:256) /\ 32+c*mem_sz <= outsz` by
    (conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     `c*mem_sz <= maxn*mem_sz` by simp[] >> decide_tac) >>
  `mload (B+p) s1 = n2w c` by fs[abi_decode_load_def, mload_def] >>
  `B+p < dimword (:256)` by decide_tac >>
  `mload (w2n (n2w (B+p):bytes32)) s1 = n2w c` by simp[w2n_n2w, LESS_MOD] >>
  drule_all abi_malformed_bulk_body_resource >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  disj2_tac >> qexists_tac `t` >> simp[] >>
  suspend "reflect"
QED

Resume abi_malformed_bulk_fresh_total[abort]:
  disj1_tac >> drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  drule_all run_inst_seq_abort_extends >> simp[] >> metis_tac[]
QED

Resume abi_malformed_bulk_fresh_total[reflect]:
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s s1` by
    (drule_all abi_malformed_dynarray_prefix_resource >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s1 t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`mid.cs_next_var`, `sites`] >> simp[]) >>
  drule_all abi_malformed_resource_trans >> strip_tac >>
  pure_rewrite_tac[abi_malformed_reflected_post_def] >>
  `vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (DROP p xs) /\
   abi_vyper_admissible env (ArrayT ty (Dynamic maxn))
     (dec (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (DROP p xs))`
    suffices_by metis_tac[] >>
  `DecDynArray ei mem_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule static_layout_compatible_properties >> strip_tac >>
  `c < dimword (:256)` by decide_tac >>
  `c <> 0 ==> type_memory_size tv < dimword (:256)` by
    (strip_tac >>
     `type_memory_size tv <= c*type_memory_size tv` by
       (Cases_on `c` >> fs[MULT_CLAUSES]) >>
     `c*type_memory_size tv < dimword (:256)` by metis_tac[] >>
     metis_tac[LESS_EQ_LESS_TRANS]) >>
  irule abi_malformed_bulk_memory_reflected >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`B`, `L`, `c`, `s1`] >>
      simp[] >> fs[] >> decide_tac) >>
  qexistsl_tac [`ce`, `sf`, `tv`] >> simp[] >> metis_tac[]
QED
Finalise abi_malformed_bulk_fresh_total

(* The analogous bytes helper is local to abiMalformedBytesExecution.
   Bulk adds MUL for the checked payload extent. *)
Theorem abi_malformed_bulk_step_lookup[local]:
  MEM inst.inst_opcode [ADD; MUL; AND; MSTORE; MCOPY; LT; GT; ISZERO; ASSERT; MLOAD] /\
  step_inst_base inst s = OK t ==>
  !x. ~MEM x inst.inst_outputs ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  simp[] >> strip_tac >>
  FIRST [
    (mp_tac (Q.INST [`inst` |-> `inst`, `s` |-> `s`, `t` |-> `t`]
       abi_malformed_read_step_frame) >>
     simp[fresh_write_op_def, abi_decode_source_opcode_def] >> NO_TAC),
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
     simp[exec_write2_def, AllCaseEqs(), mstore_def, mcopy_def,
       write_memory_with_expansion_def] >> rpt strip_tac >> gvs[])]
QED

Theorem abi_malformed_bulk_sequence_lookup[local]:
  !is P s t.
  EVERY (\i. MEM i.inst_opcode [ADD; MUL; AND; MSTORE; MCOPY; LT; GT; ISZERO; ASSERT; MLOAD] /\
    (!x. P x ==> ~MEM x i.inst_outputs)) is /\
  run_inst_seq is s = OK t ==>
  !x. P x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  mp_tac (Q.INST [`inst` |-> `h`, `t` |-> `v`] abi_malformed_bulk_step_lookup) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!P' s'' t'. _` (qspecl_then [`P`, `v`, `t`] mp_tac) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem abi_malformed_bulk_lookup:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  ~dec_info_needs_clamp ei /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !x. not_fresh_at st x ==> lookup_var x t = lookup_var x s
Proof
  strip_tac >> simp[lookup_var_def] >>
  match_mp_tac (Q.SPECL [`emitted_insts st en`, `not_fresh_at st`]
    abi_malformed_bulk_sequence_lookup) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, abi_decode_source_opcode_def,
    comp_bind_def, LET_THM] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    abi_decode_bulk_body_def, abi_decode_array_header_def,
    abi_decode_bulk_payload_def, abi_decode_copy_opcode_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bulk_reflected_run:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  (maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz /\
  fn_inst_ids_distinct func /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt ceiling t /\
    abi_malformed_reflected_post env (ArrayT ty (Dynamic maxn)) (DROP p xs)
      ctx func cenv cx es st.cs_next_var sites dstid s t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule abi_malformed_entry_prune >> strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_decoder_prune_fresh] >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`]
    abi_malformed_bulk_fresh_total) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  `fresh_vars_wrt ceiling t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  drule_all abi_decoder_sequence_runtime_reentry >> strip_tac >>
  rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x clean` by
    (drule abi_malformed_bulk_lookup >> disch_then (drule_at (Pos hd)) >>
     strip_tac >>
     qpat_assum `run_inst_seq _ (abi_decoder_prune_vars _ _) = OK clean`
       (mp_then Any mp_tac abi_malformed_bulk_lookup) >>
     simp[] >> rpt strip_tac >>
     fs[abi_decoder_prune_vars_def, lookup_var_def, FLOOKUP_DRESTRICT,
        abi_decoder_older_vars_def, not_fresh_at_def] >>
     qpat_assum `!t s'' x'. _` (qspecl_then [`actual`, `s`, `x`] assume_tac) >>
     qpat_x_assum `!t s'' x'. _`
       (qspecl_then [`clean`, `abi_decoder_prune_vars st.cs_next_var s`, `x`] assume_tac) >>
     fs[abi_decoder_prune_vars_def, FLOOKUP_DRESTRICT,
       abi_decoder_older_vars_def]) >>
  `local_ptrs_reserved cenv st` by fs[abi_malformed_entry_def] >>
  fs[abi_malformed_reflected_post_def] >>
  drule_all abi_malformed_resource_restore >> strip_tac >>
  fs[abi_malformed_resource_post_def, abi_decoder_prune_vars_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var s) = SOME w` by
    simp[abi_decoder_prune_eval] >>
  fs[abi_decoder_prune_vars_def] >> metis_tac[]
QED

Theorem abi_malformed_bulk_constructor:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  (maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz /\
  fn_inst_ids_distinct func ==>
  abi_malformed_constructor env (ArrayT ty (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[abi_malformed_constructor_def, vyper_to_abi_type_def, is_dynamic_def] >>
  rpt strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> fs[inst_extends_def] >>
  rpt strip_tac >> gvs[] >>
  mp_tac (Q.INST [`s` |-> `incoming`,
    `sites` |-> `abi_malformed_scratch_sites st en func`] abi_malformed_bulk_reflected_run) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_reflected_post_inst_idx, fresh_vars_wrt_def]
QED
