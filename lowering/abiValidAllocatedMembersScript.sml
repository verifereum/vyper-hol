(* Specifications for ownership-backed valid heterogeneous member traversal. *)
Theory abiValidAllocatedMembers
Ancestors
  abiValidAllocatedContract abiDecoderMemberInfos abiValidMembers
  abiMalformedRecursiveInterface abiDecoderCoherence abiDecoderContract
  abiEncoder compileEnv venomState valueEncoding words list arithmetic vyperABI
  abiDecoderLoop abiDecoderEmpty abiValidAggregateHeads
  abiMalformedConstructorContract abiDecoderComplexGuard abiDecoderReentryPointer
  abiDecoderTypedContract abiDecoderSequenceReach abiDecoderReentry abiDecoderContract
  abiDecoderTypedCompose emitHelperProps venomInst freshWrites
  instIdxIndep abiMalformedSiteFrame exprLoweringProps

Definition abi_valid_allocated_type_contract_def:
  abi_valid_allocated_type_contract ce env sf ty tv <=>
  !v ctx func cenv cx es st en base_op hi src dst B L xs p d dstid live ceiling s.
    abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
      st en base_op hi src dst B L xs p d dstid live ceiling s ==>
    ?t. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t
End

Definition abi_valid_allocated_members_entry_def:
  abi_valid_allocated_members_entry ce env sf tys tvs vs ctx func cenv cx es
      st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s <=>
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    compile_abi_decode_complex_elems dst src MLOAD base_op hi
      (abi_decoder_member_infos sf ce tys) ao vo st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      base_op hi src dst B L xs p d outsz s /\
    vo + type_memory_size_list tvs <= outsz /\
    p + ao + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
      (DROP p xs) (DROP (p+ao) xs) /\
    abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP (p+ao) xs)) = SOME vs /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_valid_allocated_members_post_def:
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid q n s t <=>
    tuple_in_memory vs tvs q t.vs_memory /\ abi_decode_sim ctx func s t /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt ceiling t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) q n s t /\
    (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b)
End

Definition abi_valid_allocated_members_contract_def:
  abi_valid_allocated_members_contract ce env sf tys tvs <=>
  !vs ctx func cenv cx es st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s.
    abi_valid_allocated_members_entry ce env sf tys tvs vs ctx func cenv cx es
      st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s ==>
    ?t. abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
      (d+vo) (type_memory_size_list tvs) s t
End

Theorem abi_valid_allocated_members_nil:
  abi_valid_allocated_members_contract ce env sf [] []
Proof
  simp_tac bool_ss [abi_valid_allocated_members_contract_def,
    abi_valid_allocated_members_entry_def, abi_decoder_member_infos_def,
    Once compile_abi_decode_to_buf_def, comp_return_def,
    abi_decode_members_def, Once abi_to_vyper_def,
    MAP, SUM, LIST_REL_EL_EQN] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qexists_tac `s` >>
  simp[abi_valid_allocated_members_post_def, val_in_memory_def,
    abi_decode_sim_refl, abi_valid_allocated_frame_refl,
    abi_malformed_resource_refl] >>
  fs[abi_malformed_entry_def] >> irule abi_malformed_resource_refl >> simp[]
QED

(* Definition probe: a dynamic empty fixed array has no source byte bound.
   The bounded Complex decoder nevertheless checks src+0 <= hi. *)
Theorem abi_valid_allocated_empty_dynamic_position_probe[local]:
  is_dynamic (contractABI$Array (SOME 0) (contractABI$Bytes NONE)) /\
  vyper_decode_valid_enc (contractABI$Array (SOME 0) (contractABI$Bytes NONE))
    (DROP 1 ([]:byte list)) /\
  ~((1w:256 word) <= 0w)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, wordsTheory.word_le_n2w] >> EVAL_TAC >> simp[bitTheory.NOT_BIT_GT_TWOEXP]
QED

(* The empty value is independent of the offset which the compiler skips. *)
Theorem abi_valid_allocated_empty_conversion:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] ==>
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) =
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs')
Proof
  strip_tac >> gvs[abiDecoderOffsetTheory.abi_decoder_empty_dynamic_translation] >>
  drule abi_decoder_empty_fixed_array_value >> simp[]
QED

(* A real nonempty dynamic child has a readable head, hence its actual
   position is inside the payload. Empty children use the inline head. *)
Theorem abi_valid_allocated_dynamic_position:
  LENGTH xs = L /\
  vyper_decode_valid_enc at (DROP p xs) /\ is_dynamic at /\
  (!elem. at <> contractABI$Array (SOME 0) elem) ==>
  p + 32 <= L
Proof
  strip_tac >> drule_all abi_valid_dynamic_head_min >>
  simp[LENGTH_DROP] >> decide_tac
QED


Theorem abi_valid_allocated_empty_sequence:
  type_to_abi_dec_info sf ce ty = DecComplex dynamic [] /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    fresh_vars_wrt ceiling t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecComplex dynamic []) st = ((),en)` by metis_tac[] >>
  `abi_decode_complex_head_guard src hi 0 st = ((),en)` by
    fs[abi_decode_empty_complex_phases] >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)` by
    fs[EVERY_CONJ] >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w p) /\
   hi <> Lit 0w /\ L < dimword (:256) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w L) /\
   fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decoder_prune_eval, abi_decoder_prune_fresh, EVERY_DEF] >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    abi_decode_empty_complex_sequence >>
  disch_then (qspecl_then [`p`, `abi_decoder_prune_vars st.cs_next_var s`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `L` >> simp[])) >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  `EVERY (\i. (fresh_write_op i.inst_opcode \/ abi_decode_source_opcode i.inst_opcode) /\
       EVERY (\x. ~not_fresh_at st x) i.inst_outputs) (emitted_insts st en)` by
    (drule_all abi_malformed_complex_guard_writes >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid s actual` by
    (irule abi_malformed_read_sequence_resource >>
     conj_tac >- (qexists_tac `emitted_insts st en` >> simp[] >>
       drule_all abi_malformed_complex_guard_writes >> simp[]) >>
     fs[abi_malformed_entry_def]) >>
  drule_all abi_malformed_read_sequence_frame >> strip_tac >>
  qexists_tac `actual` >> simp[] >>
  qpat_x_assum `actual = _` SUBST1_TAC >> simp[]
QED

Theorem abi_valid_allocated_empty_dynamic:
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
    st en base_op hi src dst B L xs p d dstid live ceiling s ==>
  ?t. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
    d (type_memory_bytes ce ty) s t
Proof
  strip_tac >> drule_all abi_valid_allocated_empty_sequence >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule_all abi_decoder_empty_descriptor_value >> strip_tac >>
  `compile_abi_decode_to_buf dst src MLOAD base_op hi (DecComplex T []) st = ((),en)` by metis_tac[] >>
  `abi_decode_complex_head_guard src hi 0 st = ((),en)` by
    fs[abi_decode_empty_complex_phases] >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `inst_extends st en` by
    (irule abi_decoder_inst_extends_prefix >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by
    (drule abi_malformed_complex_guard_writes >>
     simp_tac bool_ss [EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac
     >- metis_tac[fresh_write_op_simple] >>
     gvs[abi_decode_source_opcode_def, is_terminator_def]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  qhdtm_assum `abi_malformed_resource_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  simp[abi_valid_allocated_post_def, fresh_vars_wrt_def,
    abi_malformed_resource_post_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
    abi_valid_allocated_frame_def, abi_malformed_site_range_def] >>
  fs[fresh_vars_wrt_def]
QED
