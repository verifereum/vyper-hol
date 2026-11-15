(* Joint coherent decoding and member traversal on one operational path. *)
Theory abiValidAllocatedJoint
Ancestors
 abiValidAllocatedMembersJoint abiValidAllocatedMemberEntry abiValidMembers
 abiDecodePtrArrayJoint abiDecodePtrBulkJoint abiValidAllocatedBulkReach
 abiValidAllocatedBulk abiDecoderBulk abiDecoderDynarrayPrefix abiDecoderArrayHeader
 abiDecoderArrayInitExec abiDecoderBulkExecute exprPtrCleanBufferPost
 ghostPcTransportPtr instIdxIndep emitHelper emitHelperProps
 abiDecoderTypedCompose abiDecoderComposition abiDecoderVarSequence
 instSeqComposePtr stateFrame exprSimAccounts
 abiDecodePtrMemberFrame fragExec bodyPtrBopScalarOutcome
 venomExecSemantics venomInst venomMemDefs words
 allocaHistory bodyPtrBopHashSuffix entryDecoderHistoryFrame
 abiDecodePtrScalarFrame
 abiValidAllocatedComplexJoint abiValidAllocatedComplex abiValidAllocatedObservations
 abiDecoderComplexExecute abiDecoderComplexGuard ctorAbiActualWorld fragGasOriginPtr
 abiDecoderFixedMemory abiDecoderMembers abiDecoderStruct abiValidAggregateHeads
 vyperABIValid exprSimAggregateEncoding vyperTypeDefaults
 abiValidAllocatedMembers abiValidAllocatedContract abiValidAllocatedSource
 abiDecoderMemberCons abiDecoderMemberInfos abiDecoderMemberSetup
 abiDecoderCoherence abiDecoderContract abiDecoderReentry abiMalformedRecursiveInterface
 abiMalformedSiteFrame decoderGhostFramePtr bodyPtrDefs ptrDiscipline
 exprSimProps exprLoweringProps valueEncodingProps valueEncodingTyping valueEncodingDefs valueEncoding valueEncodingProofs
 abiEncoder abiDecodeRanges compileEnv loweringStateRelDefs venomState vyperABI vyperValue
 contractABI finite_map pred_set list rich_list arithmetic

val C = ``\ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
  st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
 ~ctx_has_dalloca ctx /\
abi_decode_ptr_window G tn s source (n2w B) L /\
ptr_covers G tn output s (type_memory_bytes ce ty) /\
op_prov G pos = NONE /\ op_prov G hi = NONE /\
op_taint tn pos = {} /\ op_taint tn hi = {} /\
allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s
==>
?u G' tn'.
  abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
    d (type_memory_bytes ce ty) s u /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,G',tn')) /\
  ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
  abi_decode_ptr_window G' tn' u source (n2w B) L /\
  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
     val_in_memory tv v d mem) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
     FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm /\
  (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
       ~abi_malformed_site_range
          (abi_malformed_scratch_sites st en func) s u a 1 ==>
       (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
  alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

val M = ``\tys tvs.
 !vs ctx func cenv cx es st en source hi pos output B L xs p d outsz ao vo dstid live ceiling s H0.
 abi_valid_allocated_members_entry H0 ce env sf tys tvs vs ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d outsz ao vo dstid live ceiling s ==>
 !G tn PG lo.
 ~ctx_has_dalloca ctx /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s outsz /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
 ?u G' tn'.
 abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
   (d+vo) (type_memory_size_list tvs) s u /\
 u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK u,G',tn')) /\
 ptr_covers G' tn' output u outsz /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
   tuple_in_memory vs tvs (d+vo) mem) /\
 (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!a. ~(d+vo <= a /\ a < d+vo+type_memory_size_list tvs) /\
   ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
   (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
 alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

Theorem abi_valid_allocated_joint_members_nil[local]:
 (^M) [] []
Proof
 BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
 `vs = []` by fs[abi_valid_allocated_members_entry_def,
   Once abi_to_vyper_def, abi_decode_members_def] >> gvs[] >>
 mp_tac (abi_valid_allocated_members_nil_joint |> Q.INST
   [`H` |-> `H0`, `base_op` |-> `Var source`, `dst` |-> `Var output`, `src` |-> `pos`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 qexistsl_tac [`s`, `G`, `tn`] >> simp[val_in_memory_def, type_memory_size_def]
QED

Theorem abi_valid_allocated_joint_bulk:
 type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
   DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
 (^C) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
 mp_tac (abi_valid_allocated_bulk_reach_run |> Q.INST
   [`H` |-> `H0`, `base_op` |-> `Var source`, `src` |-> `pos`, `dst` |-> `Var output`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 qhdtm_assum `abi_valid_allocated_entry`
   (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
 `DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
 drule_all abi_decoder_bulk_metadata >> strip_tac >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en)` by metis_tac[] >>
 `?addr c1 cnt c2.
    abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn abi_sz st = (addr,c1) /\
    abi_decode_array_header (Var output) addr MLOAD c1 = (cnt,c2) /\
    abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) c2 = ((),en)` by
   (drule_all abi_decode_bulk_phases >>
    disch_then (fn th =>
      qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ (DecDynArray _ _ _ _ _) _ = _`
        (mp_tac o SIMP_RULE bool_ss [th, abi_decode_bulk_body_def, comp_bind_def, LET_THM])) >>
    rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]) >>
 drule abi_decode_dynarray_position_prefix_joint_code >> strip_tac >>
 drule abi_decode_bulk_payload_joint_code >> strip_tac >>
 `?middle. emit_op MLOAD [addr] c1 = (cnt,middle) /\
    emit_void MSTORE [Var output;cnt] middle = ((),c2)` by
   (qpat_assum `abi_decode_array_header _ _ _ _ = _`
      (mp_tac o SIMP_RULE bool_ss [abi_decode_array_header_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, LET_THM]) >>
    rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]) >>
 `inst_extends c1 middle /\ inst_extends middle c2 /\
  same_blocks c1 middle /\ same_blocks middle c2` by
   metis_tac[inst_extends_emit_op, inst_extends_emit_void, emit_op_extends, emit_void_extends] >>
 drule emitted_insts_emit_op >> strip_tac >>
 drule emitted_insts_emit_void >> strip_tac >>
 `inst_extends c1 c2 /\ inst_extends st c2` by metis_tac[inst_extends_trans] >>
 `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
  same_blocks c1 c2` by
   (imp_res_tac emit_op_extends_next_var >> fs[same_blocks_def] >> decide_tac) >>
 `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 en` by
   (rpt conj_tac >> irule cs_extends_same_block >>
    fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
 `cs_extends c1 en` by metis_tac[cs_extends_trans] >>
 `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
   metis_tac[fn_has_code_split] >>
 `emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en /\
  emitted_insts c1 c2 = emitted_insts c1 middle ++ emitted_insts middle c2` by
   (`emitted_insts st en = emitted_insts st c2 ++ emitted_insts c2 en` by
      (irule emitted_insts_append >> fs[inst_extends_def]) >>
    `emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
      (irule emitted_insts_append >> fs[inst_extends_def]) >>
    conj_tac >- simp[APPEND_ASSOC] >>
    irule emitted_insts_append >> fs[inst_extends_def]) >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts c1 c2)` by
   (qpat_assum `emitted_insts c1 c2 = _` (fn th => pure_rewrite_tac[th]) >>
    simp[mk_inst_def, is_terminator_def]) >>
 `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 en)` by fs[EVERY_MEM] >>
 `?r1 r2. run_inst_seq (emitted_insts st c1) s = OK r1 /\
    run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
    run_inst_seq (emitted_insts c2 en) r2 = OK actual` by
   (qpat_assum `run_inst_seq (emitted_insts st en) s = OK actual` mp_tac >>
    qpat_assum `emitted_insts st en = _` (fn th => pure_rewrite_tac[th]) >>
    simp[bop_run_inst_seq_append_ok] >> metis_tac[]) >>
 qhdtm_assum `abi_malformed_entry`
   (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
 `alloca_inv s` by fs[stmt_state_rel_def] >>
 drule_all abi_malformed_allocated_bounds >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `d+32+maxn*type_memory_size tv <= s.vs_alloca_next /\
  d+32+maxn*type_memory_size tv < dimword (:256)` by
   (qpat_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= _` mp_tac >>
    qpat_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < _` mp_tac >>
    qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = _`
      (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `mem_sz = type_memory_size tv` (fn th => pure_rewrite_tac[th]) >>
    POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
 `B+L < dimword (:256)` by fs[abi_malformed_allocated_window_def] >>
 `B < dimword (:256)` by decide_tac >>
 `maxn*abi_sz < dimword (:256)` by
   (qpat_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < _` mp_tac >>
    qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = _`
      (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `abi_sz = type_memory_size tv` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `mem_sz = type_memory_size tv` (fn th => pure_rewrite_tac[th]) >>
    POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
 `not_fresh_at st source /\ not_fresh_at st output /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  (!x. hi = Var x ==> not_fresh_at st x)` by
   (qpat_assum `EVERY (abi_decoder_operand_live st.cs_next_var) _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `pos` >> Cases_on `hi` >>
    simp[EVERY_DEF, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
 mp_tac (abi_decode_dynarray_position_prefix_success_joint |> Q.INST
   [`sa` |-> `st`, `sb` |-> `c1`, `u` |-> `r1`, `stride` |-> `abi_sz`]) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `ar` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
 qpat_x_assum `addr = Var ar` SUBST_ALL_TAC >>
 qabbrev_tac `s1 = r1 with vs_inst_idx := LENGTH c1.cs_current_insts` >>
 qabbrev_tac `s2 = r2 with vs_inst_idx := LENGTH c2.cs_current_insts` >>
 `run_inst_seq (emitted_insts c1 c2) s1 =
    OK (r2 with vs_inst_idx := LENGTH c1.cs_current_insts) /\
  run_inst_seq (emitted_insts c2 en) s2 =
    OK (actual with vs_inst_idx := LENGTH c2.cs_current_insts)` by
   simp[Abbr `s1`, Abbr `s2`, run_inst_seq_inst_idx, exec_result_map_def] >>
 `r1.vs_halted = s.vs_halted /\ r1.vs_current_bb = s.vs_current_bb /\
  r1.vs_alloca_next = s.vs_alloca_next /\ r1.vs_memory = s.vs_memory /\
  r1.vs_labels = s.vs_labels` by
   (qpat_assum `r1 = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `lookup_var output s = SOME (n2w d)` by
   (qpat_assum `eval_operand (Var output) s = _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [eval_operand_def])) >>
 `lookup_var output r1 = SOME (n2w d)` by
   (qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
      (qspec_then `output` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
 qpat_assum `same_blocks st c1`
   (strip_assume_tac o PURE_REWRITE_RULE [same_blocks_def]) >>
 qpat_assum `abi_decode_ptr_window G1 tn1 r1 source _ _`
   (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_ptr_window_def]) >>
 qpat_assum `abi_decode_ptr_window G1 tn1 r1 ar _ _`
   (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_ptr_window_def]) >>
 qpat_assum `allocas_from lo r1` (assume_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
 qpat_assum `lookup_var output r1 = _` (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
 qpat_assum `lookup_var source r1 = _` (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
 qpat_assum `lookup_var ar r1 = _` (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
 `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
  s1.vs_inst_idx = LENGTH c1.cs_current_insts /\
  lookup_var output s1 = SOME (n2w d) /\
  s1.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_ptr_window G1 tn1 s1 source (n2w B) L /\
  abi_decode_ptr_window G1 tn1 s1 ar (n2w (B+p)) 32 /\ allocas_from lo s1` by
   simp[Abbr `s1`, abi_decode_ptr_window_def, allocas_from_def, lookup_var_def] >>
 `ptr_covers G1 tn1 output s1 (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
   (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
    simp[Abbr `s1`, lookup_var_def] >> metis_tac[]) >>
 `not_fresh_at c1 output /\ not_fresh_at c1 source /\
  (!x. pos = Var x ==> not_fresh_at c1 x)` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `B+p+32 < dimword (:256) /\ B+p+32 <= s1.vs_alloca_next` by decide_tac >>
 mp_tac (abi_decode_array_header_success_joint |> Q.INST
   [`sa` |-> `c1`, `sb` |-> `c2`, `s` |-> `s1`, `u` |-> `r2 with vs_inst_idx := LENGTH c1.cs_current_insts`,
    `addr` |-> `ar`, `a` |-> `B+p`, `cap` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
    `G` |-> `G1`, `tn` |-> `tn1`]) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `G2` (qx_choose_then `tn2` (strip_assume_tac o SRULE []))) >>
 `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
   (qpat_assum `emitted_insts c1 c2 = _` (fn th => pure_rewrite_tac[th]) >>
    simp[mk_inst_def, is_terminator_def]) >>
 `r2.vs_current_bb = r1.vs_current_bb /\ r2.vs_halted = r1.vs_halted` by
   (conj_tac
    >- (irule (run_inst_seq_preserves_field |> Q.ISPEC `\s:venom_state. s.vs_current_bb` |> BETA_RULE) >>
        qexists_tac `emitted_insts c1 c2` >> reverse conj_tac
        >- first_assum ACCEPT_TAC >> rpt strip_tac >>
        qpat_assum `step_inst_base _ _ = OK _` mp_tac >>
        qpat_assum `MEM _ (emitted_insts c1 c2)` mp_tac >>
        qpat_assum `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >>
        metis_tac[history_base_control_flow]) >>
    irule run_inst_seq_preserves_halted >> qexists_tac `emitted_insts c1 c2` >>
    simp[mk_inst_def, is_terminator_def]) >>
 qpat_assum `same_blocks c1 c2` (strip_assume_tac o PURE_REWRITE_RULE [same_blocks_def]) >>
 qpat_assum `allocas_from lo r2` (assume_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
 `~s2.vs_halted /\ s2.vs_current_bb = c2.cs_current_bb /\
  s2.vs_inst_idx = LENGTH c2.cs_current_insts /\
  s2.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo s2` by
   simp[Abbr `s2`, Abbr `s1`, allocas_from_def] >>
 `mload (B+p) s1 = mload (B+p) s` by
   simp[Abbr `s1`, mload_def] >>
 `abi_decoder_operand_live middle.cs_next_var cnt` by
   metis_tac[abi_decoder_operand_live_emit] >>
 `not_fresh_at c2 output /\ not_fresh_at c2 source /\
  (!x. pos = Var x ==> not_fresh_at c2 x) /\
  (!x. cnt = Var x ==> not_fresh_at c2 x)` by
   (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[LESS_EQ_TRANS]) >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts c1 c2)` by
   (qpat_assum `emitted_insts c1 c2 = _` (fn th => pure_rewrite_tac[th]) >>
    simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
 mp_tac (Q.SPECL [`emitted_insts c1 c2`, `r1`, `r2`] abi_valid_allocated_sequence_static) >>
 (impl_tac >- simp[]) >> strip_tac >>
 mp_tac (abi_decode_scalar_protected_operand |> Q.INST
   [`op` |-> `pos`, `s` |-> `s`, `t` |-> `r1`, `G` |-> `G`, `H` |-> `G1`,
    `tn` |-> `tn`, `tm` |-> `tn1`, `R` |-> `{x | not_fresh_at st x}`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 mp_tac (abi_decode_scalar_protected_operand |> Q.INST
   [`op` |-> `pos`, `s` |-> `s1`, `t` |-> `r2`, `G` |-> `G1`, `H` |-> `G2`,
    `tn` |-> `tn1`, `tm` |-> `tn2`, `R` |-> `{x | not_fresh_at c1 x}`]) >>
 (impl_tac >-
   (qunabbrev_tac `s1` >>
    qpat_assum `!x. not_fresh_at c1 x ==> _ /\ _ /\ _` mp_tac >>
    qpat_assum `!x. pos = Var x ==> not_fresh_at c1 x` mp_tac >>
    qpat_assum `r2.vs_labels = r1.vs_labels` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def])) >> strip_tac >>
 `lookup_var output r2 = SOME (n2w d)` by
   (qpat_assum `!x. not_fresh_at c1 x ==> _ /\ _ /\ _`
      (qspec_then `output` mp_tac) >>
    qpat_assum `lookup_var output s1 = _` mp_tac >>
    qpat_assum `not_fresh_at c1 output` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
 qpat_assum `lookup_var output r2 = _` (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
 `lookup_var output s2 = SOME (n2w d) /\
  eval_operand pos s2 = SOME (n2w p) /\
  eval_operand cnt s2 = SOME (n2w (w2n (mload (B+p) s))) /\
  op_prov G2 pos = NONE /\ op_taint tn2 pos = {} /\
  op_prov G2 cnt = NONE /\ op_taint tn2 cnt = {} /\
  ptr_covers G2 tn2 output s2 (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
   simp[Abbr `s2`, Abbr `s1`, lookup_var_def] >>
 `lookup_var source s2 = lookup_var source s1 /\
  FLOOKUP G2 source = FLOOKUP G1 source /\
  op_taint tn2 (Var source) = op_taint tn1 (Var source)` by
   (qpat_assum `!x. not_fresh_at c1 x ==> _ /\ _ /\ _`
      (qspec_then `source` mp_tac) >>
    qpat_assum `not_fresh_at c1 source` mp_tac >>
    qunabbrev_tac `s2` >> POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
 `!i. B <= i /\ i < B+L ==> i NOTIN tn.t_mem` by
   (qpat_assum `abi_decode_ptr_window G tn s source (n2w B) L` mp_tac >>
    qpat_assum `B < dimword (:256)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_ptr_window_def, w2n_n2w]) >>
 `!i. B <= i /\ i < B+L ==> (i IN tn2.t_mem <=> i IN tn1.t_mem)` by
   (rpt strip_tac >> simp[IN_DIFF] >> decide_tac) >>
 `abi_decode_ptr_window G2 tn2 s2 source (n2w B) L` by
   (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G1`, `s1`, `tn1`] >>
    simp[w2n_n2w]) >>
 mp_tac (abi_decode_bulk_payload_success_joint |> Q.INST
   [`sa` |-> `c2`, `sb` |-> `en`, `s` |-> `s2`,
    `u` |-> `actual with vs_inst_idx := LENGTH c2.cs_current_insts`,
    `n` |-> `w2n (mload (B+p) s)`, `G` |-> `G2`, `tn` |-> `tn2`,
    `cap` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]) >>
 (impl_tac >-
   (simp[] >>
    qpat_assum `p+32+w2n (mload (B+p) s)*abi_sz <= L` mp_tac >>
    qpat_assum `w2n (mload (B+p) s) <= maxn` mp_tac >>
    qpat_assum `abi_sz = type_memory_size tv` (fn th => pure_rewrite_tac[th]) >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    rpt disch_tac >> conj_tac
    >- (qpat_assum `p+32+_ <= L` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >> decide_tac) >>
    CONV_TAC (RAND_CONV (REWR_CONV MULT_COMM)) >> simp[LE_MULT_LCANCEL])) >>
 disch_then (qx_choose_then `G3` (qx_choose_then `tn3` (strip_assume_tac o SRULE []))) >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (actual with vs_inst_idx := LENGTH en.cs_current_insts),G3,tn3)` by
   (rpt gen_tac >>
    `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s1,G1,tn1)` by
      simp[Abbr `s1`] >>
    `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) [] (OK s2,G2,tn2)` by
      simp[Abbr `s2`] >>
    metis_tac[gas_origin_ptr_path_append, APPEND]) >>
 drule_all abi_valid_allocated_bulk_count >> strip_tac >>
 `LENGTH vs < dimword (:256)` by decide_tac >>
 `LENGTH (vs:value list)*type_memory_size tv <= maxn*type_memory_size tv` by
   (qpat_assum `LENGTH (vs:value list) <= maxn` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[LE_MULT_RCANCEL]) >>
 `!i. d <= i /\ i < d+32+LENGTH vs*type_memory_size tv ==> i NOTIN tn3.t_mem` by
   (qpat_assum `tn3.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `tn2.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `mload (B+p) s = _` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `mem_sz = type_memory_size tv` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `LENGTH vs < dimword (:256)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
    simp[w2n_n2w, IN_DIFF] >> decide_tac) >>
 `val_wf (ArrayTV tv (Dynamic maxn)) v` by
   (irule (cj 1 value_has_type_val_wf) >>
    irule (cj 1 vyperTypeABITheory.abi_to_vyper_well_typed) >>
    drule abi_decoder_coherent_header >> fs[abi_decoder_header_def] >> metis_tac[]) >>
 `!mem. mem_agree_outside tn3.t_mem actual.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d mem` by
   (`val_in_memory (ArrayTV tv (Dynamic (LENGTH vs)))
       (ArrayV (DynArrayV vs)) d actual.vs_memory` by
      fs[abi_valid_allocated_post_def, val_in_memory_dynarray] >>
    `val_wf (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))` by
      (qpat_assum `val_wf (ArrayTV tv (Dynamic maxn)) v` mp_tac >>
       qpat_assum `v = ArrayV (DynArrayV vs)` (fn th => pure_rewrite_tac[th]) >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[val_wf_def]) >>
    mp_tac (clean_window_value_robust |> Q.INST
      [`ty` |-> `ArrayTV tv (Dynamic (LENGTH (vs:value list)))`, `v` |-> `ArrayV (DynArrayV vs)`,
       `off` |-> `d`, `mem` |-> `actual.vs_memory`,
       `nb` |-> `32+LENGTH (vs:value list)*type_memory_size tv`, `dirty` |-> `tn3.t_mem`]) >>
    (impl_tac >-
      (qpat_assum `val_in_memory (ArrayTV tv (Dynamic (LENGTH vs)))
         (ArrayV (DynArrayV vs)) d actual.vs_memory` mp_tac >>
       qpat_assum `val_wf (ArrayTV tv (Dynamic (LENGTH vs)))
         (ArrayV (DynArrayV vs))` mp_tac >>
       qpat_assum `!i. d <= i /\ i < d+32+LENGTH (vs:value list)*_ ==> _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
       RULE_ASSUM_TAC (REWRITE_RULE [ADD_ASSOC]) >>
       simp_tac std_ss [type_memory_size_def, ADD_ASSOC] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[val_in_memory_dynarray]) >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all abi_valid_allocated_sequence_static >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
 `alloca_history func (actual with vs_inst_idx := LENGTH en.cs_current_insts)` by
   (irule entry_straight_line_alloca_history >>
    conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`s`, `st`] >> simp[]) >>
 `abi_decode_ptr_window G3 tn3 (actual with vs_inst_idx := LENGTH en.cs_current_insts)
    source (n2w B) L` by
   (qpat_assum `abi_decode_ptr_window G3 tn3 _ source (n2w B) L` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_ptr_window_def, lookup_var_def]) >>
 `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    `not_fresh_at st x /\ not_fresh_at c1 x /\ not_fresh_at c2 x` by
      (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
       metis_tac[LESS_EQ_TRANS]) >> metis_tac[]) >>
 qexistsl_tac [`actual with vs_inst_idx := LENGTH en.cs_current_insts`, `G3`, `tn3`] >>
 simp[] >>
 qpat_assum `LENGTH (vs:value list)*type_memory_size tv <= maxn*type_memory_size tv` mp_tac >>
 POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> decide_tac
QED

Theorem abi_valid_allocated_joint_members_cons[local]:
 (^C) ty tv /\ (^M) tys tvs ==> (^M) (ty::tys) (tv::tvs)
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
 BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `compile_abi_decode_complex_elems (Var output) pos MLOAD (Var source) hi
    (abi_decoder_member_infos sf ce (ty::tys)) ao vo st = ((),en)` by
   fs[abi_valid_allocated_members_entry_def] >>
 drule abi_decoder_member_cons_trace >> strip_tac >>
 mp_tac (abi_valid_allocated_members_head_entry_joint |> Q.INST
   [`H` |-> `H0`, `src` |-> `pos`]) >>
 (impl_tac >- asm_simp_tac bool_ss []) >>
 disch_then (qx_choose_then `v` (qx_choose_then `rest`
   (qx_choose_then `prepared` (qx_choose_then `out`
     (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))))) >>
 qpat_x_assum `vs = v::rest` SUBST_ALL_TAC >>
 asm "child" (mp_tac o BETA_RULE) >>
 disch_then drule >>
 disch_then (qspecl_then [`G1`, `tn1`, `PG`, `lo`] mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `after_head`
   (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 `fn_has_code st en func` by fs[abi_valid_allocated_members_entry_def] >>
 drule_all abi_decoder_member_cons_code >> strip_tac >>
 drule_all abi_valid_allocated_members_tail_entry >> strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var output) /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
    fs[abi_valid_allocated_members_entry_def, abi_malformed_entry_def, EVERY_DEF]) >>
 `abi_decoder_operand_live middle.cs_next_var (Var output) /\
  abi_decoder_operand_live middle.cs_next_var pos /\
  abi_decoder_operand_live middle.cs_next_var hi` by
   (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
    qexists_tac `st.cs_next_var` >> simp[]) >>
 `lookup_var output after_head = lookup_var output prepared` by
   (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
    `not_fresh_at st output` by
      fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    `lookup_var output after_head = lookup_var output s` by
      fs[abi_valid_allocated_members_entry_def, abi_malformed_entry_def, eval_operand_def] >>
    qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
      (qspec_then `output` mp_tac) >> simp[]) >>
 `ptr_covers G2 tn2 output after_head outsz` by
   (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
    irule ptr_covers_frame >> qexistsl_tac [`G1`, `prepared`, `tn1`] >>
    simp[] >> metis_tac[]) >>
 `op_prov G2 pos = NONE /\ op_prov G2 hi = NONE /\
  op_taint tn2 pos = {} /\ op_taint tn2 hi = {}` by
   (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
    Cases_on `pos` >> Cases_on `hi` >>
    fs[op_prov_def, op_taint_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
 asm "tail" (mp_tac o BETA_RULE) >> disch_then drule >>
 disch_then (qspecl_then [`G2`, `tn2`, `PG`, `lo`] mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `actual`
   (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
 asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
 `abi_decoder_coherent ce env sf ty tv` by
   fs[abi_valid_allocated_members_entry_def, LIST_REL_CONS1] >>
 drule abi_decoder_coherent_header >> strip_tac >>
 `type_memory_bytes ce ty = type_memory_size tv` by fs[abi_decoder_header_def] >>
 `val_wf tv v` by
   (irule (cj 1 value_has_type_val_wf) >>
    irule (cj 1 vyperTypeABITheory.abi_to_vyper_well_typed) >>
    fs[abi_decoder_header_def, abi_valid_allocated_entry_def] >> metis_tac[]) >>
 `val_footprint tv v <= type_memory_bytes ce ty` by metis_tac[val_footprint_le] >>
 `abi_malformed_destination func cenv es.scopes dstid (d+vo)
    (type_memory_bytes ce ty) after_head /\
  dstid NOTIN abi_malformed_scratch_sites end_st en func` by
   (fs[abi_valid_allocated_members_entry_def, abi_malformed_entry_def] >>
    irule abi_malformed_destination_subrange >>
    qexistsl_tac [`d`, `outsz`] >> simp[] >> fs[type_memory_size_def] >> decide_tac) >>
 drule_all abi_valid_allocated_members_cons_joint_post >> strip_tac >>
 `abi_malformed_scratch_sites middle end_st func SUBSET
    abi_malformed_scratch_sites st en func /\
  abi_malformed_scratch_sites end_st en func SUBSET
    abi_malformed_scratch_sites st en func` by
   (conj_tac >> irule abi_malformed_scratch_sites_nested >> decide_tac) >>
 `alloca_inv after_head /\ s.vs_alloca_next <= after_head.vs_alloca_next /\
  after_head.vs_alloca_next <= actual.vs_alloca_next /\
  (!id b sz. FLOOKUP after_head.vs_allocas id = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b)` by
   (fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def] >>
    imp_res_tac abi_malformed_resource_post_alloca_inv >>
    fs[abi_malformed_resource_post_def] >> metis_tac[]) >>
 `!a. ~(d+vo <= a /\ a < d+vo+type_memory_size_list (tv::tvs)) /\
    ~abi_malformed_site_range (abi_malformed_scratch_sites st en func)
      s after_head a 1 ==> (a IN tn2.t_mem <=> a IN tn.t_mem)` by
   (rpt strip_tac >>
    `~(d+vo <= a /\ a < d+vo+type_memory_bytes ce ty)` by
      (fs[type_memory_size_def] >> decide_tac) >>
    `~abi_malformed_site_range (abi_malformed_scratch_sites middle end_st func)
       prepared after_head a 1` by
      (fs[abi_malformed_site_range_def, SUBSET_DEF] >> metis_tac[]) >>
    metis_tac[]) >>
 `!a. ~(d+vo <= a /\ a < d+vo+type_memory_size_list (tv::tvs)) /\
    ~abi_malformed_site_range (abi_malformed_scratch_sites st en func)
      after_head actual a 1 ==> (a IN tn3.t_mem <=> a IN tn2.t_mem)` by
   (rpt strip_tac >>
    `~(d+(vo+type_memory_bytes ce ty) <= a /\
       a < d+(vo+type_memory_bytes ce ty)+type_memory_size_list tvs)` by
      (fs[type_memory_size_def] >> decide_tac) >>
    `~abi_malformed_site_range (abi_malformed_scratch_sites end_st en func)
       after_head actual a 1` by
      (fs[abi_malformed_site_range_def, SUBSET_DEF] >> metis_tac[]) >>
    metis_tac[]) >>
 mp_tac (abi_valid_allocated_taint_frame_trans |> Q.INST
   [`d` |-> `d+vo`, `n` |-> `type_memory_size_list (tv::tvs)`,
    `sites` |-> `abi_malformed_scratch_sites st en func`,
    `t` |-> `after_head`, `u` |-> `actual`, `dirty0` |-> `tn.t_mem`,
    `dirty1` |-> `tn2.t_mem`, `dirty2` |-> `tn3.t_mem`]) >>
 (impl_tac >- asm_simp_tac bool_ss []) >> disch_tac >>
 `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    `abi_decoder_operand_live middle.cs_next_var (Var x) /\
     abi_decoder_operand_live end_st.cs_next_var (Var x)` by
      (`st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
       conj_tac >> irule abi_decoder_operand_live_mono >>
       qexists_tac `st.cs_next_var` >> simp[]) >>
    `not_fresh_at st x` by
      fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[]) >>
 qexistsl_tac [`actual`, `G3`, `tn3`] >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_allocated_joint_members:
 !tys tvs. LIST_REL (^C) tys tvs ==> (^M) tys tvs
Proof
 Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
 simp_tac bool_ss [LIST_REL_def, abi_valid_allocated_joint_members_nil] >> strip_tac >>
 rename1 `head_ty::tys` >> rename1 `(head_tv:type_value)::tail_tvs` >>
 mp_tac (abi_valid_allocated_joint_members_cons |> Q.INST
   [`ty` |-> `head_ty`, `tv` |-> `head_tv`, `tvs` |-> `tail_tvs`]) >>
 (impl_tac >-
   (conj_tac >- (BETA_TAC >> fs[] >> first_assum ACCEPT_TAC) >>
    first_x_assum irule >> simp[])) >>
 simp[]
QED

Theorem abi_valid_allocated_joint_complex:
 LIST_REL (^C) tys tvs /\
 compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
   (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),en) /\
 fn_has_code st en func /\ fn_inst_ids_distinct func /\
 abi_malformed_entry H0 ctx func cenv cx es st
   (abi_malformed_scratch_sites st en func) dstid live
   (Var source) hi pos (Var output) B L xs p d (type_memory_size_list tvs) s /\
 LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ p <= L /\
 vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
 abi_to_vyper_list env tys
   (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs /\
 en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
 ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
 s.vs_inst_idx = LENGTH st.cs_current_insts /\
 ~ctx_has_dalloca ctx /\ abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s (type_memory_size_list tvs) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
?u G' tn'.
 abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
   d (type_memory_size_list tvs) s u /\
 u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK u,G',tn')) /\
 ptr_covers G' tn' output u (type_memory_size_list tvs) /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
   tuple_in_memory vs tvs d mem) /\
 (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!a. ~(d <= a /\ a < d+type_memory_size_list tvs) /\
   ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
   (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
 alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "children")
   (map_every assume_tac o CONJUNCTS)) >>
 drule abi_decoder_complex_trace >> strip_tac >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_complex_code >> strip_tac >>
 drule abi_decoder_member_infos_layout >> strip_tac >>
 `LENGTH xs = L` by
   (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
    metis_tac[LENGTH_mem_bytes_at]) >>
 `p + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L` by
   (drule abi_valid_members_view >> simp[LENGTH_DROP] >> decide_tac) >>
 mp_tac (abi_valid_allocated_complex_members_entry_joint |> Q.INST
   [`HZ` |-> `H0`, `src` |-> `pos`, `n` |-> `type_memory_size_list tvs`,
    `H` |-> `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]) >>
 (impl_tac >- asm_simp_tac (srw_ss()) []) >>
 disch_then (qx_choose_then `prepared`
   (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st middle)` by
   (drule abi_decoder_complex_guard_code >> simp[EVERY_CONJ]) >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all abi_valid_allocated_sequence_static >> strip_tac >>
 `op_prov G1 pos = NONE /\ op_prov G1 hi = NONE /\
  op_taint tn1 pos = {} /\ op_taint tn1 hi = {}` by
   (asm_x "children" kall_tac >> Cases_on `pos` >> Cases_on `hi` >>
    fs[abi_malformed_entry_def, EVERY_DEF, op_prov_def, op_taint_def,
       abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[]) >>
 asm "children" (fn th =>
   mp_tac (MATCH_MP (Q.SPECL [`tys`, `tvs`] abi_valid_allocated_joint_members) th)) >>
 disch_then (mp_tac o BETA_RULE) >> disch_then drule >>
 disch_then (qspecl_then [`G1`, `tn1`, `PG`, `lo`] mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `actual`
   (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
 asm_x "children" kall_tac >>
 drule_all abi_valid_allocated_complex_members_post >> strip_tac >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK actual,G2,tn2)` by
   metis_tac[gas_origin_ptr_path_append, APPEND] >>
 `abi_malformed_scratch_sites middle en func SUBSET
    abi_malformed_scratch_sites st en func` by
   (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
 `!a. ~(d <= a /\ a < d+type_memory_size_list tvs) /\
    ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s actual a 1 ==>
    (a IN tn2.t_mem <=> a IN tn.t_mem)` by
   (rpt strip_tac >>
    `~abi_malformed_site_range (abi_malformed_scratch_sites middle en func)
       prepared actual a 1` by
      (fs[abi_malformed_site_range_def, SUBSET_DEF] >> metis_tac[]) >>
    metis_tac[ADD_0]) >>
 `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    `abi_decoder_operand_live middle.cs_next_var (Var x)` by
      (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
    `not_fresh_at st x` by
      fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[]) >>
 qexistsl_tac [`actual`, `G2`, `tn2`] >> fs[] >> metis_tac[]
QED



Theorem abi_valid_allocated_joint_tuple:
 LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
 LIST_REL (^C) tys tvs ==> (^C) (TupleT tys) (TupleTV tvs)
Proof
 disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "children")) >>
 BETA_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 qhdtm_assum `abi_valid_allocated_entry`
   (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
 drule abi_decoder_coherent_header >> strip_tac >>
 `type_memory_bytes ce (TupleT tys) = type_memory_size_list tvs` by
   fs[abi_decoder_header_def, type_memory_size_def] >>
 `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
    (DROP p xs) (DROP p xs)` by
   (asm_x "children" kall_tac >>
    fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
    gvs[Once vyper_decode_valid_enc_def]) >>
 `dec (vyper_to_abi_type env (TupleT tys)) (DROP p xs) =
    ListV (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs))` by
   simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP,
     Once dec_def, abi_decode_members_value] >>
 `?vs. v = ArrayV (TupleV vs) /\ abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs` by
   (asm_x "children" kall_tac >>
    fs[Once abi_to_vyper_def, AllCaseEqs()] >> metis_tac[]) >>
 qpat_x_assum `v = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
 `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos sf ce tys)) st = ((),en)` by
   fs[abi_decoder_tuple_infos] >>
 mp_tac (abi_valid_allocated_joint_complex |> Q.INST
   [`dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`]) >>
 (impl_tac >- (conj_tac >- asm "children" ACCEPT_TAC >> fs[])) >>
 disch_then (qx_choose_then `u`
   (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
 asm_x "children" kall_tac >> qexistsl_tac [`u`, `G'`, `tn'`] >>
 fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def,
    val_in_memory_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_joint_fixed_array:
 abi_decoder_coherent ce env sf ty tv /\ (^C) ty tv ==>
 (^C) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
 disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "child")) >>
 `LIST_REL (^C) (REPLICATE n ty) (REPLICATE n tv)` by
   (simp[LIST_REL_REPLICATE_same] >> strip_tac >>
    asm "child" (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o BETA_RULE)) >>
 asm_x "child" kall_tac >>
 BETA_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 qhdtm_assum `abi_valid_allocated_entry`
   (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
 `evaluate_type env ty = SOME tv` by
   (rev_drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
 `type_memory_bytes ce (ArrayT ty (Fixed n)) = type_memory_size_list (REPLICATE n tv)` by
   (drule_at Any abi_decoder_coherent_header >>
    simp[abi_decoder_header_def, type_memory_size_def, type_memory_size_list_replicate]) >>
 `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))
    (DROP p xs) (DROP p xs)` by
   (fs[vyper_to_abi_type_def, Once vyper_decode_valid_enc_def] >>
    simp[map_replicate, vyper_decode_valid_enc_tuple_REPLICATE]) >>
 `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) (DROP p xs) = ListV
    (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs))` by
   simp[vyper_to_abi_type_def, Once dec_def, abi_decode_array_members,
     map_replicate, abi_decode_members_value] >>
 qpat_assum `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) _ = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 `LENGTH (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty))
    (DROP p xs) (DROP p xs)) = n` by
   (drule abi_valid_members_view >> strip_tac >>
    metis_tac[has_types_length, LENGTH_MAP, LENGTH_REPLICATE]) >>
 `?vs. abi_to_vyper_list env (REPLICATE n ty)
    (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs)) = SOME vs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))` by
   (fs[Once abi_to_vyper_def, make_array_value_def, AllCaseEqs()] >> metis_tac[]) >>
 `LENGTH vs = n` by metis_tac[abi_to_vyper_list_lengths, LENGTH_REPLICATE] >>
 qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
 `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
      (abi_decoder_member_infos sf ce (REPLICATE n ty))) st = ((),en)` by
   fs[abi_decoder_fixed_array_infos] >>
 mp_tac (abi_valid_allocated_joint_complex |> Q.INST
   [`tys` |-> `REPLICATE n ty`, `tvs` |-> `REPLICATE n tv`,
    `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]) >>
 (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> fs[LIST_REL_REPLICATE_same])) >>
 disch_then (qx_choose_then `u`
   (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
 qpat_x_assum `LIST_REL _ (REPLICATE n ty) (REPLICATE n tv)` kall_tac >>
 `!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Fixed n))
      (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d mem` by
   (rpt strip_tac >> irule abi_decoder_fixed_array_memory >> simp[]) >>
 `val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d u.vs_memory` by
   (irule abi_decoder_fixed_array_memory >>
    fs[abi_valid_allocated_members_post_def]) >>
 qexistsl_tac [`u`, `G'`, `tn'`] >>
 fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def] >> first_assum ACCEPT_TAC
QED
Theorem abi_valid_allocated_joint_struct:
 FLOOKUP env nsid = SOME (StructArgs args) /\
 FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
 MAP (\(name,ty,sz). (name,ty)) fields = args /\
 LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
   (MAP SND args) tvs /\
 LIST_REL (^(C |> subst [``env:nsid |-> type_args`` |-> ``(env:nsid |-> type_args) \\ nsid``,
   ``sf:string |-> (string # vyperAST$type # num) list`` |->
     ``(sf:string |-> (string # vyperAST$type # num) list) \\ nsid_to_string nsid``]))
   (MAP SND args) tvs ==>
 (^C) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
 disch_then (CONJUNCTS_THEN2 assume_tac
   (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
     (CONJUNCTS_THEN2 assume_tac (mk_asm "children"))))) >>
 `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
 `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
 `MAP (FST o SND) fields = MAP SND args` by
   (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
    irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
 BETA_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 qhdtm_assum `abi_valid_allocated_entry`
   (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
 drule abi_decoder_coherent_header >> strip_tac >>
 `type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs` by
   (`type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
      (irule type_memory_size_fields_zip >> simp[]) >>
    fs[abi_decoder_header_def, type_memory_size_def]) >>
 `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))
    (DROP p xs) (DROP p xs)` by
   (fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
    gvs[Once vyper_decode_valid_enc_def]) >>
 `dec (vyper_to_abi_type env (StructT nsid)) (DROP p xs) = ListV
    (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) (DROP p xs) (DROP p xs))` by
   simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP, Once dec_def, abi_decode_members_value] >>
 qpat_assum `dec (vyper_to_abi_type env (StructT nsid)) _ = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 drule abi_decoder_struct_values >> strip_tac >>
 qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
 drule_all abi_decoder_struct_conversion >> strip_tac >>
 `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
      (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))) st = ((),en)` by
   (drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
    simp[] >> strip_tac >> gvs[]) >>
 mp_tac (abi_valid_allocated_joint_complex |> Q.INST
   [`env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields':(string # vyperValue$value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]) >>
 (impl_tac >- (conj_tac >- asm "children" ACCEPT_TAC >> fs[])) >>
 disch_then (qx_choose_then `u`
   (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
 asm_x "children" kall_tac >> qexistsl_tac [`u`, `G'`, `tn'`] >>
 fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def,
    val_in_memory_def, fields_in_memory_tuple, MAP_ZIP] >> metis_tac[]
QED
