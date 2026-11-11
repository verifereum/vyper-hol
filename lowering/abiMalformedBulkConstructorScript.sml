(* Allocation-backed bulk writes for malformed-input constructor execution. *)
Theory abiMalformedBulkConstructor
Ancestors
  abiMalformedConstructorContract abiMalformedConstructorInduction
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiMalformedCopyState
  abiMalformedPruneState abiDecoderReentry abiDecoderContract
  abiBoundedLeafReflection abiDecoderBytesFrame abiDecoderVarExtend
  abiDecoderReentryPointer abiDecoderAbortReentry
  abiDecoderBytesRuntime abiDecoderBytesPhases emitHelperProps emitHelper venomInst
  exprLoweringProps localPtrsProps compileEnv loweringStateRelDefs venomMemDefs venomMemProps
  venomState venomExecSemantics valueEncoding valueEncodingDefs valueEncodingProps valueCopy abiCanonicalHeadSize
  abiDecoderBytestringCases abiDecoderCoherence exprLowering abiEncoder
  rich_list finite_map pred_set words list arithmetic

Theorem abi_malformed_destination_copy_resource:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  d <= at /\ at+n <= d+outsz /\ fn_inst_ids_distinct func ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
    (mcopy at source_addr n s)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   abi_malformed_destination func cenv es.scopes dstid d outsz s` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_destination func cenv es.scopes dstid at n s` by
    (irule abi_malformed_destination_subrange >>
     qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  qpat_x_assum `abi_malformed_destination _ _ _ _ at n s` mp_tac >>
  simp_tac bool_ss [abi_malformed_destination_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mcopy at source_addr n s)` by
    (irule abi_malformed_mcopy_state_rel >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
     rpt strip_tac >>
     `local_ptrs_rel func cenv es.scopes s` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     `alloca_inv s` by fs[stmt_state_rel_def] >>
     `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by simp[] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  ` (mcopy at source_addr n s).vs_vars = s.vs_vars /\
    (mcopy at source_addr n s).vs_allocas = s.vs_allocas /\
    (mcopy at source_addr n s).vs_alloca_next = s.vs_alloca_next` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[abi_malformed_resource_post_def] >>
  conj_tac
  >- (rpt strip_tac >>
  `allocas_non_overlapping s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  irule mem_bytes_at_mcopy_disjoint >>
  fs[allocas_non_overlapping_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  rpt strip_tac >> Cases_on `op` >>
  fs[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_malformed_bytestring_capacity:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_bytes ce ty <= outsz /\ d+outsz < dimword (:256) ==>
  32+32*((n+31) DIV 32) <= outsz /\
  n+32 < dimword (:256) /\
  d+(32+32*((n+31) DIV 32)) < dimword (:256)
Proof
  strip_tac >> drule_all abi_decoder_bytestring_cases >> strip_tac >>
  gvs[type_memory_bytes_def] >>
  `n <= 32*((n+31) DIV 32)` by
    (`(n+31) MOD 32 < 32` by simp[] >>
     qspec_then `32` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `n+31` mp_tac) >> decide_tac) >>
  decide_tac
QED

Theorem abi_malformed_source_suffix:
  mem_bytes_at B L mem = xs ==>
  mem_bytes_at (B+p) (L-p) mem = DROP p xs
Proof
  strip_tac >> Cases_on `p <= L`
  >- (mp_tac (Q.SPECL [`B`, `p`, `L-p`, `L`, `mem`] mem_bytes_at_window) >>
      simp[] >>
      `LENGTH (DROP p xs) = L-p` by metis_tac[LENGTH_DROP, LENGTH_mem_bytes_at] >>
      metis_tac[TAKE_LENGTH_ID]) >>
  `L-p = 0 /\ L <= p` by decide_tac >>
  simp[mem_bytes_at_def] >> metis_tac[LENGTH_mem_bytes_at]
QED

Theorem abi_malformed_bytestring_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_bytes ce ty <= outsz /\ base_op <> Lit 0w /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP p xs) /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) (DROP p xs)) /\
   ?t. run_inst_seq (emitted_insts st en) s = OK t /\
     fresh_vars_wrt ceiling t /\
     abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
     t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op s = SOME w ==> eval_operand op t = SOME w))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `d+outsz < dimword (:256)` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_bytestring_capacity >> strip_tac >>
  `hi <> Lit 0w /\ p < dimword (:256) /\ B+L < dimword (:256) /\
   mem_bytes_at B L s.vs_memory = xs /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst] /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L) /\
   eval_operand src s = SOME (n2w p) /\
   eval_operand dst s = SOME (n2w d)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  qsuff_tac `B+L <= d \/ d+(32+32*((n+31) DIV 32)) <= B`
  >- (disch_tac >>
  `mem_bytes_at (B+p) (L-p) s.vs_memory = DROP p xs` by
    metis_tac[abi_malformed_source_suffix] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w B) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w L) /\
   eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w p) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w d) /\
   mem_bytes_at (B+p) (L-p) (abi_decoder_prune_vars st.cs_next_var s).vs_memory = DROP p xs` by
    fs[abi_decoder_prune_eval, abi_decoder_prune_fresh, abi_decoder_prune_vars_def] >>
  drule_all abi_decoder_bytestring_reflected_total >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
      drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  disj2_tac >> simp[] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  goal_assum (drule_at Any) >> fs[abi_decoder_prune_vars_def]) >>
  fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
     abi_malformed_destination_def] >>
  `allocas_non_overlapping s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  fs[allocas_non_overlapping_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac
QED

Theorem abi_malformed_bytes_store_copy_resource:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  d <= at /\ at+32 <= d+outsz /\ ncopy <= outsz /\
  fn_inst_ids_distinct func ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
    (mcopy d source_addr ncopy (mstore at 0w s))
Proof
  strip_tac >>
  `at+32 < dimword (:256)` by (fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_malformed_destination func cenv es.scopes dstid at 32 s` by
    (irule abi_malformed_destination_subrange >>
     qexistsl_tac [`d`, `outsz`] >> fs[abi_malformed_entry_def]) >>
  `abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src (Lit (n2w at)) B L xs p at 32 s` by
    (fs[abi_malformed_entry_def, eval_operand_def,
        abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s
    (mstore at 0w s)` by
    (irule (SRULE [] (Q.INST [`vars` |-> `s.vs_vars`]
       abi_malformed_destination_store_resource)) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz (mstore at 0w s)` by
    (irule abi_malformed_child_entry >>
     `p < dimword (:256) /\ d+outsz < dimword (:256) /\
      eval_operand dst (mstore at 0w s) = SOME (n2w d) /\
      eval_operand src (mstore at 0w s) = SOME (n2w p) /\
      EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst] /\
      local_ptrs_reserved cenv st` by
       fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[LESS_EQ_REFL]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid
    (mstore at 0w s) (mcopy d source_addr ncopy (mstore at 0w s))` by
    (irule abi_malformed_destination_copy_resource >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_malformed_resource_trans >> simp[]
QED

(* The bytes tail changes only registers and memory.  This complements the
   existing memory-value theorem with the missing whole-state boundary. *)
Theorem abi_malformed_bytes_step_mask[local]:
  MEM inst.inst_opcode [ADD; NOT; AND; MSTORE; MCOPY] /\
  step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  simp[] >> strip_tac
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >>
      simp[] >> strip_tac >>
      fs[venom_state_component_equality])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >>
      simp[] >> strip_tac >>
      fs[venom_state_component_equality])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >>
      simp[] >> strip_tac >>
      fs[venom_state_component_equality]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_write2_def, AllCaseEqs(), mstore_def, mcopy_def,
       write_memory_with_expansion_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_malformed_bytes_sequence_mask[local]:
  !is s t. EVERY (\i. MEM i.inst_opcode [ADD; NOT; AND; MSTORE; MCOPY]) is /\
  run_inst_seq is s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_at (Pos last) abi_malformed_bytes_step_mask >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem abi_malformed_bytes_tail_mask[local]:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  strip_tac >> irule abi_malformed_bytes_sequence_mask >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_malformed_store_copy_mask[local]:
  mcopy d a n (mstore at w s) =
    s with vs_memory := (mcopy d a n (mstore at w s)).vs_memory
Proof
  simp_tac std_ss [mcopy_def, mstore_def, write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdfupds]
QED

Theorem abi_malformed_bytes_runtime_tail_exact:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),en) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword (:256) /\
  d+32*((c+31) DIV 32) < dimword (:256) /\
  d < dimword (:256) /\ a < dimword (:256) /\ 32+c < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    t = (mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s))
      with vs_vars := t.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all abi_decode_bytes_runtime_tail_sequence >> strip_tac >>
  drule_all abi_malformed_bytes_tail_mask >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  once_rewrite_tac [abi_malformed_store_copy_mask] >>
  qpat_x_assum `t.vs_memory = _` (mp_tac o SYM) >>
  simp_tac bool_ss [ADD_COMM] >> disch_then SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

(* Resource clients need only agreement on entry-old registers, not SUBMAP. *)
Theorem abi_malformed_resource_register_update:
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s v /\
  local_ptrs_reserved cenv st /\
  t = v with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x v) ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = v with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >>
     reverse conj_tac >- fs[abi_malformed_resource_post_def] >>
     qexists_tac `st` >> simp[lookup_var_def] >>
     fs[lookup_var_def]) >>
  `t.vs_memory = v.vs_memory /\ t.vs_allocas = v.vs_allocas /\
   t.vs_alloca_next = v.vs_alloca_next /\ t.vs_labels = v.vs_labels` by
    (qpat_assum `t = v with vs_vars := _` SUBST1_TAC >> simp[]) >>
  fs[abi_malformed_resource_post_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qexistsl_tac [`aid`, `cap`] >> simp[]) >>
  rpt strip_tac >>
  `eval_operand op v = SOME w` by metis_tac[] >>
  Cases_on `op` >> fs[eval_operand_def, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]
QED
