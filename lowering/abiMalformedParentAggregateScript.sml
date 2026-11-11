(* Shared checked head guard and aggregate member execution boundary. *)
Theory abiMalformedParentAggregate
Ancestors
  abiMalformedConstructorContract abiMalformedMembersFold abiMalformedMembers
  abiMalformedLeafProbe abiMalformedMemberSetup abiDecoderComplexGuard abiDecoderComplexHead
  abiDecoderReentry abiDecoderAbortReentry abiDecoderReentryPointer
  abiDecoderVarSequence abiMalformedRecursiveInterface abiDecoderContract
  exprLoweringProps localPtrsProps abiEncoder emitHelper emitHelperProps
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderCode abiDecoderCounters
  abiDecoderAppend abiVyperAdmissible contractABI vyperABI valueEncoding
  fragExec compileEnv loweringStateRelDefs venomState venomExecSemantics words list arithmetic

Theorem abi_malformed_aggregate_guard_run:
  abi_decode_complex_head_guard src hi H st = ((),en) /\
  H < dimword (:256) /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ p+H <= L /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t)
Proof
  strip_tac >>
  `hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
   eval_operand hi s = SOME (n2w L) /\ p < dimword (:256) /\
   L < dimword (:256) /\
   abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >> decide_tac) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)` by
    fs[EVERY_CONJ] >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w p) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w L) /\
   fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  `comp_bind (emit_op ADD [src; Lit (n2w H)])
      (\e. compile_abi_decode_range_check src e hi) st = ((),en)` by
    fs[abi_decode_complex_head_guard_def] >>
  `eval_operand (Lit (n2w H)) (abi_decoder_prune_vars st.cs_next_var s) =
     SOME (n2w H : bytes32)` by simp[eval_operand_def] >>
  drule_all (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`,
      `sz` |-> `Lit (n2w H)`] abi_aggregate_head_guard_total) >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  `p+H <= L` by
    (qpat_x_assum `w2n (n2w p) + H <= w2n (n2w L)` mp_tac >>
     simp[w2n_n2w]) >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s actual` by
    (irule abi_malformed_read_sequence_resource >>
     conj_tac
     >- (qexists_tac `emitted_insts st en` >> simp[] >>
         drule_all abi_malformed_complex_guard_writes >> simp[]) >>
     fs[abi_malformed_entry_def]) >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_aggregate_guard_fragment:
  abi_decode_complex_head_guard src hi H st = ((),en) /\
  H < dimword (:256) /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling incoming /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz incoming ==>
  frag_exec ctx st en (\s. s = incoming)
    (\t. p+H <= L /\
      abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid incoming t /\
      fresh_vars_wrt ceiling t) (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  `en.cs_next_var <= ceiling.cs_next_var` by fs[] >>
  drule_all abi_malformed_aggregate_guard_run >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_resource_post_inst_idx, fresh_vars_wrt_def]
QED


Theorem abi_malformed_aggregate_fragment:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex dynamic (abi_decoder_member_infos sf ce tys)) st = ((),en) /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  abi_malformed_members_contract ce env sf tys tvs /\
  EVERY (assignable_type env) tys /\
  EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys /\
  type_memory_size_list tvs < dimword (:256) /\
  type_memory_size_list tvs <= outsz /\
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) < dimword (:256) /\
  fn_inst_ids_distinct func /\ fn_has_code st en func /\
  en.cs_next_var <= ceiling.cs_next_var /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d outsz incoming /\ fresh_vars_wrt ceiling incoming ==>
  frag_exec ctx st en (\s. s = incoming)
    (\u. vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
      abi_vyper_admissible_list env tys
        (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) /\
      abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
        (abi_malformed_scratch_sites st en func) dstid incoming u /\
      fresh_vars_wrt ceiling u) (\r. ?v. r = Abort Revert_abort v)
Proof
  simp_tac bool_ss [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def] >>
  simp_tac bool_ss [LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),mid)` >>
  qmatch_asmsub_abbrev_tac `abi_decode_complex_head_guard src hi H st` >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `cs_extends st mid` by (simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_elems_code >> strip_tac >>
  `cs_extends mid en` by
    (metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def, pairTheory.SND]) >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    (fs[] >> metis_tac[cj 2 abi_decoder_vars_mono_mutual,
      abi_decoder_vars_mono_def, pairTheory.SND]) >>
  `fn_has_code mid en func` by metis_tac[fn_has_code_split] >>
  `H = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys))` by
    (drule_all abi_decoder_member_infos_layout >> simp[Abbr `H`]) >>
  `mid.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  `H < dimword (:256)` by fs[] >>
  drule_all abi_malformed_aggregate_guard_fragment >>
  disch_then (irule o MATCH_MP frag_exec_then) >> simp[] >> rpt strip_tac >>
  `abi_malformed_scratch_sites mid en func SUBSET
     abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es mid
     (abi_malformed_scratch_sites mid en func) dstid live
     base_op hi src dst B L xs p d outsz t` by
    (irule abi_malformed_aggregate_reentry >> conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
         fs[abi_malformed_entry_def]) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `abi_malformed_members_contract ce env sf tys tvs`
    (mp_tac o REWRITE_RULE [abi_malformed_members_contract_def]) >>
  disch_then drule >> simp[] >>
  disch_then assume_tac >> irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `ceiling` >> simp[] >> rpt strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid t s` by
    (irule abi_malformed_resource_weaken >> goal_assum (drule_at Any) >> simp[]) >>
  irule abi_malformed_resource_trans >> goal_assum (drule_at Any) >> simp[]
QED
