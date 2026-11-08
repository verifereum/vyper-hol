(* Operational fold over coherent heterogeneous members. *)
Theory abiMalformedMembersFold
Ancestors
  abiMalformedMemberSetup abiMalformedMembers abiMalformedConstructorInduction
  abiMalformedMemberReflection abiMalformedRecursiveInterface abiDecoderMemberCons
  abiDecoderMemberSetup abiDecoderCoherence abiDecoderMemberInfos abiDecoderContract
  abiEncoder abiDecoderCounters abiDecoderCode exprLoweringProps localPtrsProps
  abiMalformedConstructorContract abiDecoderDynamic abiDecoderComplexHead abiDecoderMemberCode
  abiDecoderOffset abiDecoderAppend fragExec compileEnv emitHelper emitHelperProps
  abiDecodeRanges abiDecoderWordTyped contractABI vyperABI valueEncoding words list rich_list arithmetic

Theorem abi_malformed_entry_restrict_sites[local]:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n s /\ child_sites SUBSET sites ==>
  abi_malformed_entry ctx func cenv cx es st child_sites dstid live
    base_op hi src dst B L xs p d n s
Proof
  simp_tac bool_ss [abi_malformed_entry_def] >>
  strip_tac >> fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_malformed_constructor_continue[local]:
  abi_malformed_constructor env ty di ctx func cenv cx es st mid
    base_op hi src dst outsz /\ fn_has_code st mid func /\
  mid.cs_next_var <= ceiling.cs_next_var /\
  (case di of DecPrimWord clamp => p+32 <= L | _ => T) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st mid func) dstid live
    base_op hi src dst B L xs p d outsz incoming /\
  fresh_vars_wrt ceiling incoming /\ cs_extends st mid /\ cs_extends mid en /\
  (!u. abi_malformed_reflected_post env ty
       (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
        else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
       ctx func cenv cx es st.cs_next_var
       (abi_malformed_scratch_sites st mid func) dstid incoming u /\
       fresh_vars_wrt ceiling u ==>
       frag_exec ctx mid en (\s. s = u) Q (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_exec ctx st en (\s. s = incoming) Q (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  irule frag_exec_seq_pointwise >> simp[] >>
  qexistsl_tac [`\u. abi_malformed_reflected_post env ty
       (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
        else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
       ctx func cenv cx es st.cs_next_var
       (abi_malformed_scratch_sites st mid func) dstid incoming u /\
       fresh_vars_wrt ceiling u`, `mid`] >> simp[] >>
  irule frag_exec_pre_exit >>
  qexistsl_tac [`\v. v = incoming /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st mid func) dstid live
      base_op hi src dst B L xs p d outsz v /\ fresh_vars_wrt ceiling v`,
    `\r. ?v. r = Abort Revert_abort v`] >> simp[] >>
  fs[abi_malformed_constructor_def] >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_members_finish[local]:
  abi_malformed_members_contract ce env sf tys tvs /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys) ao vo st = ((),en) /\
  EVERY (assignable_type env) tys /\
  EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys /\
  type_memory_size_list tvs < dimword (:256) /\
  vo + type_memory_size_list tvs <= outsz /\
  fn_inst_ids_distinct func /\ fn_has_code st en func /\
  en.cs_next_var <= ceiling.cs_next_var /\
  p+ao+SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d outsz incoming /\ fresh_vars_wrt ceiling incoming /\
  (!u. vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
          (DROP p xs) (DROP (p+ao) xs) /\
     abi_vyper_admissible_list env tys
       (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP (p+ao) xs)) /\
     abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
       (abi_malformed_scratch_sites st en func) dstid incoming u /\
     fresh_vars_wrt ceiling u ==> Q u) ==>
  frag_exec ctx st en (\s. s = incoming) Q (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = incoming /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      base_op hi src dst B L xs p d outsz s /\ fresh_vars_wrt ceiling s`,
    `\u. vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
          (DROP p xs) (DROP (p+ao) xs) /\
     abi_vyper_admissible_list env tys
       (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP (p+ao) xs)) /\
     abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
       (abi_malformed_scratch_sites st en func) dstid incoming u /\
     fresh_vars_wrt ceiling u`, `\r. ?v. r = Abort Revert_abort v`] >>
  simp[] >> fs[abi_malformed_members_contract_def] >> first_x_assum irule >> simp[] >>
  qexists_tac `vo` >> simp[]
QED

Theorem abi_malformed_members_cons:
  abi_decoder_coherent ce env sf ty tv /\
  abi_malformed_type_contract ce env sf ty tv /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  abi_malformed_members_contract ce env sf tys tvs ==>
  abi_malformed_members_contract ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >>
  simp_tac bool_ss [abi_malformed_members_contract_def, EVERY_DEF,
    type_memory_size_def, MAP, SUM] >> rpt gen_tac >> strip_tac >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code middle end_st func` by
    (metis_tac[fn_has_code_split]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `abi_malformed_constructor env ty (type_to_abi_dec_info sf ce ty)
     ctx func cenv cx es middle end_st base_op hi (FST ops) (SND ops)
     (type_memory_bytes ce ty)` by
    (fs[abi_malformed_type_contract_def] >> first_x_assum irule >>
     simp[] >> metis_tac[LESS_EQ_LESS_TRANS, LESS_EQ_ADD]) >>
  rpt gen_tac >> strip_tac >>
  `cs_extends middle en` by simp[] >>
  `vo + type_memory_bytes ce ty <= outsz` by
    (fs[abi_decoder_header_def] >> decide_tac) >>
  `p + ao + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
              then 32 else 0) <= L` by
    (drule abi_decoder_coherent_dynamic >> strip_tac >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[abi_member_head_size_def, abi_decoder_needs_offset_iff] >>
     Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []` >> gvs[] >> decide_tac) >>
  irule frag_exec_pointwise >> gen_tac >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = incoming` SUBST_ALL_TAC >>
  `middle.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  drule_all abi_malformed_member_setup_fragment >>
  disch_then (mp_tac o Q.INST
    [`sites` |-> `abi_malformed_scratch_sites st en func`] o SPEC_ALL) >>
  simp[SF CONJ_ss] >>
  disch_then (irule o MATCH_MP frag_exec_then) >>
  simp[] >> rpt strip_tac >>
  `abi_malformed_scratch_sites middle end_st func SUBSET
     abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `abi_malformed_entry ctx func cenv cx es middle
     (abi_malformed_scratch_sites middle end_st func) dstid live
     base_op hi (FST ops) (SND ops) B L xs
     (p + if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
          then abi_head_word (DROP (ao+p) xs) else ao)
     (d+vo) (type_memory_bytes ce ty) t` by
    (irule abi_malformed_entry_restrict_sites >> goal_assum (drule_at Any) >> simp[]) >>
  `!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
     p + ao + 32 <= L` by
    (rpt strip_tac >> drule_all abi_decoder_primitive_cases >> strip_tac >>
     gvs[abi_decoder_header_def, abi_member_head_size_def, is_dynamic_def] >> decide_tac) >>
  `end_st.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  irule abi_malformed_constructor_continue >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`type_to_abi_dec_info sf ce ty`, `env`, `ty`] >> simp[] >>
  reverse conj_tac
  >- (Cases_on `type_to_abi_dec_info sf ce ty` >>
      fs[dec_info_needs_offset_def] >> decide_tac) >>
  rpt strip_tac >> rename1 `fresh_vars_wrt ceiling t'` >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid incoming t'` by
    (drule_all abi_malformed_reflected_child_return >>
     simp[abi_malformed_reflected_post_def]) >>
  `abi_malformed_scratch_sites end_st en func SUBSET
     abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `local_ptrs_reserved cenv end_st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_malformed_entry ctx func cenv cx es end_st
     (abi_malformed_scratch_sites end_st en func) dstid live
     base_op hi src dst B L xs p d outsz t'` by
    (irule abi_malformed_aggregate_reentry >> simp[] >>
     qexistsl_tac [`incoming`, `abi_malformed_scratch_sites st en func`, `st`] >>
     simp[] >> decide_tac) >>
  irule abi_malformed_members_finish >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ao + abi_embedded_static_size ce.ce_struct_fields ty`,
    `ce`, `env`, `sf`, `tvs`, `tys`, `vo + type_memory_bytes ce ty`] >>
  simp[] >>
  `abi_embedded_static_size ce.ce_struct_fields ty =
     abi_member_head_size (vyper_to_abi_type env ty)` by
    fs[abi_decoder_header_def] >>
  fs[abi_decoder_header_def] >>
  gen_tac >> strip_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     qpat_x_assum `mem_bytes_at B L incoming.vs_memory = xs`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[mem_bytes_at_def, LENGTH_TAKE_EQ, LENGTH_DROP]) >>
  `p + ao + abi_member_head_size (vyper_to_abi_type env ty) <= L` by decide_tac >>
  `((is_dynamic (vyper_to_abi_type env ty) ==>
       is_num_value (dec_number (Uint 256) (TAKE 32 (DROP (p+ao) xs)))) /\
     vyper_decode_valid_enc (vyper_to_abi_type env ty)
       (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) /\
     abi_vyper_admissible env ty
       (dec (vyper_to_abi_type env ty)
         (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs))))` by
    (irule abi_malformed_member_reflection >>
     conj_tac >- (qexists_tac `L` >> simp[]) >>
     qexistsl_tac [`ce`,
       `p + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
             then abi_head_word (DROP (p+ao) xs) else ao)`, `sf`, `tv`] >>
     qpat_x_assum `abi_malformed_reflected_post env ty _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_malformed_reflected_post_def, ADD_COMM] >>
     strip_tac >> asm_rewrite_tac []) >>
  `vyper_decode_valid_enc_tuple (vyper_to_abi_type env ty::MAP (vyper_to_abi_type env) tys)
      (DROP p xs) (DROP (p+ao) xs) /\
    abi_vyper_admissible_list env (ty::tys)
      (abi_decode_members (vyper_to_abi_type env ty::MAP (vyper_to_abi_type env) tys)
        (DROP p xs) (DROP (p+ao) xs))` by
    (irule (PURE_REWRITE_RULE [MAP] abi_malformed_members_reflect_cons) >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
  full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >>
  irule abi_malformed_resource_trans >>
  qexists_tac `t'` >> simp[] >>
  irule abi_malformed_resource_weaken >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_members_fold:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (abi_malformed_type_contract ce env sf) tys tvs ==>
  abi_malformed_members_contract ce env sf tys tvs
Proof
  qid_spec_tac `tvs` >> Induct_on `tys`
  >- (Cases_on `tvs` >> simp[abi_malformed_members_nil]) >>
  Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  irule abi_malformed_members_cons >> simp[]
QED
