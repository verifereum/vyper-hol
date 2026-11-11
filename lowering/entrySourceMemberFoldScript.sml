(* Source-member iteration with a jointly witnessed observation/history frame. *)
Theory entrySourceMemberFold
Ancestors
  entrySourceMemberCursor entryDecoderRelationIteration entryDecoderStateFrame
  calldataSourceMemberFold calldataMemberResourceFrame calldataSafeIteration
  abiDecoderMemberCons abiDecoderMemberCode abiDecoderMembers abiDecoderMemberInfos
  abiDecoderCode abiDecoderCounters abiDecoderAppend abiDecoderContract
  abiEncoder compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  words list rich_list pair arithmetic relation

Theorem entry_source_members_owned_success:
  let xs = abi_decoder_member_infos sf ce tys in
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs 0 0 first = ((),final) /\
  fn_has_code first final fn /\
  (first.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  abi_decoder_operand_live first.cs_next_var src /\
  abi_decoder_operand_live first.cs_next_var dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  fresh_vars_wrt limit_st initial /\ alloca_inv initial /\
  alloca_frontier_inv ctx fn site initial /\
  calldata_member_own fn first.cs_next_id final.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < first.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d + SUM (MAP type_memory_size tvs) <= base_addr+cap /\
  SUM (MAP type_memory_size tvs) <= outsz /\
  d + SUM (MAP type_memory_size tvs) < dimword(:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = first.cs_current_bb /\
  initial.vs_inst_idx = LENGTH first.cs_current_insts /\
  (!i. i < LENGTH tys ==> entry_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) /\ fn_inst_ids_distinct fn /\ alloca_history fn initial ==>
  ?t scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id final.cs_next_id
      first.cs_next_var d outsz initial t scratch /\
    EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory)
      (GENLIST I (LENGTH tvs)) /\
    calldata_member_transfers ctx fn initial t /\
    entry_decoder_obs initial t /\ alloca_history fn t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `xs = abi_decoder_member_infos sf ce tys` >>
  drule abi_decoder_members_extends >> strip_tac >>
  `ci_mono first final` by suspend "mono" >>
  qabbrev_tac `Inv = \k s. ?a.
    calldata_source_member_cursor ce env sf ctx fn site limit_st
      xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
      0 0 first final initial (DROP k xs)
      (SUM (MAP (\(ei,az,mz). az) (TAKE k xs)))
      (SUM (MAP (\(ei,az,mz). mz) (TAKE k xs))) a s /\
    ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\
    entry_decoder_obs initial s /\ alloca_history fn s` >>
  `Inv 0 initial` by suspend "initial" >>
  `?t. Inv (LENGTH xs) t /\ calldata_member_transfers ctx fn initial t`
    suffices_by (strip_tac >> suspend "terminal") >>
  irule entry_relation_finite_iteration >>
  conj_tac >- suspend "successor" >>
  conj_tac >- suspend "reflexive" >>
  conj_tac >- suspend "transitive" >>
  qexists_tac `0` >> simp[]
QED

Resume entry_source_members_owned_success[mono]:
  `first.cs_next_id <= final.cs_next_id` by
    (mp_tac (cj 2 abi_decoder_code_mutual) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`xs`,`0`,`0`] mp_tac) >>
     simp[] >> disch_then (qspec_then `first` mp_tac) >>
     simp[abi_decoder_code_def]) >>
  simp[ci_mono_def]
QED

Resume entry_source_members_owned_success[initial]:
  simp_tac bool_ss [Abbr `Inv`] >> qexists_tac `first` >>
  asm_simp_tac (srw_ss()) [] >>
  rewrite_tac[calldata_source_member_cursor_def] >>
  qexistsl_tac [`0`,`[]`] >>
  simp[cs_extends_refl, ci_mono_refl] >>
  irule calldata_member_resource_identity >> simp[]
QED

Resume entry_source_members_owned_success[reflexive]:
  simp[reflexive_def, calldata_member_transfers_def] >> metis_tac[]
QED

Resume entry_source_members_owned_success[transitive]:
  simp_tac bool_ss [transitive_def, calldata_member_transfers_def] >>
  metis_tac[calldata_safe_transfer_trans]
QED

Resume entry_source_members_owned_success[terminal]:
  qpat_x_assum `Inv _ _` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >>
  qhdtm_x_assum `calldata_source_member_cursor`
    (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
  `n = LENGTH xs` by
    (qpat_x_assum `DROP (LENGTH xs) xs = _` mp_tac >>
     simp[DROP_EQ_NIL] >> decide_tac) >>
  `LENGTH tvs = LENGTH xs` by
    (fs[Abbr `xs`, abi_decoder_member_infos_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `a = final` by
    (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ (DROP (LENGTH xs) xs) _ _ _ = _`
       mp_tac >> rpt (pop_assum kall_tac) >>
     simp[compile_abi_decode_to_buf_def, comp_return_def]) >>
  qexistsl_tac [`t`,`scratch`] >> simp[] >>
  qpat_x_assum `EVERY _ (GENLIST I n)` mp_tac >>
  simp_tac bool_ss [ADD_CLAUSES] >> asm_rewrite_tac[]
QED

Resume entry_source_members_owned_success[successor]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Inv _ _` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >>
  `DROP k xs = EL k xs::DROP (SUC k) xs` by
    (qpat_assum `k < LENGTH xs` mp_tac >> rpt (pop_assum kall_tac) >>
     metis_tac[DROP_EL_CONS, ADD1]) >>
  Cases_on `EL k xs` >> Cases_on `r` >>
  rename1 `EL k xs = (ei,az,mz)` >>
  `cs_extends first a /\ cs_extends a final /\
   compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DROP k xs)
     (SUM (MAP (\(ei,az,mz). az) (TAKE k xs)))
     (SUM (MAP (\(ei,az,mz). mz) (TAKE k xs))) a = ((),final)` by
    (qhdtm_assum `calldata_source_member_cursor`
       (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ (DROP k xs) _ _ _ = _` mp_tac >>
  qpat_assum `DROP k xs = _` (fn th => pure_once_rewrite_tac[th]) >>
  suspend "split"
QED
Resume entry_source_members_owned_success[split]:
  simp_tac bool_ss [Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
  pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
  pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei ready = (ignored,next)` >>
  Cases_on `ignored` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
       (SUM (MAP (\(ei,az,mz). az) (TAKE k xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w (SUM (MAP (\(ei,az,mz). mz) (TAKE k xs))))];
       compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),next)` by
    asm_simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  suspend "step"
QED

Resume entry_source_members_owned_success[step]:
  `fn_has_code a final fn` by metis_tac[fn_has_code_split] >>
  `a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by suspend "phi" >>
  `xs = abi_decoder_member_infos sf ce tys` by simp[Abbr `xs`] >>
  qpat_assum `DROP k xs = _` (fn th =>
    qhdtm_x_assum `calldata_source_member_cursor`
      (assume_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  drule entry_source_member_cursor_step >>
  disch_then (qspec_then `next` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_PROVE
    [first_assum MATCH_ACCEPT_TAC, disj1_tac >> first_assum MATCH_ACCEPT_TAC,
     disj2_tac >> first_assum MATCH_ACCEPT_TAC])) >> strip_tac >>
  suspend "assemble"
QED
Resume entry_source_members_owned_success[phi]:
  Cases_on `first.cs_blocks = final.cs_blocks`
  >- (disj1_tac >>
      qpat_x_assum `cs_extends first a` mp_tac >>
      qpat_x_assum `cs_extends a final` mp_tac >>
      qpat_x_assum `first.cs_blocks = final.cs_blocks` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[cs_extends_def] >> rpt strip_tac >>
      qpat_assum `final.cs_blocks = _ ++ _`
        (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >>
      qpat_assum `a.cs_blocks = _ ++ _`
        (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >>
      simp_tac list_ss [] >> rpt strip_tac >>
      `LENGTH new' = 0` by decide_tac >>
      `new' = []` by metis_tac[LENGTH_NIL] >>
      qpat_x_assum `a.cs_blocks = _` mp_tac >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Resume entry_source_members_owned_success[assemble]:
  markerLib.RESUME_TAC >> (
  `TAKE (SUC k) xs = TAKE k xs ++ [(ei,az,mz)]` by
    (qpat_assum `k < LENGTH xs` mp_tac >>
     qpat_assum `EL k xs = _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[TAKE_SUC]) >>
  `entry_decoder_obs initial t` by metis_tac[entry_decoder_obs_trans] >>
  qexists_tac `t` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `next` >>
  qpat_assum `TAKE (SUC k) xs = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [MAP_APPEND, SUM_APPEND] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)

QED
Finalise entry_source_members_owned_success
