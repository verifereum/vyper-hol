Theory calldataExactTupleAssembly
Ancestors
  calldataExactMembers calldataExactLinkedMembers calldataRecursiveProducers
  calldataSourceCorrespondence calldataSourceDecisions calldataSourceSize abiDecoderCoherence
  abiDecoderAppend abiDecoderMemberInfos calldataAggregateTyped
  abiCallerAllocation exprLowering valueEncodingDefs vyperCalldata
  arithmetic list rich_list words compileEnv abiEncoder

Theorem calldata_exact_tuple_case:
  let R = \ty tv.
    !dst src st final fn initial p d ctx site oid base_addr cap.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) st = ((),final) /\
    fn_has_code st final fn /\
    eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\
    alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
    (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
    base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
    d+type_memory_size tv < dimword (:256) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
    unit_alloca_budget ctx < dimword (:256) /\
    (final.cs_current_insts = [] ==>
      !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
    (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
      ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
        mem_safe_run fuel ctx fn initial) \/
    ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
      ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
      v.vs_inst_idx = LENGTH final.cs_current_insts /\ value_has_type tv x /\
      val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn initial = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
      v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op v = eval_operand op initial) /\
      abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
      (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k))
  in
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\ R ty tv) tys tvs /\
  abi_decoder_header ce env (TupleT tys) (TupleTV tvs) ==>
  R (TupleT tys) (TupleTV tvs)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    (qpat_assum `LIST_REL _ tys tvs` mp_tac >>
     ho_match_mp_tac listTheory.LIST_REL_mono >>
     rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  `abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs)` by
    (irule (cj 4 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  qpat_x_assum `LIST_REL (\ty tv. _ /\ _) tys tvs` mp_tac >>
  qmatch_goalsub_abbrev_tac `LIST_REL ih tys tvs` >> disch_tac >>
  BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_tuple_member_metadata >> strip_tac >>
  qpat_x_assum `TupleTV _ = TupleTV _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `tvs = _` SUBST_ALL_TAC >>
  drule calldata_member_indexed_metadata >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  simp_tac (srw_ss()) [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >> strip_tac >>
  `exact_aggregate_pack (TupleTV tvs') tvs'
    (\i. cd_member_ptr F initial.vs_call_ctx.cc_calldata (EL i tvs') (w2n p)
      (SUM (MAP tv_abi_size (TAKE i tvs'))))
    initial.vs_call_ctx.cc_calldata (w2n p) (\vs. ArrayV (TupleV vs))` by
    simp[exact_aggregate_pack_tuple] >>
  drule_at (Pat `exact_aggregate_pack _ _ _ _ _ _`)
    calldata_exact_aggregate_owned_run_linked_tail >>
  disch_then (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src initial = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand dst initial = SOME _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  (impl_tac >- suspend "premises") >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `tuple_end` (qx_choose_then `tuple_values`
      (qx_choose_then `tuple_scratch` assume_tac))))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`tuple_end`, `ArrayV (TupleV tuple_values)`, `tuple_scratch`] >>
  pop_assum (fn th => POP_ASSUM_LIST (K all_tac) >>
    map_every assume_tac (CONJUNCTS (BETA_RULE th))) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]
QED
Resume calldata_exact_tuple_case[premises]:
  asm_rewrite_tac[] >>
  conj_tac >- suspend "sizes" >>
  conj_tac >- suspend "pointers" >>
  conj_tac >- suspend "extends" >>
  conj_tac >- suspend "element_extends" >>
  suspend "child"
QED
Resume calldata_exact_tuple_case[sizes]:
  rpt strip_tac >> `i < LENGTH tys` by decide_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` drule >>
  strip_tac >> asm_rewrite_tac[] >> simp_tac std_ss []
QED
Resume calldata_exact_tuple_case[pointers]:
  `MAP (abi_member_head_size o vyper_to_abi_type env) tys =
    MAP tv_abi_size tvs'` by
    (simp[MAP_EQ_EVERY2] >>
     qpat_assum `LIST_REL (abi_decoder_coherent ce env sf) tys tvs'` mp_tac >>
     ho_match_mp_tac LIST_REL_mono >> rpt strip_tac >>
     drule calldata_coherent_embedded_size >>
     drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` drule >> strip_tac >>
  `ei = type_to_abi_dec_info sf ce (EL i tys)` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >> conj_tac
  >- (drule calldata_coherent_offset >> simp[]) >>
  qpat_x_assum `MAP _ tys = MAP _ tvs'` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  BETA_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  metis_tac[MAP_TAKE]
QED
Resume calldata_exact_tuple_case[extends]:
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[abiDecoderMemberConsTheory.abi_decoder_members_extends]
QED
Resume calldata_exact_tuple_case[element_extends]:
  POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
  qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,
    `[(ei,0,0)]`,`ao`,`vo`,`a`,`b`] mp_tac
    (Q.GENL [`dst`,`src`,`opc`,`base_op`,`hi`,`elems`,`ao`,`vo`,`st`,`final`]
      abiDecoderMemberConsTheory.abi_decoder_members_extends) >>
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED
Resume calldata_exact_tuple_case[child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ih (EL i tys) (EL i tvs')` by
    (qpat_assum `LIST_REL ih _ _` mp_tac >>
     qpat_assum `i < LENGTH tys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[LIST_REL_EL_EQN]) >>
  qpat_x_assum `Abbrev (ih = _)`
    (fn th => qpat_x_assum `ih _ _`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [PURE_REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
  drule calldata_member_address_static_live >> strip_tac >>
  `ei = type_to_abi_dec_info sf ce (EL i tys)` by
    (qpat_x_assum `!i. i < LENGTH tys ==> _` drule >>
     strip_tac >> qpat_x_assum `EL i _ = (ei,az,mz)` mp_tac >>
     asm_rewrite_tac[] >> simp_tac std_ss []) >>
  `b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (drule calldata_member_tail_empty_exit_phi >>
     disch_then (qspec_then `fn` mp_tac) >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`w`,`ctx`,`site`] mp_tac) >>
  (impl_tac >- suspend "child_pre") >>
  suspend "child_post"
QED
Resume calldata_exact_tuple_case[child_pre]:
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Resume calldata_exact_tuple_case[child_post]:
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `child_end` (qx_choose_then `child_value`
      (qx_choose_then `child_scratch` assume_tac))))
  >- (disj1_tac >> conj_tac
      >- (qpat_x_assum `exact_aggregate_pack _ _ _ _ _ _` mp_tac >>
          qpat_x_assum `cd_decode F u.vs_call_ctx.cc_calldata _ _ = NONE` mp_tac >>
          qpat_x_assum `u.vs_call_ctx.cc_calldata = _` mp_tac >>
          qpat_x_assum `w2n w = _` mp_tac >>
          qpat_x_assum `i < LENGTH tys` mp_tac >>
          qpat_x_assum `LENGTH tvs' = LENGTH tys` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[exact_aggregate_pack_def] >>
          rpt strip_tac >> first_x_assum irule >> qexists `i` >> simp[]) >>
      metis_tac[]) >>
  disj2_tac >> qexistsl [`child_end`,`child_value`,`child_scratch`] >>
  qpat_x_assum `u.vs_call_ctx.cc_calldata = _` mp_tac >>
  qpat_x_assum `w2n w = _` mp_tac >>
  pop_assum (fn th => POP_ASSUM_LIST (K all_tac) >>
    map_every assume_tac (CONJUNCTS th)) >>
  ntac 2 strip_tac >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `cd_decode F u.vs_call_ctx.cc_calldata _ _ = SOME _` mp_tac >>
     BETA_TAC >> asm_rewrite_tac[])]
QED
Finalise calldata_exact_tuple_case
