Theory calldataExactStructAssembly
Ancestors
  calldataExactMembers calldataExactLinkedMembers calldataRecursiveProducers
  calldataSourceCorrespondence calldataSourceDecisions calldataSourceSize abiDecoderCoherence
  abiDecoderAppend abiDecoderMemberInfos calldataAggregateTyped
  abiCallerAllocation exprLowering valueEncodingDefs vyperCalldata
  arithmetic list rich_list words compileEnv abiEncoder

Theorem calldata_exact_struct_case:
  let R = \ce env sf ty tv.
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
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
  LIST_REL (\ty tv.
    abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv /\
    R ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv) (MAP SND args) tvs /\
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) ==>
  R ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs` by
    (qpat_assum `LIST_REL _ (MAP SND args) tvs` mp_tac >>
     ho_match_mp_tac listTheory.LIST_REL_mono >>
     rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `LIST_REL (\ty tv. _ /\ _) _ tvs` mp_tac >>
  qmatch_goalsub_abbrev_tac `LIST_REL ih (MAP SND args) tvs` >> disch_tac >>
  `abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))` by
    (qpat_x_assum `Abbrev (ih = _)` kall_tac >>
     irule (cj 5 abi_decoder_coherent_rules) >> asm_rewrite_tac[] >>
     qexists `fields` >> asm_rewrite_tac[]) >>
  BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
  disch_then (fn th => qpat_assum `MAP (FST o SND) fields = _`
    (fn eq => assume_tac (PURE_REWRITE_RULE [eq] th))) >>
  drule calldata_member_indexed_metadata >> strip_tac >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by
    (drule LIST_REL_LENGTH >> simp[LENGTH_MAP] >> strip_tac >> simp[MAP_ZIP]) >>
  `type_memory_size (StructTV (ZIP (MAP FST args,tvs))) = SUM (MAP type_memory_size tvs)` by
    (simp_tac std_ss [valueEncodingTheory.type_memory_size_def,
      valueEncodingProofsTheory.type_memory_size_fields_sum, GSYM MAP_MAP_o] >>
     qpat_assum `MAP SND (ZIP _) = tvs` (fn th => rewrite_tac[th])) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (fn th => qpat_assum `type_to_abi_dec_info sf ce (StructT nsid) = _`
      (fn eq => mp_tac (PURE_REWRITE_RULE [eq] th))) >>
  simp_tac (srw_ss()) [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >> strip_tac >>
  `exact_aggregate_pack (StructTV (ZIP (MAP FST args,tvs))) tvs
    (\i. cd_member_ptr F initial.vs_call_ctx.cc_calldata (EL i tvs) (w2n p)
      (SUM (MAP tv_abi_size (TAKE i tvs))))
    initial.vs_call_ctx.cc_calldata (w2n p)
    (\vs. StructV (ZIP (MAP FST args,vs)))` by
    (qspecl_then [`ZIP (MAP FST args,tvs)`, `initial.vs_call_ctx.cc_calldata`, `w2n p`] mp_tac
       (Q.GENL [`fs`,`cd`,`root_addr`] exact_aggregate_pack_struct) >>
     `LENGTH args = LENGTH tvs` by
       (drule LIST_REL_LENGTH >> simp[]) >>
     asm_rewrite_tac[] >> simp[MAP_ZIP]) >>
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
    (qx_choose_then `struct_end` (qx_choose_then `struct_values`
      (qx_choose_then `struct_scratch` assume_tac))))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`struct_end`, `StructV (ZIP (MAP FST args,struct_values))`, `struct_scratch`] >>
  pop_assum (fn th => POP_ASSUM_LIST (K all_tac) >>
    map_every assume_tac (CONJUNCTS (BETA_RULE th))) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]
QED
Resume calldata_exact_struct_case[premises]:
  asm_rewrite_tac[] >>
  conj_tac >- suspend "sizes" >>
  conj_tac >- suspend "pointers" >>
  conj_tac >- suspend "extends" >>
  conj_tac >- suspend "element_extends" >>
  suspend "child"
QED
Resume calldata_exact_struct_case[sizes]:
  rpt strip_tac >>
  `i < LENGTH (MAP SND args)` by
    (drule LIST_REL_LENGTH >> strip_tac >> decide_tac) >>
  qpat_x_assum `!i. i < LENGTH (MAP SND args) ==> _` drule >>
  strip_tac >> asm_rewrite_tac[] >> simp_tac std_ss []
QED
Resume calldata_exact_struct_case[pointers]:
  `MAP (abi_member_head_size o vyper_to_abi_type (env \\ nsid)) (MAP SND args) =
    MAP tv_abi_size tvs` by
    (`LENGTH args = LENGTH tvs` by (drule LIST_REL_LENGTH >> simp[]) >>
     simp[MAP_EQ_EVERY2] >>
     qpat_assum `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)) _ tvs` mp_tac >>
     ho_match_mp_tac LIST_REL_mono >> rpt strip_tac >>
     drule calldata_coherent_embedded_size >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH (MAP SND args)` by
    (drule LIST_REL_LENGTH >> simp[] >> strip_tac >> decide_tac) >>
  qpat_x_assum `!i. i < LENGTH (MAP SND args) ==> _` drule >> strip_tac >>
  `ei = type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce (EL i (MAP SND args))` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >> conj_tac
  >- (drule calldata_coherent_offset >> simp[]) >>
  qpat_x_assum `MAP _ (MAP SND args) = MAP _ tvs` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  BETA_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> metis_tac[MAP_TAKE]
QED
Resume calldata_exact_struct_case[extends]:
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[abiDecoderMemberConsTheory.abi_decoder_members_extends]
QED
Resume calldata_exact_struct_case[element_extends]:
  POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
  qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,
    `[(ei,0,0)]`,`ao`,`vo`,`a`,`b`] mp_tac
    (Q.GENL [`dst`,`src`,`opc`,`base_op`,`hi`,`elems`,`ao`,`vo`,`st`,`final`]
      abiDecoderMemberConsTheory.abi_decoder_members_extends) >>
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED
Resume calldata_exact_struct_case[child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH (MAP SND args)` by
    (drule LIST_REL_LENGTH >> metis_tac[]) >>
  `ih (EL i (MAP SND args)) (EL i tvs)` by
    (qpat_assum `LIST_REL ih _ _` mp_tac >>
     qpat_assum `i < LENGTH (MAP SND args)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN]) >>
  qpat_x_assum `Abbrev (ih = _)`
    (fn th => qpat_x_assum `ih _ _`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [PURE_REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
  drule calldata_member_address_static_live >> strip_tac >>
  `ei = type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce (EL i (MAP SND args))` by
    (qpat_x_assum `!i. i < LENGTH (MAP SND args) ==> _` drule >>
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
Resume calldata_exact_struct_case[child_pre]:
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Resume calldata_exact_struct_case[child_post]:
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `child_end` (qx_choose_then `child_value`
      (qx_choose_then `child_scratch` assume_tac))))
  >- (disj1_tac >> conj_tac
      >- (qpat_x_assum `exact_aggregate_pack _ _ _ _ _ _` mp_tac >>
          qpat_x_assum `cd_decode F u.vs_call_ctx.cc_calldata _ _ = NONE` mp_tac >>
          qpat_x_assum `u.vs_call_ctx.cc_calldata = _` mp_tac >>
          qpat_x_assum `w2n w = _` mp_tac >>
          qpat_x_assum `i < LENGTH tvs` mp_tac >>
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
Finalise calldata_exact_struct_case
