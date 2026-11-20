(* The installed decoder either reverts or can continue only after source decoding succeeds. *)
Theory calldataNoneDecoder
Ancestors
  calldataNoneDecodeLeaves calldataNoneFiniteMembers calldataNoneArrayFold
  calldataRecursiveProducers ptrSafetyTransport assignTuplePtrCopyLen
  abiDecoderSourceFacts calldataDecodePtr decoderBlockGrowth valueEncodingProofs
  fragGasOriginPtr fragExec abiDecoderFrame calldataSourceSize
  abiDecoderMemberInfos abiDecoderComplexGuard abiDecoderBulk abiDecoderArrayHeader
  abiDecoderDynarrayPrefix abiDecoderContract abiEncoderExitPhi abiDecoderBytesEdges
  calldataRegistration exprSimAbiDecodePhiBoundary compileEnv emitHelper
  vyperCalldata ptrDiscipline abiDecoderCoherence words venomState
  rich_list list option arithmetic pred_set decoderOriginAllocationFrame

val decode_history = ``\st last fn s.
  !id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]``;
val decode_exit = ``\st last fn. st.cs_blocks = last.cs_blocks \/
  !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0``;
val decode_input = ``\di sz st last limit ctx fn site src child s p d oid base cap G tn lo.
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w) di st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\ unit_alloca_budget ctx < dimword (:256) /\
  (^decode_exit) st last fn /\
  eval_operand src s = SOME p /\ eval_operand (Var child) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ (^decode_history) st last fn s /\
  FLOOKUP s.vs_allocas oid = SOME (base,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base <= d /\ d+sz <= base+cap /\ d+sz < dimword (:256) /\
  ptr_covers G tn child s sz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts``;
val decode_outcome = ``\accepted sz st last limit ctx fn site child s d G tn lo PG.
  (?z H u. z.vs_returndata = [] /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v sc H u. accepted /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    v.vs_call_ctx = s.vs_call_ctx /\ v.vs_data_section = s.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp v /\
      v.vs_alloca_next + pending_alloca_size fn v <= w2n v.vs_initial_fmp) /\
    (^decode_history) st last fn v /\
    s.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==> FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op v = eval_operand op s) /\
    abi_decode_footprint_frame ((d,sz)::sc) s v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v sz /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      op_taint u (Var name) = op_taint tn (Var name)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,H,u))``;
val coherent_paths = ``\ce (env:(num option # string) |-> type_args)
  (sf:string |-> (string # type # num) list) ty tv.
  !st last limit ctx fn site src child s p d oid base cap G tn lo PG.
  (^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
    st last limit ctx fn site src child s p d oid base cap G tn lo ==>
  (^decode_outcome) (IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p)))
    (type_memory_size tv) st last limit ctx fn site child s d G tn lo PG``;

Theorem decode_path_endpoint_floor[local]:
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  disch_then (CONJUNCTS_THEN2 (mp_tac o SPEC_ALL) strip_assume_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP member_path_allocas_from o CONJUNCT2) >>
  disch_then (qspecl_then [`lo`,`t`] mp_tac) >> simp[]
QED

Theorem decode_fixed_source[local]:
  !n i. cd_decode_list F cd (REPLICATE n tv) p (i * tv_abi_size tv) =
        cd_decode_elems F cd tv p i n
Proof
  Induct_on `n` >> simp[REPLICATE, Once cd_decode_def] >> gen_tac >>
  once_rewrite_tac[cd_decode_def] >>
  Cases_on `cd_decode F cd tv (cd_member_ptr F cd tv p (i * tv_abi_size tv))` >>
  simp[] >>
  first_x_assum (qspec_then `i + 1` mp_tac) >>
  simp[RIGHT_ADD_DISTRIB, ADD_COMM]
QED

(* At a finite aggregate, the unbounded head guard emits no code. *)
Theorem decode_finite_paths[local]:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (^coherent_paths) ce env sf ty tv) tys tvs /\
  (^decode_input) (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    (SUM (MAP type_memory_size tvs)) st last limit ctx fn site src child s p d oid owner_base cap G tn lo ==>
  (^decode_outcome) (IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0))
    (SUM (MAP type_memory_size tvs)) st last limit ctx fn site child s d G tn lo PG
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE std_ss [Once abiEncoderTheory.compile_abi_decode_to_buf_def, LET_THM]) >>
  drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)
    (BETA_RULE calldataNoneFiniteMembersTheory.none_finite_members_paths) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (mp_tac o Q.INST [`env` |-> `env`, `PG` |-> `PG`,
    `tvs'` |-> `tvs`, `p` |-> `p`] o SPEC_ALL) >>
  rewrite_tac[ADD_CLAUSES, LESS_EQ_REFL] >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >> ho_match_mp_tac LIST_REL_mono >>
      rpt gen_tac >> strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      map_every qx_gen_tac [`mid`,`en`,`q`,`sop`,`r`,`pw`,`e`,`rid`,`rb`,`child_cap`,`A`,`ta`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `(^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
        mid en limit ctx fn site sop q r pw e rid rb child_cap A ta lo` by
        (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum (fn input =>
        qpat_x_assum `!st last limit ctx fn site src child s p d oid base cap G tn lo PG. _`
          (mp_tac o C MATCH_MP (BETA_RULE input))) >>
      disch_then (qspec_then `PG` (DISJ_CASES_THEN2
        (qx_choose_then `z` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))
        (qx_choose_then `v` (qx_choose_then `sc` (qx_choose_then `H`
          (qx_choose_then `u` strip_assume_tac))))))
      >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
      `allocas_from lo v /\ lo <= v.vs_alloca_next` by
        (irule decode_path_endpoint_floor >>
         qexistsl [`A`,`H`,`PG`,`ctx`,`fn`,`r`,`ta`,`u`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> qexistsl [`v`,`H`,`u`,`sc`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_then (fn th =>
        POP_ASSUM_LIST (K ALL_TAC) >> mp_tac (CONJUNCT1 th) >> mp_tac (cj 2 th)) >>
      simp[arithmeticTheory.NOT_LESS]) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl [`t`,`sc`,`H`,`u`] >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section` by
    (qpat_assum `abi_decode_footprint_frame _ _ _`
       (mp_tac o REWRITE_RULE [abi_decode_footprint_frame_def]) >> simp[NoAsms]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule ptr_covers_lookup_frame >> qexistsl [`G`,`s`,`tn`] >>
  `not_fresh_at st child` by
    (rewrite_tac[GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!name. not_fresh_at st name ==> _` (drule_all_then strip_assume_tac) >>
  `lookup_var child t = lookup_var child s` by
    (qpat_assum `!op. abi_decoder_operand_live _ op ==> _`
       (qspec_then `Var child` mp_tac) >>
     disch_then (drule_then mp_tac) >> simp[NoAsms, eval_operand_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem decode_leaf_exit_nonempty[local]:
  ((?cl. di = DecPrimWord cl) \/ (?n. di = DecBytestring n) \/
   (?ei az mz n. di = DecDynArray ei az mz F n /\ ~dec_info_needs_clamp ei)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di st = ((),last) ==>
  last.cs_current_insts <> []
Proof
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  `abi_encoder_exit_nonempty
     (compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di)` by
    (FIRST [qpat_assum `di = DecPrimWord _` SUBST1_TAC >>
            simp[Once abiEncoderTheory.compile_abi_decode_to_buf_def,
                 abiEncoderTheory.compile_abi_decode_static_def],
            qpat_assum `di = DecBytestring _` SUBST1_TAC >>
            simp[abiDecoderBytesEdgesTheory.abi_decode_bytes_sentinel_base_branches],
            qpat_assum `di = DecDynArray _ _ _ _ _` SUBST1_TAC >>
            simp[abi_decode_bulk_phases, abi_decode_bulk_body_def, abi_decode_bulk_payload_def]] >>
     rpt (ho_match_mp_tac abi_encoder_exit_nonempty_bind >> gen_tac ORELSE
          irule abi_encoder_exit_nonempty_ignore) >>
     simp[abi_encoder_exit_nonempty_emit]) >>
  pop_assum (mp_tac o REWRITE_RULE [abi_encoder_exit_nonempty_def]) >>
  metis_tac[]
QED

Theorem decode_leaf_paths[local]:
  abi_decoder_coherent ce env sf ty tv /\
  ((?cl. type_to_abi_dec_info sf ce ty = DecPrimWord cl) \/
   is_bytestring_type ty \/
   (?ety maxn ei abi_sz mem_sz. ty = ArrayT ety (Dynamic maxn) /\
     type_to_abi_dec_info sf ce ty = DecDynArray ei abi_sz mem_sz F maxn /\
     ~dec_info_needs_clamp ei)) /\
  (^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
    st last limit ctx fn site src child s p d oid owner_base cap G tn lo ==>
  (^decode_outcome) (IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p)))
    (type_memory_size tv) st last limit ctx fn site child s d G tn lo PG
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `last.cs_current_insts <> []` by
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) decode_leaf_exit_nonempty >>
     disch_then irule >> qpat_assum `(?cl. _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac
     >- (disj1_tac >> qexists_tac `cl` >> first_assum ACCEPT_TAC)
     >- (disj2_tac >> disj1_tac >>
         qpat_x_assum `is_bytestring_type _` mp_tac >>
         Cases_on `ty` >> simp[is_bytestring_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         simp[is_bytestring_type_def, exprLoweringTheory.type_to_abi_dec_info_def] >>
         rename1 `BytesT b` >> Cases_on `b` >>
         simp[is_bytestring_type_def, exprLoweringTheory.type_to_abi_dec_info_def]) >>
     disj2_tac >> disj2_tac >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) none_decode_leaf_paths >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = SOME _`)) >>
  disch_then (mp_tac o Q.INST [`PG` |-> `PG`] o SPEC_ALL) >>
  impl_tac >- (rpt conj_tac >> asm_rewrite_tac[]) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v /\
    v.vs_alloca_next + pending_alloca_size fn v <= w2n v.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK v,H,u)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     strip_tac >>
     drule_at (Pat `gas_origin_ptr_path _ _ _ _`) decoder_origin_path_room >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`v`,`sc`,`H`,`u`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem none_coherent_decode_paths:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    (^coherent_paths) ce env sf ty tv
Proof
  BETA_TAC >> ho_match_mp_tac calldata_coherent_induction >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "flag" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "tuple" >>
  suspend "struct"
QED

Resume none_coherent_decode_paths[tuple]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  rewrite_tac[abi_decoder_tuple_infos, valueEncodingTheory.type_memory_size_def,
    type_memory_size_list_sum] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata (TupleTV tvs) (w2n p)) =
   IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0)` by
    (once_rewrite_tac[cd_decode_def] >>
     Cases_on `cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0` >> simp[]) >>
  qpat_x_assum `IS_SOME (cd_decode _ _ (TupleTV _) _) = _` SUBST1_TAC >>
  rename1 `FLOOKUP s.vs_allocas oid = SOME (owner_base,cap)` >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) (BETA_RULE decode_finite_paths) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexistsl [`cap`,`oid`,`owner_base`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `env` >> first_assum ACCEPT_TAC
QED

Resume none_coherent_decode_paths[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound` >- suspend "fixed" >> suspend "dynamic"
QED

Resume none_coherent_decode_paths[fixed]:
  rpt gen_tac >>
  rewrite_tac[abi_decoder_fixed_array_infos, valueEncodingTheory.type_memory_size_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata (ArrayTV tv (Fixed n)) (w2n p)) =
   IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata (REPLICATE n tv) (w2n p) 0)` by
    (once_rewrite_tac[cd_decode_def] >>
     rewrite_tac[REWRITE_RULE [MULT_CLAUSES] (Q.SPECL [`n`,`0`] decode_fixed_source)] >>
     Cases_on `cd_decode_elems F s.vs_call_ctx.cc_calldata tv (w2n p) 0 n` >> simp[]) >>
  qpat_x_assum `IS_SOME (cd_decode _ _ (ArrayTV _ _) _) = _` SUBST1_TAC >>
  rename1 `FLOOKUP s.vs_allocas oid = SOME (owner_base,cap)` >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    (BETA_RULE decode_finite_paths) >>
  disch_then (irule o BETA_RULE o
    REWRITE_RULE [rich_listTheory.map_replicate, SUM_REPLICATE, LIST_REL_REPLICATE_same] o
    Q.INST [`tvs` |-> `REPLICATE n tv`] o SPEC_ALL) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> disch_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`cap`,`oid`,`owner_base`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume none_coherent_decode_paths[struct]:
  rpt gen_tac >> strip_tac >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH,LENGTH_MAP] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by simp[MAP_ZIP] >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  drule abi_decoder_struct_infos >> disch_then (rewrite_tac o single) >>
  qpat_assum `MAP (FST o SND) fields = MAP SND args` (rewrite_tac o single) >>
  rewrite_tac[valueEncodingTheory.type_memory_size_def, type_memory_size_fields_sum,
    GSYM MAP_MAP_o] >>
  qpat_assum `MAP SND (ZIP _) = tvs` (rewrite_tac o single) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata (StructTV (ZIP (MAP FST args,tvs))) (w2n p)) =
   IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0)` by
    (once_rewrite_tac[cd_decode_def] >>
     qpat_assum `MAP SND (ZIP _) = tvs` (rewrite_tac o single) >>
     Cases_on `cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  rename1 `FLOOKUP s.vs_allocas oid = SOME (owner_base,cap)` >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) (BETA_RULE decode_finite_paths) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexistsl [`cap`,`oid`,`owner_base`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `env \\ nsid` >> first_assum ACCEPT_TAC
QED

Resume none_coherent_decode_paths[base]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    (irule (cj 1 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  `(?cl. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord cl) \/
    is_bytestring_type (BaseT bt)` by
    (Cases_on `is_word_type (BaseT bt)`
     >- (disj1_tac >> irule word_type_decoder_primitive >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qpat_x_assum `abi_decoder_scalar_valid _` mp_tac >>
     qpat_x_assum `~is_word_type _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `bt` >> simp[is_word_type_def, is_bytestring_type_def, abi_decoder_scalar_valid_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[is_word_type_def, is_bytestring_type_def, abi_decoder_scalar_valid_def]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) (BETA_RULE decode_leaf_paths) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [disj1_tac >> qexists_tac `cl` >> first_assum ACCEPT_TAC,
    disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC]
QED

Resume none_coherent_decode_paths[flag]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    (irule (cj 2 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  `?cl. type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord cl` by
    (irule word_type_decoder_primitive >> simp[is_word_type_def]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) (BETA_RULE decode_leaf_paths) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists_tac `cl` >> first_assum ACCEPT_TAC
QED

Resume none_coherent_decode_paths[dynamic]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))` by
    (irule (cj 3 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "nonbulk" >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) F n /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by
    (qpat_assum `~(_ \/ _)` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprLoweringTheory.type_to_abi_dec_info_def]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) (BETA_RULE decode_leaf_paths) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ (ArrayT _ _) _`)) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  qexistsl [`ty`,`n`,`type_to_abi_dec_info sf ce ty`,
    `abi_embedded_static_size ce.ce_struct_fields ty`,`type_memory_bytes ce ty`] >>
  asm_rewrite_tac[]
QED

Resume none_coherent_decode_paths[nonbulk]:
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `st.cs_blocks <> last.cs_blocks` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp_tac std_ss [exprLoweringTheory.type_to_abi_dec_info_def] >>
     disch_tac >> drule_all nonbulk_decoder_blocks_grow >> disch_then ACCEPT_TAC) >>
  `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `st.cs_blocks = last.cs_blocks \/ _`
       (DISJ_CASES_THEN2 (fn th => fs[th]) ACCEPT_TAC)) >>
  `type_memory_size (ArrayTV tv (Dynamic n)) = 32 + n * type_memory_size tv` by
    (once_rewrite_tac[valueEncodingTheory.type_memory_size_def] >> REFL_TAC) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) none_nonbulk_fold_paths >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ (ArrayT _ _) _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (mp_tac o Q.INST [`G` |-> `G`, `tn` |-> `tn`, `PG` |-> `PG`] o SPEC_ALL) >>
  qpat_x_assum `type_memory_size (ArrayTV _ _) = _` SUBST_ALL_TAC >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (disch_tac >> first_assum ACCEPT_TAC >> NO_TAC) >> suspend "nonbulk_child") >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `z` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))
    (qx_choose_then `v` (qx_choose_then `sc` (qx_choose_then `H`
      (qx_choose_then `u` strip_assume_tac)))))
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v /\
    v.vs_alloca_next + pending_alloca_size fn v <= w2n v.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK v,H,u)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all decoder_origin_path_allocation_frame >> strip_tac >>
     strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp v`
       (drule_then assume_tac) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `v.vs_alloca_next + pending_alloca_size fn v = _`
       (fn credit => qpat_assum `v.vs_initial_fmp = s.vs_initial_fmp`
         (fn fmp => PURE_REWRITE_TAC [credit,fmp])) >>
     first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`v`,`sc`,`H`,`u`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume none_coherent_decode_paths[nonbulk_child]:
  map_every qx_gen_tac [`a`,`b`,`q`,`sop`,`r`,`pw`,`e`,`A`,`ta`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(^decode_exit) a b fn` by
    (BETA_TAC >> Cases_on `b.cs_current_insts = []`
     >- (disj2_tac >>
         qpat_x_assum `b.cs_current_insts = [] ==> _` (drule_then ACCEPT_TAC)) >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ a = _`
       (mp_then Any mp_tac abi_decode_to_buf_nonempty_observer_phi) >>
     disch_then (qspec_then `fn` mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  pop_assum (assume_tac o BETA_RULE) >>
  rename1 `FLOOKUP r.vs_allocas oid = SOME (owner_base,cap)` >>
  `(^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
     a b limit ctx fn site sop q r pw e oid owner_base cap A ta lo` by
    (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (fn input =>
    qpat_x_assum `!st last limit ctx fn site src child s p d oid base cap G tn lo PG. _`
      (mp_tac o C MATCH_MP (BETA_RULE input))) >>
  disch_then (qspec_then `PG` (DISJ_CASES_THEN2
    (qx_choose_then `z` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))
    (qx_choose_then `v` (qx_choose_then `sc` (qx_choose_then `H`
      (qx_choose_then `u` strip_assume_tac))))))
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
  `allocas_from lo v /\ lo <= v.vs_alloca_next` by
    (irule decode_path_endpoint_floor >>
     qexistsl [`A`,`H`,`PG`,`ctx`,`fn`,`r`,`ta`,`u`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  disj2_tac >> qexistsl [`v`,`sc`,`H`,`u`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise none_coherent_decode_paths
