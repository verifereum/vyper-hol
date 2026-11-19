(* Join the actual index-zero cut to the finite decoder traversal. *)
Theory abiDecodeValidFiniteArray
Ancestors
  abiDecodeValidFiniteInit abiDecodeValidFiniteLoop abiValidAllocatedArraySource
  actualDecoderSites materializeSeparation fragGasOriginPtrLoop valueEncodingProps
  abiValidAllocatedContract abiDecoderCoherence abiDecoderRecursiveArray
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderIndexInit
  abiValidAllocatedArrayPrefix abiMalformedRecursiveInterface stateRelProj
  loweringStateRelDefs emitHelperProps exprLowering fragExec compileEnv
  abiDecodePtrMemberFrame bodyPtrDefs ptrDiscipline allocaHistory venomInst
  vyperValue vyperABI abiDecodeRanges abiDecoderContract
  finite_map pred_set words list rich_list arithmetic

local
val C = ``\ce env sf ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
 ~ctx_has_dalloca ctx /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s (type_memory_bytes ce ty) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
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
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
   tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
   alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
in
Theorem abi_valid_allocated_finite_array_joint:
  !ce env sf ty tv maxn.
    abi_decoder_coherent ce env sf ty tv /\ (^C) ce env sf ty tv /\
    abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    (is_abi_dynamic ce.ce_struct_fields ty \/
     dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
    (^C) ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  qabbrev_tac `outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` >>
  qabbrev_tac `sites = abi_malformed_scratch_sites st en func` >>
  `d+outsz < dimword (:256) /\ LENGTH xs = L` by
    (qhdtm_assum `abi_malformed_entry`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
     fs[abi_malformed_allocated_window_def] >> metis_tac[LENGTH_mem_bytes_at]) >>
  `maxn < dimword (:256)` by metis_tac[abi_decoder_coherent_array_capacity] >>
  `outsz = 32 + maxn * type_memory_size tv` by
    (qpat_assum `abi_decoder_coherent ce env sf (ArrayT _ _) _`
       (assume_tac o MATCH_MP abi_valid_allocated_array_memory_size) >>
     simp[Abbr `outsz`]) >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
   type_memory_bytes ce ty = type_memory_size tv` by fs[abi_decoder_header_def] >>
  qabbrev_tac `stride = abi_embedded_static_size ce.ce_struct_fields ty` >>
  `stride <= type_memory_size tv` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)`
     >- (`0 < type_slot_size tv` by
           fs[abi_decoder_header_def, Once evaluate_type_def, vyperASTTheory.bound_case_def] >>
         fs[Abbr `stride`, abi_member_head_size_def, type_memory_size_slots] >> decide_tac) >>
     fs[Abbr `stride`, abi_member_head_size_def, abi_decoder_header_def]) >>
  `maxn*stride < dimword (:256) /\ 32 <= outsz` by
    (`maxn*stride <= maxn*type_memory_size tv` by simp[LE_MULT_LCANCEL] >> decide_tac) >>
  qpat_x_assum `vyper_decode_valid_enc _ _`
    (assume_tac o PURE_REWRITE_RULE [cj 3 vyper_to_abi_type_def]) >>
  qpat_x_assum `abi_to_vyper _ _ _ = SOME _`
    (assume_tac o PURE_REWRITE_RULE [cj 3 vyper_to_abi_type_def]) >>
  drule_all abi_valid_allocated_array_source_view >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  `p+32+LENGTH vs*stride <= L` by simp[Abbr `stride`] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [Once type_to_abi_dec_info_def]) >>
  drule_all abi_decoder_recursive_array_code >>
  disch_then (qx_choosel_then [`setup`,`ls`] (map_every assume_tac o CONJUNCTS)) >>
  drule abi_decode_array_loop_init_trace >>
  disch_then (qx_choosel_then [`gs`,`hs`,`cnt`,`ip`,`addr`] strip_assume_tac) >>
  qpat_x_assum `setup = (_,_)` SUBST_ALL_TAC >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `MEM (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (ls.cs_next_var-1))]) (fn_insts func)` by
    (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >>
     `cs_extends st hs /\ cs_extends hs ls` by
       (rpt conj_tac >> irule cs_extends_same_block >>
        metis_tac[inst_extends_trans, inst_extends_def, IS_PREFIX_APPEND]) >>
     `fn_has_code hs ls func` by metis_tac[fn_has_code_split] >>
     drule actual_index_init_allocation_instruction >> strip_tac >>
     `ls.cs_next_id-2 = hs.cs_next_id /\ ls.cs_next_var-1 = hs.cs_next_var` by decide_tac >>
     fs[inst_extends_def] >> metis_tac[fn_has_code_current_instruction]) >>
  `ls.cs_next_id-2 IN sites` by
    (simp[Abbr `sites`, abi_malformed_scratch_sites_def] >>
     rpt conj_tac >> TRY decide_tac >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `abi_decoder_operand_live ls.cs_next_var (Var (STRING #"%" (toString (ls.cs_next_var-1))))` by
    simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def, ASCIInumbersTheory.toString_inj] >>
  `ip = Var (STRING #"%" (toString (ls.cs_next_var-1)))` by simp[] >>
  qpat_x_assum `ip = Var _` SUBST_ALL_TAC >>
  `abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
     ((Var (STRING #"%" (toString (ls.cs_next_var-1))),cnt),ls)` by simp[Abbr `stride`] >>
  `compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) stride (type_memory_bytes ce ty)
      (Var (STRING #"%" (toString (ls.cs_next_var-1)))) cnt ls = ((),en)` by
    (qhdtm_assum `compile_abi_decode_dyn_loop`
       (mp_tac o PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
     simp[Abbr `stride`]) >>
  `abi_malformed_entry H0 ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz s` by
    simp[Abbr `sites`, Abbr `outsz`] >>
  `LENGTH vs = abi_head_word (DROP p xs)` by metis_tac[] >>
  drule_all (Q.INST [`tv` |-> `tv`, `vs` |-> `vs`, `PG` |-> `PG`,
                    `sites` |-> `sites`, `outsz` |-> `outsz`] abi_valid_allocated_finite_init_joint) >>
  disch_then (qspecl_then [`tv`,`PG`]
    (qx_choosel_then [`head`,`slot`,`Gh`,`th`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  `abi_malformed_scratch_sites st en func SUBSET sites` by simp[Abbr `sites`] >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty) stride (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn` by
    simp[Once type_to_abi_dec_info_def, Abbr `stride`] >>
  `outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Abbr `outsz`] >>
  qhdtm_assum `abi_valid_allocated_array_inv`
    (mp_then Any (fn loop =>
      qhdtm_assum `abi_valid_allocated_entry` (mp_then Any (fn loop =>
        qpat_assum `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) = _`
          (mp_then Any (fn loop =>
            qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ stride _ = _`
              (mp_then Any (fn loop =>
                qpat_assum `abi_decode_ptr_window Gh th head _ _ _`
                  (mp_then Any mp_tac loop)) loop)) loop)) loop))
      (BETA_RULE abi_valid_allocated_finite_loop_joint)) >>
  disch_then (qspecl_then [`lo`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms])) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `abi_decode_sim ctx func s u` by metis_tac[abiDecoderLoopTheory.abi_decode_sim_trans] >>
  `abi_malformed_scratch_sites st en func = sites` by simp[NoAsms, Abbr `sites`] >>
  qexistsl [`u`,`Gu`,`tu`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qhdtm_assum `abi_valid_allocated_effect`
        (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_effect_def]) >>
      rewrite_tac[abi_valid_allocated_post_def] >>
      qpat_assum `abi_malformed_scratch_sites st en func = sites` SUBST1_TAC >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (first_x_assum irule >> simp[NoAsms, mem_agree_outside_def]) >>
      qpat_assum `en.cs_current_insts = []` SUBST1_TAC >>
      simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  TRY (goal_term (fn tm =>
    if boolSyntax.is_eq tm then
      (first_assum (fn th =>
          if boolSyntax.is_eq (concl th) andalso
             aconv (lhs (concl th)) (lhs tm)
          then SUBST1_TAC th else NO_TAC) >> first_assum ACCEPT_TAC)
    else NO_TAC))
  >- (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
        (qspecl_then [`D`,`explicit`] (irule_at Any)) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (head,Gh,th) _ _`
        (qspecl_then [`D`,`explicit`] ACCEPT_TAC))
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. abi_decoder_operand_live _ _ ==> FLOOKUP Gh _ = _ /\ _`
        (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (CONJUNCTS_THEN (SUBST1_TAC o SYM)) >>
      qpat_assum `!x. abi_decoder_operand_live _ _ ==> _ /\ FLOOKUP Gu _ = _ /\ _`
        (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp_tac bool_ss []) >>
  qhdtm_assum `abi_valid_allocated_array_inv`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_array_inv_def]) >>
  qpat_assum `abi_valid_allocated_effect _ _ _ _ _ _ _ _ _ _ s head`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_effect_def]) >>
  `alloca_inv head /\ s.vs_alloca_next <= head.vs_alloca_next` by
    (qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ s head`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `?H. stmt_state_rel H _ _ _ _ _ head`
       (qx_choose_then `Hhead`
         (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca))) >>
  `head.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (head,Gh,th) _ _`
       (mp_tac o SPEC_ALL) >>
     disch_then (mp_tac o CONJUNCT2 o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP fragGasPathPtrTheory.gas_path_ptr_erase) >>
     disch_then (mp_tac o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_path_frontier) >>
     simp_tac bool_ss []) >>
  gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  `~abi_malformed_site_range sites head u a 1` by
    (strip_tac >> qpat_assum `~abi_malformed_site_range sites s u a 1` mp_tac >>
     simp_tac bool_ss [] >> irule abi_valid_allocated_site_sequence >>
     qexists `head` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~abi_malformed_site_range sites s head a 1` by
    (strip_tac >> qpat_assum `~abi_malformed_site_range sites s u a 1` mp_tac >>
     simp_tac bool_ss [] >>
     qpat_assum `abi_malformed_site_range sites s head a 1`
       (strip_assume_tac o PURE_REWRITE_RULE [abiMalformedSiteFrameTheory.abi_malformed_site_range_def]) >>
     rewrite_tac[abiMalformedSiteFrameTheory.abi_malformed_site_range_def]
     >- (disj1_tac >> goal_assum (drule_at Any) >>
         rpt (goal_assum (drule_at Any))) >>
     disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     irule LESS_EQ_TRANS >> qexists `head.vs_alloca_next` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!a. _ /\ ~abi_malformed_site_range sites s head a 1 ==> _`
    (qspec_then `a` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (SUBST1_TAC o SYM) >>
  qpat_assum `!a. _ /\ ~abi_malformed_site_range sites head u a 1 ==> _`
    (qspec_then `a` irule) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
end
