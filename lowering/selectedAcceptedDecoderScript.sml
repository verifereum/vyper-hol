(* Exact acceptance of nonbulk arrays joins initialization and traversal at
   the same concrete header and ghost state. *)
Theory selectedAcceptedDecoder
Ancestors
  decoderOriginAllocationFrame
  selectedAcceptedInduction selectedAcceptedArrayPrepare selectedAcceptedArrayLoop
  selectedAcceptedInterfaces calldataMemberResourceFrame calldataDynOwned
  abiDecoderCoherence abiDecoderReentry abiDecoderFrame entryDecoderStateFrame
  normalizationPrefixPtr representationCleanPtr fragGasOriginPtr fragGasPathMem
  fragExec valueEncodingDefs valueEncodingProps vyperTyping
  venomState venomExecSemantics words pred_set finite_map list arithmetic

Theorem selected_argument_decoder_accepts:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    selected_decoder_accepts ce env sf ty tv
Proof
  match_mp_tac selected_argument_decoder_accepts_from_nonbulk >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[selected_decoder_accepts_def] >>
  map_every qx_gen_tac [`st`,`last`,`limit`,`ctx`,`fn`,`site`,`src`,`root`,`s`,
    `p`,`d`,`oid`,`base_addr`,`cap`,`G`,`tn`,`lower`,`PG`,`x`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `type_to_abi_dec_info sf ce (ArrayT ty _) = _` (fn th =>
    qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all selected_nonbulk_parent_to_header >>
  disch_then (qspec_then `PG` (List.foldr (uncurry qx_choose_then)
    (map_every assume_tac o CONJUNCTS)
    [`ip`,`cnt`,`guard_st`,`header_st`,`loop_st`,`labels`,`st0`,`ops`,`middle`,
     `st1`,`body_bb`,`exit_bb`,`n`,`vs`,`init_st`,`h`,`Gh`,`th`,`q`,`slot`])) >>
  qpat_x_assum `ip = Var q` SUBST_ALL_TAC >>
  qpat_x_assum `ei = type_to_abi_dec_info _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `asz = tv_abi_size tv` SUBST_ALL_TAC >>
  qpat_x_assum `msz = type_memory_size tv` SUBST_ALL_TAC >>
  qabbrev_tac `span = type_memory_size (ArrayTV tv (Dynamic maxn))` >>
  qabbrev_tac `live = loop_st.cs_next_var` >>
  qabbrev_tac `hdr = FST labels` >>
  qabbrev_tac `exit_lbl = SND (SND labels)` >>
  qpat_x_assum `st0.cs_current_bb = FST (SND labels)` (SUBST_ALL_TAC o SYM) >>
  `calldata_member_own fn st.cs_next_id last.cs_next_id h` by
    (rewrite_tac[calldata_member_own_def] >> first_assum ACCEPT_TAC) >>
  `lookup_var root h = SOME (n2w d)` by
    (qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `Var root` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `eval_operand (Var root) s = SOME (n2w d)` mp_tac >>
     simp[NoAsms, eval_operand_def]) >>
  `DISJOINT {a | slot <= a /\ a < slot+32} th.t_mem` by
    (simp[NoAsms, DISJOINT_ALT] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `hv = STRING #"%" (toString live)` >>
  qabbrev_tac `cv = STRING #"%" (toString (live+1))` >>
  qabbrev_tac `cmp = STRING #"%" (toString (live+2))` >>
  qabbrev_tac `dn = STRING #"%" (toString (live+3))` >>
  qabbrev_tac `bb = <|bb_label := hdr; bb_instructions :=
    abi_decode_header_insts (loop_st.cs_next_id+1) (Var q) src CALLDATALOAD
      hv cv cmp dn st0.cs_current_bb exit_lbl|>` >>
  qabbrev_tac `back_bb = <|bb_label := st1.cs_current_bb; bb_instructions :=
    st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id
      (STRING #"%" (toString st0.cs_next_var)) (STRING #"%" (toString st1.cs_next_var))
      (Var q) hdr|>` >>
  `bb.bb_instructions = abi_decode_header_insts (loop_st.cs_next_id+1)
     (Var q) src CALLDATALOAD hv cv cmp dn st0.cs_current_bb exit_lbl /\
   back_bb.bb_instructions = st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id
     (STRING #"%" (toString st0.cs_next_var)) (STRING #"%" (toString st1.cs_next_var)) (Var q) hdr` by
    simp[NoAsms, Abbr `bb`, Abbr `back_bb`] >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `!b. lookup_block hdr fn.fn_blocks = SOME b ==> _`
       (qspec_then `bb` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `!child. SND (SND ops) = Var child ==>
     compile_abi_decode_to_buf (Var child) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
       (type_to_abi_dec_info sf ce ty) middle = ((),st1)` by
    (rpt gen_tac >> disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `(!y. MEM y [hv;cv;cmp;dn] ==> ?k. y = STRING #"%" (toString k) /\ k < limit.cs_next_var) /\
   (!y. MEM y [hv;cv;cmp;dn] ==> ~abi_decoder_operand_live live (Var y)) /\
   ~abi_decoder_operand_live live (Var (STRING #"%" (toString st1.cs_next_var)))` by
    (qpat_assum `!y. MEM y (_::hv::cv::cmp::dn::[]) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[MEM] >> metis_tac[]) >>
  `n < dimword (:256) /\ live <= st0.cs_next_var /\
   middle.cs_next_var <= limit.cs_next_var /\ st1.cs_next_var <= limit.cs_next_var /\
   st1.cs_next_var < limit.cs_next_var /\ st.cs_next_id <= middle.cs_next_id` by decide_tac >>
  `h.vs_fmp = s.vs_fmp` by
    (qpat_assum `entry_decoder_obs s h` (ACCEPT_TAC o MATCH_MP entry_decoder_obs_fmp)) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp h /\
    h.vs_alloca_next + pending_alloca_size fn h <= w2n h.vs_initial_fmp)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK h,Gh,th)`
       (qspecl_then [`ARB`,`{}`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_inst_ids_distinct fn`,`h.vs_fmp = s.vs_fmp`,`alloca_inv h`,
        `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[decoder_origin_path_room]) >>
  mp_tac (SIMP_RULE bool_ss [ADD_CLAUSES, LENGTH, EVERY_DEF, APPEND,
      prim_recTheory.NOT_LESS_0, n2w_w2n]
    (Q.INST [`j` |-> `0`, `xs` |-> `[]`, `sb` |-> `w2n (p:bytes32)`,
      `remaining` |-> `n`, `cnt` |-> `n`, `pending` |-> `vs`,
      `s` |-> `h`, `G` |-> `Gh`, `tn` |-> `th`,
      `st` |-> `st0`, `ready` |-> `middle`, `last` |-> `st1`,
      `di` |-> `type_to_abi_dec_info sf ce ty`,
      `L` |-> `st.cs_next_id`, `H_id` |-> `last.cs_next_id`,
      `counter_id` |-> `header_st.cs_next_id`, `hid` |-> `loop_st.cs_next_id+1`,
      `bid` |-> `st1.cs_next_id`, `k` |-> `st1.cs_next_var`,
      `iv` |-> `STRING #"%" (toString st0.cs_next_var)`,
      `nv` |-> `STRING #"%" (toString st1.cs_next_var)`]
      (SPEC_ALL selected_array_header_to_exit))) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
  disch_then (List.foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS)
    [`v`,`Hv`,`tvn`,`sc`]) >>
  `abi_decode_footprint_frame [(d,span);(slot,32)] s h` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(d,32);(slot,32)]` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, MEM] >> rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`,`span`] >> simp[NoAsms] >> decide_tac) >>
     qexistsl_tac [`slot`,`32`] >> asm_rewrite_tac[MEM, LESS_EQ_REFL]) >>
  qpat_x_assum `entry_decoder_obs s h`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [entry_decoder_obs_def]) >>
  `calldata_member_resource_frame ctx fn site limit st.cs_next_id last.cs_next_id
       st.cs_next_var d span s h [(slot,32)]` by
    (rewrite_tac[calldata_member_resource_frame_def] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (rpt gen_tac >> disch_tac >>
        first_assum (irule o SPEC_ALL) >> decide_tac),
       (simp[NoAsms, calldata_member_wit_def, MEM] >>
        qexists_tac `header_st.cs_next_id` >> asm_rewrite_tac[])]) >>
  `calldata_member_resource_frame ctx fn site limit st.cs_next_id last.cs_next_id
       st.cs_next_var d span s v ((slot,32)::sc)` by
    (`calldata_member_resource_frame ctx fn site limit st.cs_next_id last.cs_next_id
        st.cs_next_var d span s v ([(slot,32)] ++ sc)` suffices_by simp[NoAsms] >>
     irule calldata_member_resource_extend >>
     qexistsl_tac [`last.cs_next_id`,`st.cs_next_id`,`live`,`d`,`span`,`h`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
  `!name. not_fresh_at st name ==>
      FLOOKUP Hv name = FLOOKUP G name /\ FLOOKUP tvn.t_var name = FLOOKUP tn.t_var name` by
    (qx_gen_tac `name` >> disch_tac >>
     `abi_decoder_operand_live live (Var name)` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
        rewrite_tac[calldata_operand_live_not_fresh] >> asm_rewrite_tac[]) >>
     qpat_assum `!y. not_fresh_at st y ==> _` (qspec_then `name` mp_tac) >>
     qpat_assum `!y. _ ==> FLOOKUP Hv y = _ /\ _` (qspec_then `name` mp_tac) >>
     qpat_assum `not_fresh_at st name` mp_tac >>
     qpat_assum `abi_decoder_operand_live live (Var name)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK v,Hv,tvn)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK h,Gh,th)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append o Q.SPECL [`D`,`explicit`]) >>
     disch_then (qspecl_then [`h`,`Gh`,`th`,`[]`,`OK v`,`Hv`,`tvn`] mp_tac) >>
     rewrite_tac[APPEND] >> disch_then irule >> asm_rewrite_tac[]) >>
  `!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn s)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK v,Hv,tvn)`
       (mp_then Any mp_tac selected_zero_path_mem o Q.SPECL [`ARB`,`{}`]) >>
     disch_then (mp_then Any mp_tac gas_path_mem_exec) >>
     qpat_assum `~v.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[exit_result_def]) >>
  `!mem. mem_agree_outside tvn.t_mem v.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) x d mem` by
    (qpat_assum `x = ArrayV (DynArrayV vs)` SUBST1_TAC >>
     mp_tac (Q.SPECL [`tv`,`vs`,`maxn`,`d`,`tvn.t_mem`,`v.vs_memory`]
       robust_dynarray_assemble) >>
     (impl_tac >-
       (qpat_assum `LENGTH vs = n` (fn th => rewrite_tac[th]) >>
        conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) x d v.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory (ArrayTV tv (Dynamic maxn)) x d mem`
        (qspec_then `v.vs_memory` mp_tac) >>
     simp[NoAsms, bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `value_has_type (ArrayTV tv (Dynamic maxn)) x /\ val_wf (ArrayTV tv (Dynamic maxn)) x` by
    (qpat_assum `x = ArrayV (DynArrayV vs)` SUBST1_TAC >>
     simp[NoAsms, value_has_type_def, val_wf_def, all_have_type_EVERY,
       memoryValueFrameTheory.elems_val_wf_every] >>
     qpat_assum `LENGTH vs = n` (fn th => rewrite_tac[th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `tvn.t_mem SUBSET tn.t_mem` by
    (irule SUBSET_TRANS >> qexists_tac `th.t_mem` >> asm_rewrite_tac[]) >>
  qpat_x_assum `calldata_member_resource_frame _ _ _ _ _ _ st.cs_next_var _ _ s v _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE
       [calldata_member_resource_frame_def, calldata_member_own_def, calldata_member_wit_def]) >>
  `v.vs_initial_fmp = s.vs_initial_fmp /\
   v.vs_alloca_next + pending_alloca_size fn v <=
     s.vs_alloca_next + pending_alloca_size fn s` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK v,Hv,tvn)`
       (qspecl_then [`ARB`,`{}`] assume_tac) >>
     drule_all decoder_origin_path_allocation_frame >> simp[NoAsms]) >>
  qexistsl_tac [`v`,`(slot,32)::sc`,`Hv`,`tvn`] >>
  asm_rewrite_tac[LENGTH]
QED
