(* Source-certified semantic callback for the existing array iteration engine. *)
Theory entryReachBodySourceIterationCallback
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySourceArrayChild entryReachBodySourceIterationInputs
  entryReachBodyCanonicalArrayIteration entryReachBodyOwnedRegion
  entryReachBodySourceProducer entryReachBodyExactArrayLoop
  abiEncoderRegisteredEffect abiDecoderContract abiDecoderCoherence
  abiDecoderReentry entryReachBodyOwnedLoop
  entryReachBodyCanonicalArrayChild
  venomState venomInst venomExecSemantics arithmetic words pred_set

Theorem entry_source_certified_iteration_callback:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_callback_config cfg /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),last) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  cert last /\
  (!j. j < LENGTH xs ==> entry_source_certified_child_producer cert
    ce env sf ty tv (EL j avs) (EL j xs) ctx fn oid root extent ambient b reserve site limit_st) ==>
  iteration_semantic_callback cfg
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `iteration_callback_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_callback_config_def]) >>
  simp_tac bool_ss [iteration_semantic_callback_def] >> rpt strip_tac >>
  qhdtm_x_assum `iteration_body`
    (strip_assume_tac o PURE_REWRITE_RULE [iteration_body_def]) >>
  drule_all iteration_frame_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var ip /\
   abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono, LESS_EQ_TRANS, DECIDE ``n <= n+4``] >>
  `fresh_vars_wrt limit_st u /\ entry_scratch_ready ambient b reserve u` by
    fs[iteration_frame_def] >>
  qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_loop_resources_def]) >>
  `eval_operand ip u = SOME p /\
   u.vs_current_bb = st.cs_current_bb /\
   u.vs_inst_idx = LENGTH st.cs_current_insts` by fs[iteration_frame_def] >>
  suspend "execute"
QED
Resume entry_source_certified_iteration_callback[execute]:
  `entry_source_certified_child_producer cert ce env sf ty tv
     (EL j avs) (EL j xs) ctx fn oid root extent ambient b reserve site limit_st` by
    metis_tac[] >>
  drule_at (Pat `entry_source_certified_child_producer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SIMP_RULE bool_ss [] entry_source_certified_array_child) >>
  disch_then (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `entry_source_metadata _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `entry_owned_region _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  simp[Excl "enc_def"] >>
  disch_then (qspecl_then [`sb`,`LENGTH xs`] mp_tac) >>
  simp[Excl "enc_def"] >> strip_tac >>
  qhdtm_x_assum `array_child_result`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `oid NOTIN window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id)` by
    metis_tac[SUBSET_DEF] >>
  `entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t` by
    (irule entry_owned_region_preserved >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >> simp[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [entry_owned_loop_resources_def] >>
  gvs[Excl "enc_def"] >>
  irule iteration_array_child_frame >>
  qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
    `root`,`oid`,`extent`,`st.cs_next_var`] >> simp[]
QED
Finalise entry_source_certified_iteration_callback
