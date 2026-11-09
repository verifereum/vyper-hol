(* Source-only semantic inputs for the generic array iteration interface. *)
Theory entryReachBodySourceIterationInputs
Ancestors
  valueEncodingDefs entryReachBodyCanonicalArrayIteration entryReachBodySourceArrayInputs
  entryReachBodySourceArrayEntry
  entryReachBodySourceArrayBounds entryReachBodySourceMemberEntry
  abiDecoderCoherence vyperTyping vyperABI valueEncodingTyping compileEnv
  list arithmetic words

Theorem source_iteration_values[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) ==>
  LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  LENGTH xs <= maxn /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  strip_tac >>
  `LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn` by
    (irule entry_source_dynamic_array_alignment >>
     gvs[entry_source_metadata_def, Excl "enc_def"] >> metis_tac[]) >>
  `LENGTH avs < dimword (:256)` by
    (irule entry_source_array_count_word_bound >>
     qexistsl_tac [`Dynamic maxn`, `env`, `sb`,
       `ArrayTV tv (Dynamic maxn)`, `ty`, `ArrayV (DynArrayV xs)`] >>
     gvs[entry_source_metadata_def, Once vyper_to_abi_type_def, Excl "enc_def"]) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by fs[abi_decoder_header_def] >>
  `EVERY (value_has_type tv) xs` by
    fs[entry_source_metadata_def, value_has_type_def, all_have_type_EVERY, Excl "enc_def"] >>
  `EVERY (val_wf tv) xs` by
    (fs[EVERY_MEM] >> metis_tac[cj 1 value_has_type_val_wf]) >>
  simp[type_memory_bytes_def]
QED

Theorem entry_source_iteration_callback_config:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME (n2w sb) /\
  eval_operand dst prepared = SOME (n2w d) /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\ next+4 <= st.cs_next_var /\
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code st mid fn /\ st.cs_current_bb = body_lbl /\ st.cs_current_insts = [] /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) mid = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code mid last fn /\
  abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET ambient /\
  oid NOTIN ambient /\ cid < mid.cs_next_id /\ oid <> cid /\
  FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
  lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = last.cs_current_insts ++ abi_decode_backedge_insts last.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString nv)) ip hdr /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) prepared = n2w (LENGTH xs) /\
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) /\
  next <= nv /\ nv < limit_st.cs_next_var ==>
  iteration_callback_config cfg
Proof
  strip_tac >> drule_all source_iteration_values >> strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  simp[iteration_callback_config_def, Excl "enc_def"]
QED

(* Next operational interface (specification only, not an assumed theorem):
   For cfg with the tuple shape in entry_source_iteration_callback_config,
   iteration_callback_config cfg, parent source metadata/coherence at sf,
   and the actual setup/child compile equations with descriptor
   type_to_abi_dec_info sf ce ty, the proposed additional premises are

     (!j. j < LENGTH xs ==>
       entry_source_certified_child_producer cert ce env sf ty tv
         (EL j avs) (EL j xs) ctx fn oid root extent ambient
         b reserve site limit_st)
     /\ cert last

   and the intended conclusion is iteration_semantic_callback cfg.
   entry_source_array_owned_entry supplies the child source slice, metadata,
   strict cell/source endpoints and owned subregion at the post-setup state.
   The certified producer is instantiated at mid,last, the two operands in
   SND ops, source sb+abi_array_child_offset NONE aty avs j and destination
   d+32+j*type_memory_bytes ce ty. The setup and child paths/effects must be
   composed back to the pre-setup u; iteration_array_child_frame then restores
   the semantic frame and counter allocation. This composition is not proved
   here. cert last is explicit; if a caller has only a later certificate,
   it must separately supply backward transfer across that suffix.

   The legacy configuration's structural compile equations use
   ce.ce_struct_fields. A descending sf must NOT be equated with that map:
   the operational implication must retain actual setup/child equations at sf
   (or a separately proved descriptor equality), in addition to the generic
   configuration. The generic engine itself does not inspect those equations.
*)
