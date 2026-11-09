(* Persistent semantic frame for canonical finite array iteration. *)
Theory entryReachBodyCanonicalArrayIteration
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyConditionalArrayChild entryReachBodyConditionalProducer
  entryReachBodyCanonicalArrayChild entryReachBodyOwnedLoop entryReachBodyExactArrayLoop
  entryReachBodyRegisteredChild entryReachBodyEnclosingCounter entryReachBodyActualOwnedLoop
  entryReachBodyScratchSet entryReachBodyOwnedRegion
  abiDecoderLoopRegisters abiDecoderReentry abiDecoderContract
  abiEncoderRegisteredEffect abiDecoderExecution abiDecoderArrayBackedge
  valueEncoding valueEncodingProps venomMemProofs venomState venomInst exprLoweringProps
  emitHelperProps compileEnv pred_set finite_map words list arithmetic
  calldataDynOwned abiDecoderArrayInvariant

(* The memory predicate is separate from execution/resource invariants: this
   frame does not assert an exact prefix or a loop callback. *)
Definition iteration_frame_def:
  iteration_frame next limit_st prepared sites b reserve P u <=>
    entry_loop_fields prepared u /\ fresh_vars_wrt limit_st u /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
      eval_operand op u = SOME w) /\
    P u.vs_memory /\ entry_scratch_ready sites b reserve u
End

Theorem iteration_frame_initial[local]:
  fresh_vars_wrt limit_st prepared /\ P prepared.vs_memory /\
  entry_scratch_ready sites b reserve prepared ==>
  iteration_frame next limit_st prepared sites b reserve P prepared
Proof
  simp[iteration_frame_def, entry_loop_fields_def]
QED

Theorem iteration_frame_header[local]:
  next+4 <= limit_st.cs_next_var /\
  iteration_frame next limit_st prepared sites b reserve P u ==>
  iteration_frame next limit_st prepared sites b reserve P
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j n u))
Proof
  simp_tac bool_ss [iteration_frame_def] >> strip_tac >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`n`,`j`] strip_assume_tac) >>
  asm_simp_tac (srw_ss()) [] >>
  gvs[entry_loop_fields_def, entry_scratch_ready_def, entry_scratch_missing_def,
     jump_to_def, abi_decode_header_state_def, update_var_def] >> metis_tac[]
QED

Theorem iteration_frame_backedge[local]:
  next <= nv /\ nv < limit_st.cs_next_var /\
  iteration_frame next limit_st prepared sites b reserve P u /\
  P (mstore q w u).vs_memory ==>
  iteration_frame next limit_st prepared sites b reserve P
    (jump_to hdr (mstore q w (update_var (STRING #"%" (toString nv)) v u)))
Proof
  simp_tac bool_ss [iteration_frame_def] >> strip_tac >>
  drule_all abi_decoder_generated_update_fresh >> disch_then (qspec_then `v` assume_tac) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
    eval_operand op (update_var (STRING #"%" (toString nv)) v u) = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live nv op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
     simp[abi_decoder_generated_update_operand]) >>
  asm_simp_tac (srw_ss()) [eval_operand_mstore, fresh_vars_wrt_def, lookup_var_def] >>
  gvs[entry_loop_fields_def, entry_scratch_ready_def, entry_scratch_missing_def,
     jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def,
     fresh_vars_wrt_def, lookup_var_def] >> metis_tac[]
QED

Theorem iteration_frame_child[local]:
  iteration_frame next limit_st prepared sites b reserve P s /\
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
  entry_scratch_ready sites b reserve t /\ next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ P t.vs_memory ==>
  iteration_frame next limit_st prepared sites b reserve P t
Proof
  simp_tac bool_ss [iteration_frame_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[entry_registered_fields_trans] >>
  rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  metis_tac[]
QED

Theorem iteration_array_child_frame:
  iteration_frame next limit_st prepared sites b reserve
    (\m. mem_word_at d m = n2w n) s /\
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
  entry_scratch_ready sites b reserve t /\ next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  entry_owned_region oid root extent d total_sz s /\ 32 <= total_sz /\
  oid NOTIN ids /\ alloca_inv t /\ d+32 <= cell /\
  abi_encoder_registered_effect ids [(cell,sz)] s t ==>
  iteration_frame next limit_st prepared sites b reserve
    (\m. mem_word_at d m = n2w n) t
Proof
  strip_tac >> irule iteration_frame_child >> asm_rewrite_tac[] >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (irule entry_registered_child_slice >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     fs[entry_owned_region_def] >> goal_assum (drule_at Any) >> simp[]) >>
  fs[iteration_frame_def, mem_word_at_def, mem_bytes_at_def] >> metis_tac[]
QED

Theorem iteration_array_backedge_frame[local]:
  next <= nv /\ nv < limit_st.cs_next_var /\
  iteration_frame next limit_st prepared sites b reserve
    (\m. mem_word_at d m = n2w n) u /\
  entry_owned_loop_resources ctx fn site cid q oid root extent d total_sz u /\
  oid <> cid /\ 32 <= total_sz ==>
  iteration_frame next limit_st prepared sites b reserve
    (\m. mem_word_at d m = n2w n)
    (jump_to hdr (mstore q w (update_var (STRING #"%" (toString nv)) v u)))
Proof
  strip_tac >>
  `d+32 <= q \/ q+32 <= d` by
    (fs[entry_owned_loop_resources_def] >>
     drule entry_owned_region_counter_separation >>
     disch_then (qspecl_then [`q`,`cid`] mp_tac) >> simp[] >> decide_tac) >>
  irule iteration_frame_backedge >> asm_rewrite_tac[] >>
  asm_simp_tac (srw_ss()) [mstore_mem_word_at_disjoint] >>
  fs[iteration_frame_def]
QED

Theorem iteration_frame_inputs:
  iteration_frame next limit_st prepared sites b reserve P u /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME (n2w sb) /\
  eval_operand dst prepared = SOME (n2w d) /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD prepared) = bytes /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) prepared = n2w n ==>
  eval_operand ip u = SOME p /\ eval_operand src u = SOME (n2w sb) /\
  eval_operand dst u = SOME (n2w d) /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD u) = bytes /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) u = n2w n
Proof
  simp_tac bool_ss [iteration_frame_def] >> strip_tac >>
  fs[entry_loop_fields_def, abi_decode_load_def, abi_decode_source_def] >> metis_tac[]
QED

Definition iteration_body_def:
  iteration_body next limit_st prepared sites b reserve d n p j u <=>
    iteration_frame next limit_st prepared sites b reserve
      (\m. mem_word_at d m = n2w n) u /\ mload (w2n p) u = n2w j
End

Theorem iteration_header_body[local]:
  next+4 <= limit_st.cs_next_var /\
  iteration_frame next limit_st prepared sites b reserve
    (\m. mem_word_at d m = n2w n) u /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr n j u ==>
  iteration_body next limit_st prepared sites b reserve d n p j
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j n u))
Proof
  strip_tac >> simp_tac bool_ss [iteration_body_def] >> conj_tac
  >- (irule iteration_frame_header >> simp[]) >>
  fs[abi_decode_loop_ready_def, mload_def, jump_to_def,
     abi_decode_header_state_def, update_var_def]
QED

(* Fixed compilation/CFG facts are separated from the three semantic phases.
   In particular, the child effect is its actual window, not the ambient reserve. *)
Definition iteration_config_def:
  iteration_config
    ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) <=>
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
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
  (!j. j < LENGTH xs ==> array_child_producer ce env ty tv (EL j avs) (EL j xs)
    ctx fn oid root extent ambient b reserve site limit_st) /\
  abi_decode_loop_cfg fn hdr body_lbl exit hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
End

(* The producer-independent certificate is shared by both producer interfaces.
   iteration_config_def remains the established unconditional package. *)
Definition iteration_static_config_def:
  iteration_static_config
    ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) <=>
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
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
  next <= nv /\ nv < limit_st.cs_next_var /\
  LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
End

(* The iterator consumes operational phase facts, not a compiler descriptor. *)
Definition iteration_callback_config_def:
  iteration_callback_config
    ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) <=>
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
  next <= nv /\ nv < limit_st.cs_next_var /\
  LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  LENGTH xs <= maxn /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
End

Definition iteration_semantic_callback_def:
  iteration_semantic_callback
    ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,(nv:num)),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) <=>
  !j u.
    iteration_body next limit_st prepared ambient b reserve d (LENGTH xs) p j u /\
    j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) u ==>
    ?t. iteration_frame next limit_st prepared ambient b reserve
        (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
      entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
        (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString nv))
        ip hdr src p (n2w sb) (LENGTH xs) j t /\
      entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
        (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
      val_in_memory tv (EL j xs) (d+(j*type_memory_size tv+32)) t.vs_memory /\
      entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
      abi_encoder_registered_effect
        (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
        [(d+(j*type_memory_size tv+32),type_memory_size tv)] u t
End

Theorem iteration_conditional_callback:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  (!j. j < LENGTH xs ==> entry_conditional_array_child_producer ce env ty tv (EL j avs) (EL j xs)
    ctx fn oid root extent ambient b reserve site limit_st) /\
  iteration_body next limit_st prepared ambient b reserve d (LENGTH xs) p j u /\
  j < LENGTH xs /\ ~u.vs_halted /\ u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) u ==>
  ?t. iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
      (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString nv))
      ip hdr src p (n2w sb) (LENGTH xs) j t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    val_in_memory tv (EL j xs) (d+(j*type_memory_size tv+32)) t.vs_memory /\
    entry_loop_fields u t /\ entry_decode_path ctx fn u t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d+(j*type_memory_size tv+32),type_memory_size tv)] u t
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `iteration_static_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_static_config_def]) >>
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
  `eval_operand ip u = SOME p` by fs[iteration_frame_def] >>
  `?t. array_child_result ctx fn oid root extent ambient
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      b reserve site limit_st st last (d+32+j*type_memory_bytes ce ty) tv (EL j xs) u t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
      (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString nv))
      ip hdr src p (n2w sb) (LENGTH xs) j t /\
    mload (w2n p) t = n2w j /\ FLOOKUP t.vs_allocas cid = SOME (w2n p,32)` by
    (irule (SIMP_RULE bool_ss [] entry_conditional_canonical_array_child) >>
     simp[Excl "enc_def"] >> conj_tac
     >- (qexistsl_tac [`dst`,`ops`] >> gvs[Excl "enc_def"]) >>
     qexistsl_tac [`avs`,`env`,`maxn`,`parent_di`] >> simp[Excl "enc_def"]) >>
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

Theorem entry_generic_array_callback_contract:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_callback_config cfg /\
  iteration_semantic_callback cfg ==>
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid
    last.cs_current_bb last.cs_current_insts last.cs_next_id ip src
    (STRING #"%" (toString next)) (STRING #"%" (toString st.cs_next_var))
    (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
    (STRING #"%" (toString nv)) p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent
    (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
    (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
    (\j u. iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) u)
    (iteration_body next limit_st prepared ambient b reserve d (LENGTH xs) p)
    (\j u. iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) u)
    (iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)))
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_assum `iteration_callback_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_callback_config_def]) >>
  `src <> Var (STRING #"%" (toString next)) /\
   ip <> Var (STRING #"%" (toString nv)) /\ src <> Var (STRING #"%" (toString nv))` by
    (rpt conj_tac >> irule abi_decoder_live_excludes_output >>
     qexists_tac `next` >> simp[]) >>
  `oid NOTIN window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id)` by
    metis_tac[SUBSET_DEF] >>
  simp_tac bool_ss [entry_actual_owned_indexed_contract_def] >>
  asm_rewrite_tac[] >> simp[Excl "enc_def", SUBSET_DEF] >> rpt conj_tac
  >- suspend "header"
  >- suspend "child"
  >> suspend "backedge"
QED
Resume entry_generic_array_callback_contract[header]:
  rpt strip_tac >> Cases_on `j < LENGTH xs`
  >- (simp[] >> irule iteration_header_body >>
      fs[entry_owned_loop_inv_def, SF SFY_ss, Excl "enc_def"]) >>
  simp[] >> irule iteration_frame_header >> simp[]
QED
Resume entry_generic_array_callback_contract[child]:
  rpt strip_tac >>
  qhdtm_x_assum `iteration_semantic_callback`
    (mp_tac o PURE_REWRITE_RULE [iteration_semantic_callback_def]) >>
  disch_then (qspecl_then [`j`,`u`] mp_tac) >> simp[]
QED
Resume entry_generic_array_callback_contract[backedge]:
  rpt strip_tac >> irule iteration_array_backedge_frame >>
  asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[]
QED
Finalise entry_generic_array_callback_contract

Theorem entry_generic_array_callback_iteration:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_callback_config cfg /\
  iteration_semantic_callback cfg /\
  entry_owned_loop_inv ctx fn site hdr ip src p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent j s /\
  iteration_frame next limit_st prepared ambient b reserve
    (\m. mem_word_at d m = n2w (LENGTH xs)) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_generic_array_callback_contract >> strip_tac >>
  drule entry_actual_owned_indexed_array_loop_from_index >>
  simp_tac bool_ss [] >> disch_then drule >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule (cj 2 calldata_terminal_array_memory) >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `iteration_callback_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_callback_config_def]) >>
  fs[entry_loop_prefix_def, iteration_frame_def, Excl "enc_def"] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem iteration_static_callback_config:
  iteration_static_config cfg ==> iteration_callback_config cfg
Proof
  PairCases_on `cfg` >> strip_tac >>
  qhdtm_x_assum `iteration_static_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_static_config_def]) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  simp[iteration_callback_config_def, Excl "enc_def"]
QED

Theorem entry_array_callback_contract:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  iteration_semantic_callback cfg ==>
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit hid
    last.cs_current_bb last.cs_current_insts last.cs_next_id ip src
    (STRING #"%" (toString next)) (STRING #"%" (toString st.cs_next_var))
    (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
    (STRING #"%" (toString nv)) p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent
    (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
    (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
    (\j u. iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) u)
    (iteration_body next limit_st prepared ambient b reserve d (LENGTH xs) p)
    (\j u. iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) u)
    (iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)))
Proof
  strip_tac >> drule iteration_static_callback_config >> strip_tac >>
  drule_all entry_generic_array_callback_contract >> simp[]
QED

Theorem entry_array_callback_iteration:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  iteration_semantic_callback cfg /\
  entry_owned_loop_inv ctx fn site hdr ip src p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent j s /\
  iteration_frame next limit_st prepared ambient b reserve
    (\m. mem_word_at d m = n2w (LENGTH xs)) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> drule iteration_static_callback_config >> strip_tac >>
  drule_all entry_generic_array_callback_iteration >> simp[]
QED

Theorem iteration_conditional_semantic_callback:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  (!j. j < LENGTH xs ==> entry_conditional_array_child_producer ce env ty tv
    (EL j avs) (EL j xs) ctx fn oid root extent ambient b reserve site limit_st) ==>
  iteration_semantic_callback cfg
Proof
  strip_tac >> qpat_assum `cfg = _` SUBST_ALL_TAC >>
  simp_tac bool_ss [iteration_semantic_callback_def] >> rpt strip_tac >>
  irule (SRULE [] iteration_conditional_callback) >>
  simp[Excl "enc_def"] >>
  qpat_assum `iteration_static_config _` (irule_at Any) >> simp[]
QED

Theorem iteration_config_static[local]:
  iteration_config cfg ==> iteration_static_config cfg
Proof
  PairCases_on `cfg` >>
  simp_tac bool_ss [iteration_config_def, iteration_static_config_def] >>
  rpt strip_tac >> asm_rewrite_tac[]
QED

Theorem iteration_config_callback[local]:
  iteration_config cfg ==> iteration_semantic_callback cfg
Proof
  PairCases_on `cfg` >> strip_tac >>
  drule iteration_config_static >> strip_tac >>
  irule (SRULE [] iteration_conditional_semantic_callback) >>
  simp[Excl "enc_def"] >>
  fs[iteration_config_def, Excl "enc_def"] >> rpt strip_tac >>
  irule entry_unconditional_producer_implies_conditional >> simp[]
QED

Theorem entry_canonical_dynamic_array_iteration:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_config cfg /\
  entry_owned_loop_inv ctx fn site hdr ip src p (n2w sb) tv xs d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent j s /\
  iteration_frame next limit_st prepared ambient b reserve
    (\m. mem_word_at d m = n2w (LENGTH xs)) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] s t
Proof
  strip_tac >> drule iteration_config_static >> strip_tac >>
  drule iteration_config_callback >> strip_tac >>
  drule_all entry_array_callback_iteration >> simp[]
QED
