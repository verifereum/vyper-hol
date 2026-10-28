(* Complex assembly around the single shared member execution spine. *)
Theory abiEncoderSharedComplex
Ancestors
  abiEncoderSharedMembersCorrect abiEncoderSharedMembersInput abiEncoderSharedMembersIndex
  abiDecoderDynamicLoopSetup abiEncoderMemberPhaseRaw abiDecoderReentryAddress abiEncoderMemberPhaseEffect abiScratchAddress abiEncoderAddressReach emitHelperProps emitHelper venomInst
  abiEncoderSharedArrayPrepare abiEncoderSharedContract abiEncoderComplexLayout
  abiEncoderComplexContext abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode abiEncoderOpenInput abiEncoderInput abiEncoderMembersDefs
  abiScratchEffect abiScratchEncoderContract abiEncoderRegisteredEffect abiEncoderExtendSim abiDecoderContract
  abiDecodeRanges abiDecoderAllocation abiDecoderReentry compileEnv valueEncoding contractABI venomState words list arithmetic pred_set

Theorem abi_encoder_shared_complex_head_length:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s ==>
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths tys 0
Proof
  simp_tac bool_ss [abi_encoder_shared_members_pre_def] >> strip_tac >>
  qpat_x_assum `abi_encoder_open_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_open_complex_iff]) >>
  gvs[abi_encoder_tuple_type_def] >> rename1 `head_lengths tys 0` >>
  `MAP (\(_,asz,_,_). asz) infos = MAP abi_member_head_size tys` by
    (irule (cj 1 abi_encoder_members_metadata) >> asm_simp_tac bool_ss [] >>
     rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[head_lengths_acc]
QED

Theorem abi_encoder_shared_complex_prepare:
  abi_encode_complex_prefix infos st = (dp,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_shared_input (AbiComplex infos,at,ListV avs) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\ abi_encoder_tuple_type at tys /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_shared_members_inv infos tys avs [] [] T dp st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id prepared.cs_next_id)
      [(d,output_size)] initial ready /\
    (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_cursor_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  drule_all abi_encoder_shared_members_root_pre >> strip_tac >>
  drule abi_encoder_shared_complex_head_length >> disch_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  `abi_encoder_shared_members_inv infos tys avs [] [] T dp st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready` by
    (irule abi_encoder_shared_members_initial_inv >> fs[]) >>
  qexistsl_tac [`ready`,`slot`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_complex_load_finish:
  emit_op MLOAD [dp] st = (out,final) /\ fn_has_code st final func /\
  abi_encoder_shared_members_inv [] [] [] tys avs T dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap initial /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?ready.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) ready.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out ready = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_scratch_effect first last lo final.cs_next_id st.cs_next_var limit_st d sz b cap initial ready /\
    abi_encoder_registered_effect (abi_decoder_ids lo final.cs_next_id) [(d,sz)] initial ready /\
    (alloca_inv initial ==> alloca_inv ready) /\
    ready.vs_current_bb = final.cs_current_bb /\ ready.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~ready.vs_halted /\ abi_encoder_extend_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_members_final_output >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_cursor_def]) >>
  drule_all abi_encoder_member_load_raw >> disch_then (qx_choose_then `ready` assume_tac) >>
  drule_all abi_encoder_member_load_transport >> strip_tac >>
  `abi_scratch_effect first last lo final.cs_next_id st.cs_next_var limit_st d sz b cap initial ready` by
    (irule abi_scratch_address_effect >> asm_rewrite_tac []) >>
  drule_all abi_encoder_member_load_registered >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids lo final.cs_next_id`] strip_assume_tac) >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def,is_terminator_def]) >>
  drule_all abi_encoder_member_phase_extend_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `ready` >> fs[abi_decoder_address_frame_def]
QED

Theorem abi_encoder_shared_complex_static_length:
  abi_encoder_shared_members_pre infos tys avs st src dst sb so d sz first last b cap s /\
  LIST_REL abi_encoder_structural_valid tys avs /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  LENGTH (enc (Tuple tys) (ListV avs)) = SUM (MAP (\(_,asz,_,_). asz) infos)
Proof
  strip_tac >> drule abi_encoder_shared_complex_head_length >> disch_tac >>
  drule abi_encoder_structural_list_layout >> disch_tac >>
  qpat_x_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_shared_members_pre_def]) >>
  disch_then (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
    REWRITE_RULE [abi_encoder_open_complex_iff]) >>
  gvs[abi_encoder_tuple_type_def] >> rename1 `head_lengths tys 0` >>
  `MAP (\(_,_,_,dyn). dyn) infos = MAP is_dynamic tys` by
    (irule (cj 2 abi_encoder_members_metadata) >> asm_simp_tac bool_ss [] >>
     rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  `~any_dynamic tys` by
    (qpat_x_assum `MAP (\(_,_,_,dyn). dyn) infos = _`
       (mp_tac o AP_TERM ``EXISTS I:bool list -> bool``) >>
     simp_tac bool_ss [EXISTS_MAP, ETA_AX] >>
     fs[GSYM abi_encoder_any_dynamic, EXISTS_MEM, EVERY_MEM, combinTheory.o_DEF] >>
     metis_tac[]) >>
  drule abi_encoder_static_tuple_tails >> disch_then (qspec_then `avs` assume_tac) >>
  drule abi_encoder_open_tuple_length >> simp[head_lengths_acc]
QED

Theorem abi_encoder_shared_complex_static_run:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st = (ignored,final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_members_inv infos tys avs [] [] F (Lit 0w) 0 0 first last st.cs_next_id
    st limit_st src dst sb 0 0 d hl (LENGTH (enc (Tuple tys) (ListV avs))) b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple tys) (ListV avs)) = SUM (MAP (\(_,asz,_,_). asz) infos) ==>
  ?actual. abi_encoder_shared_endpoint (ctx,func)
    (st,final,Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))),limit_st)
    (first,last,b,cap) (Tuple tys,ListV avs,d) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_members_correct >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_encoder_shared_members_final_output >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_members_inv [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_encoder_shared_endpoint_def, eval_operand_def, Excl "enc_def"]
QED

Theorem abi_encoder_shared_complex_static:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_encoder_shared (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?tys avs. av = ListV avs /\ abi_encoder_tuple_type at tys` by
    (qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
     simp_tac bool_ss [abi_encoder_open_complex_iff] >> metis_tac[]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_encoder_shared_members_root_pre >> strip_tac >>
  qpat_x_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all abi_encoder_shared_complex_static_length >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `EVERY (\(_,_,_,dyn). ~dyn) infos` by
    (fs[EVERY_MEM, EXISTS_MEM, Excl "enc_def"] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_x_assum `!e. MEM e infos ==> ~_`
       (qspec_then `(e0,e1,e2,e3)` mp_tac) >> simp[]) >>
  `abi_encoder_shared_members_inv infos tys avs [] [] F (Lit 0w) 0 0 first last start.cs_next_id
    start limit_st src dst sb 0 0 d (head_lengths tys 0)
    (LENGTH (enc (Tuple tys) (ListV avs))) b cap initial` by
    (irule abi_encoder_shared_members_initial_inv >>
     asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> decide_tac) >>
  drule_all abi_encoder_shared_complex_static_run >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` assume_tac)) >>
  qexists_tac `actual` >> gvs[abi_encoder_shared_endpoint_def, Excl "enc_def"]
QED

Theorem abi_encoder_shared_complex_slot_bound[local]:
  abi_encoder_shared_members_inv infos tys avs pre pvs T dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap s /\ st.cs_next_id <= last ==>
  slot < dimword (:256)
Proof
  simp_tac bool_ss [abi_encoder_shared_members_inv_def, abi_encoder_cursor_def] >>
  strip_tac >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `site IN abi_decoder_ids first last` by
    (simp_tac (srw_ss()) [abi_decoder_ids_def] >> decide_tac) >>
  qpat_x_assum `!id off sz. _ /\ FLOOKUP _ id = SOME (off,sz) ==> _`
    (qspecl_then [`site`,`slot`,`32`] mp_tac) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_shared_complex_effect_sequence[local]:
  abi_scratch_effect first last lo mid next limit_st d sz b cap initial ready /\
  abi_scratch_effect first last lo hi later limit_st d sz b cap ready actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo mid) [(d,sz)] initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] ready actual /\
  abi_encoder_extend_sim ctx func initial ready /\ abi_encoder_extend_sim ctx func ready actual /\
  first <= lo /\ lo <= mid /\ mid <= hi /\ hi <= last /\ next <= later ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
  abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  conj_tac >- (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
    qexists_tac `ready` >> asm_rewrite_tac []) >>
  conj_tac >- (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_complex_members_finish:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (ignored,middle) /\
  emit_op MLOAD [dp] middle = (out,final) /\
  fn_has_code st middle func /\ fn_has_code middle final func /\
  (st.cs_blocks = middle.cs_blocks \/
    !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_members_inv infos tys avs [] [] T dp site slot first last lo st limit_st
    src dst sb 0 0 d hl sz b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_scratch_effect first last lo final.cs_next_id st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo final.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_id <= last /\ middle.cs_next_id <= last /\
   middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `first <= lo /\ lo <= st.cs_next_id` by fs[abi_encoder_shared_members_inv_def] >>
  drule_all abi_encoder_shared_complex_slot_bound >> disch_tac >>
  drule_all abi_encoder_shared_members_correct >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qpat_x_assum `abi_encoder_shared_members_inv [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule_all abi_encoder_shared_complex_load_finish >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `abi_scratch_effect first last lo final.cs_next_id st.cs_next_var limit_st d sz b cap initial actual /\
   abi_encoder_registered_effect (abi_decoder_ids lo final.cs_next_id) [(d,sz)] initial actual /\
   abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_shared_complex_effect_sequence >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`middle.cs_next_var`,`middle.cs_next_id`,`encoded`] >>
     gvs[Excl "enc_def"] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_encoder_shared_complex_dynamic:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_encoder_shared (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?tys avs. av = ListV avs /\ abi_encoder_tuple_type at tys` by
    (qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
     simp_tac bool_ss [abi_encoder_open_complex_iff] >> metis_tac[]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_encoder_shared_members_root_pre >> strip_tac >>
  qpat_x_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all abi_encoder_complex_dynamic_context >>
  disch_then (qx_choose_then `dp` (qx_choose_then `prepared`
    (qx_choose_then `ignored` (qx_choose_then `middle` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `prepared.cs_next_id <= last /\ middle.cs_next_id <= last /\
   prepared.cs_next_var <= limit_st.cs_next_var /\ start.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `LENGTH (enc (Tuple tys) (ListV avs)) <= LENGTH (enc (Tuple tys) (ListV avs))` by simp[] >>
  drule_all abi_encoder_shared_complex_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encoder_shared_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all abi_encoder_shared_complex_members_finish >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var limit_st
     d (LENGTH (enc (Tuple tys) (ListV avs))) b cap initial actual /\
   abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
     [(d,LENGTH (enc (Tuple tys) (ListV avs)))] initial actual /\
   abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_shared_complex_effect_sequence >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`prepared.cs_next_var`,`prepared.cs_next_id`,`ready`] >>
     gvs[Excl "enc_def"] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_shared_endpoint_def] >>
  metis_tac[]
QED

Theorem abi_encoder_shared_complex:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos ==>
  abi_encoder_shared (AbiComplex infos)
Proof
  strip_tac >> Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- (irule abi_encoder_shared_complex_dynamic >> asm_rewrite_tac []) >>
  irule abi_encoder_shared_complex_static >> asm_rewrite_tac []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared complex admission, axiom or hypothesis"
  end) [abi_encoder_shared_complex_head_length,abi_encoder_shared_complex_prepare,
    abi_encoder_shared_complex_load_finish, abi_encoder_shared_complex_static_length,
    abi_encoder_shared_complex_static_run, abi_encoder_shared_complex_static,
    abi_encoder_shared_complex_slot_bound, abi_encoder_shared_complex_effect_sequence,
    abi_encoder_shared_complex_members_finish, abi_encoder_shared_complex_dynamic,
    abi_encoder_shared_complex];
