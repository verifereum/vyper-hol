(* Canonical heterogeneous traversal: semantic prefix advancement. *)
Theory entryReachBodyCanonicalMembers
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyMemberPrefix entryReachBodyCanonicalMemberEntry
  entryReachBodyEmptyMember entryReachBodyMemberIteration
  abiDecoderMembers abiDecoderMemberInfos valueEncodingTyping
  entryReachBodyOwnedRegion abiEncoderRegisteredEffect
  entryReachBodyExactArrayLoop abiDecoderContract abiDecoderDynamicLoopSetup
  entryReachBodyScratchSet abiAllocationHistory allocaFrontierBound
  entryReachBodyMemberSetup abiDecoderDynamic abiDecoderOffset abiDecoderCode
  abiEncoderWindowContract allocaBudgetProps entryReachBodyOperationalPath
  abiDecoderReentry abiDecoderMemberSetup abiDecoderMemberBody abiDecoderCoherence
  entryReachBodyScratchSites abiDecoderAllocation abiDecoderMemberCons
  abiEncoder emitHelper compileEnv valueEncoding list rich_list arithmetic pred_set

Theorem canonical_members_prefix_wf[local]:
  abi_decoder_members ce env sf tys tvs avs vs ==> LIST_REL val_wf tvs vs
Proof
  strip_tac >> drule abi_decoder_members_relations >> strip_tac >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule (cj 1 value_has_type_val_wf) >> first_x_assum irule >> simp[]
QED

Theorem canonical_members_prefix_extend[local]:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  tuple_in_memory prevs pretvs d s.vs_memory /\
  entry_owned_region oid root extent d outsz s /\
  SUM (MAP (type_memory_bytes ce) pretys) <= outsz /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP (type_memory_bytes ce) pretys),sz)] s t /\ alloca_inv t /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory ==>
  tuple_in_memory (prevs ++ [v]) (pretvs ++ [tv]) d t.vs_memory
Proof
  strip_tac >>
  `LIST_REL val_wf pretvs prevs` by metis_tac[canonical_members_prefix_wf] >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >>
  irule entry_member_memory_extend >> metis_tac[]
QED

(* The semantic part of the traversal cursor.  Resource and operational
   frames are kept separately, so the child contract is about one decoder,
   rather than preservation of this traversal invariant. *)
Definition canonical_members_semantics_def:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs tys tvs avs vs s <=>
    fulltys = pretys ++ tys /\ fulltvs = pretvs ++ tvs /\
    fullavs = preavs ++ avs /\ fullvs = prevs ++ vs /\
    abi_decoder_members ce env ce.ce_struct_fields pretys pretvs preavs prevs /\
    abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
    mem_bytes_at sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)))
      (abi_decode_source CALLDATALOAD s) =
      enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs) /\
    tuple_in_memory prevs pretvs d s.vs_memory
End

Theorem canonical_members_semantics_initial[local]:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) ==>
  canonical_members_semantics ce env tys tvs avs vs sb d
    [] [] [] [] tys tvs avs vs s
Proof
  simp[canonical_members_semantics_def, abi_decoder_members_def,
       val_in_memory_def]
QED

Theorem canonical_members_semantics_final[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs [] [] [] [] s ==>
  tuple_in_memory fullvs fulltvs d s.vs_memory
Proof
  simp[canonical_members_semantics_def]
QED

Theorem canonical_members_semantics_advance[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  entry_owned_region oid root extent d
    (SUM (MAP (type_memory_bytes ce) fulltys)) s /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP (type_memory_bytes ce) pretys),type_memory_size tv)] s t /\
  alloca_inv t /\ entry_loop_fields s t /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory ==>
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
    tys tvs avs vs t
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  `tuple_in_memory (prevs ++ [v]) (pretvs ++ [tv]) d t.vs_memory` by
    (irule canonical_members_prefix_extend >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     qpat_assum `entry_owned_region _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `abi_decoder_members _ _ _ pretys _ _ _` (irule_at Any) >>
     asm_rewrite_tac[] >> simp[MAP_APPEND, SUM_APPEND]) >>
  `abi_decoder_members ce env ce.ce_struct_fields [ty] [tv] [av] [v] /\
   abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs` by
    fs[abi_decoder_members_def] >>
  `abi_decoder_members ce env ce.ce_struct_fields
     (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])` by
    (qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
       (mp_tac o MATCH_MP abi_decoder_members_lengths) >> strip_tac >>
     simp[abi_decoder_members_append]) >>
  `abi_decode_source CALLDATALOAD t = abi_decode_source CALLDATALOAD s` by
    fs[entry_loop_fields_def, abi_decode_source_def] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` mp_tac >>
  asm_rewrite_tac[]
QED

Theorem canonical_members_empty_advance[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty = DecComplex T [] /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) F ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (DecComplex T []) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d
    (SUM (MAP (type_memory_bytes ce) fulltys)) s /\ oid NOTIN sites /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s ==>
  ?t. entry_decode_path ctx fn s t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
      tys tvs avs vs t /\
    val_in_memory tv v (d+vo) t.vs_memory /\
    entry_loop_fields s t /\ abi_decoder_address_frame st.cs_next_var s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    abi_encoder_registered_effect sites [(d+vo,type_memory_size tv)] s t /\
    entry_scratch_ready sites b cap t /\ alloca_inv t /\
    abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d
      (SUM (MAP (type_memory_bytes ce) fulltys)) t /\
    fresh_vars_wrt limit_st t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\ t.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
   abi_decoder_metadata ce env ty tv (DecComplex T []) av v` by
    fs[canonical_members_semantics_def, abi_decoder_members_def] >>
  `abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (DecComplex T [])) ao vo st = (ops,mid)` by
    (qpat_x_assum `abi_decode_member_setup _ _ _ _ F _ _ _ = _` mp_tac >>
     simp[abi_decoder_needs_offset_iff]) >>
  mp_tac (Q.INST [`ei` |-> `DecComplex T []`] entry_empty_dynamic_member_endpoint) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `abi_encoder_registered_effect sites [(d+vo,type_memory_size tv)] s u` by
    fs[abi_encoder_registered_effect_def, entry_loop_fields_def] >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d
     (SUM (MAP (type_memory_bytes ce) fulltys)) u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> simp[]) >>
  `canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
      tys tvs avs vs u` by
    (gvs[] >> irule canonical_members_semantics_advance >>
     asm_rewrite_tac[] >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     qpat_assum `entry_owned_region _ _ _ _ _ s` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  qexists_tac `u` >> asm_rewrite_tac[]
QED

(* Exact child IH interface: it mentions only the child descriptor/value and
   its owned window, never a processed/remaining tuple cursor. *)
Definition canonical_member_result_def:
  canonical_member_result ctx fn oid root extent sites b cap site limit_st
    st last d tv v s t <=>
    entry_decode_path ctx fn s t /\ val_in_memory tv v d t.vs_memory /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
    entry_scratch_ready sites b cap t /\ alloca_inv t /\
    abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_size tv) t /\
    abi_encoder_registered_effect sites [(d,type_memory_size tv)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts
End

Definition canonical_member_child_def:
  canonical_member_child ce env ty tv av v ctx fn oid root extent sites b cap site limit_st <=>
    !st last dst src sb d s.
      compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
        (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
      abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
      mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
        (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
      sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
      d+type_memory_size tv < dimword (:256) /\
      eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
      abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
      last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
      fn_has_code st last fn /\ abi_decoder_code st last /\
      fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
      oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
      window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites /\
      oid NOTIN sites /\ entry_scratch_ready sites b cap s /\ alloca_inv s /\
      abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
      entry_owned_region oid root extent d (type_memory_size tv) s /\
      ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      ?t. canonical_member_result ctx fn oid root extent sites b cap site limit_st
        st last d tv v s t
End

Theorem canonical_member_result_prepend[local]:
  canonical_member_result ctx fn oid root extent sites b cap site limit_st
    mid last d tv v u t /\
  entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
  abi_decoder_address_frame st.cs_next_var s u /\ st.cs_next_var <= mid.cs_next_var ==>
  canonical_member_result ctx fn oid root extent sites b cap site limit_st
    st last d tv v s t
Proof
  simp_tac bool_ss [canonical_member_result_def] >> strip_tac >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  `abi_encoder_registered_effect sites [(d,type_memory_size tv)] s u` by
    fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def,
       entry_loop_fields_def] >>
  `abi_encoder_registered_effect sites [(d,type_memory_size tv)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `eval_operand op u = SOME w` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED


Theorem canonical_members_navigation[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty <> DecComplex T [] /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao vo st = (ops,mid) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w (sb + abi_tuple_child_offset
      (MAP (vyper_to_abi_type env) fulltys) fullavs (LENGTH pretys))) /\
    eval_operand (SND ops) u = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    mem_bytes_at (sb + abi_tuple_child_offset
      (MAP (vyper_to_abi_type env) fulltys) fullavs (LENGTH pretys))
      (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source CALLDATALOAD u) =
      enc (vyper_to_abi_type env ty) av /\
    sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) fulltys) fullavs (LENGTH pretys) +
      LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    d+vo+type_memory_size tv < dimword (:256) /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    entry_owned_region oid root extent (d+vo) (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  strip_tac >>
  qpat_assum `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_semantics_def]) >>
  irule entry_canonical_member_owned_entry >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule entry_nonempty_member_offset >> asm_rewrite_tac[] >>
      qexists_tac `tv` >> fs[abi_decoder_members_def, Excl "enc_def"]) >>
  qpat_assum `abi_decoder_members _ _ _ (_::_) (_::_) (_::_) (_::_)`
    (irule_at (Pat `abi_decoder_members _ _ _ (_::_) (_::_) (_::_) (_::_)`)) >>
  last_assum (irule_at (Pat `abi_decoder_members _ _ _ _ _ _ _`)) >>
  simp_tac bool_ss [] >>
  qpat_assum `eval_operand src s = _` (irule_at (Pat `eval_operand _ _ = SOME (n2w sb)`)) >>
  qpat_assum `eval_operand dst s = _` (irule_at (Pat `eval_operand _ _ = SOME (n2w d)`)) >>
  gvs[Excl "enc_def"]
QED

Theorem canonical_members_nonempty_advance[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty <> DecComplex T [] /\
  canonical_member_child ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ fn_has_code st mid fn /\ fn_has_code mid last fn /\
  abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites /\
  oid NOTIN sites /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. canonical_member_result ctx fn oid root extent sites b cap site limit_st
      st last (d+vo) tv v s t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
      tys tvs avs vs t /\
    entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t
Proof
  strip_tac >> drule_all canonical_members_navigation >> strip_tac >>
  qpat_x_assum `canonical_member_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [canonical_member_child_def]) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) fulltys) fullavs (LENGTH pretys)`, `d+vo`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by
    (drule abi_decode_member_setup_counters >> simp[]) >>
  `canonical_member_result ctx fn oid root extent sites b cap site limit_st
     st last (d+vo) tv v s t` by
    (irule canonical_member_result_prepend >> qexistsl_tac [`mid`, `u`] >> simp[]) >>
  qexists_tac `t` >> conj_tac >- gvs[Excl "enc_def"] >>
  qpat_assum `canonical_member_result _ _ _ _ _ _ _ _ _ _ st _ _ _ _ s t`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_member_result_def]) >>
  gvs[Excl "enc_def"] >> conj_tac
  >- (irule canonical_members_semantics_advance >>
      qpat_assum `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
      qpat_assum `entry_owned_region _ _ _ d _ s` (irule_at Any) >> simp[]) >>
  irule entry_owned_region_preserved >>
  qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
  qpat_assum `entry_owned_region _ _ _ d _ s` (irule_at Any) >> simp[]
QED

Theorem canonical_members_owned_child[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t ==>
  entry_owned_region oid root extent
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_size tv) t
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by
    fs[abi_decoder_members_def] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  gvs[entry_owned_region_def, MAP_APPEND, SUM_APPEND, Excl "enc_def"] >> decide_tac
QED

Theorem canonical_members_advance[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  canonical_member_child ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites /\
  oid NOTIN sites /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. canonical_member_result ctx fn oid root extent sites b cap site limit_st
      st last (d+vo) tv v s t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
      tys tvs avs vs t /\
    entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  Cases_on `type_to_abi_dec_info ce.ce_struct_fields ce ty = DecComplex T []`
  >- (fs[abi_decoder_needs_offset_iff, Excl "enc_def"] >>
      drule_all canonical_members_empty_advance >> strip_tac >>
      `entry_owned_region oid root extent
         (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_size tv) t` by
        (irule canonical_members_owned_child >>
         qpat_assum `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
      qexists_tac `t` >> gvs[canonical_member_result_def, abi_decoder_address_frame_def,
        Excl "enc_def"]) >>
  irule canonical_members_nonempty_advance >>
  qpat_assum `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `canonical_member_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[]
QED

Definition canonical_members_frame_def:
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d n st s <=>
    entry_scratch_ready sites b cap s /\ alloca_inv s /\
    abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
    entry_owned_region oid root extent d n s /\ fresh_vars_wrt limit_st s /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition canonical_members_effect_def:
  canonical_members_effect ctx fn sites d n st s t <=>
    entry_decode_path ctx fn s t /\ entry_loop_fields s t /\
    abi_encoder_registered_effect sites [(d,n)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
End

Theorem canonical_members_effect_refl[local]:
  canonical_members_effect ctx fn sites d n st s s
Proof
  simp[canonical_members_effect_def, entry_decode_path_refl,
    entry_loop_fields_def, abi_encoder_registered_effect_refl]
QED

Theorem canonical_members_effect_trans[local]:
  canonical_members_effect ctx fn sites d n st s u /\
  canonical_members_effect ctx fn sites d n mid u t /\
  st.cs_next_var <= mid.cs_next_var ==>
  canonical_members_effect ctx fn sites d n st s t
Proof
  simp_tac bool_ss [canonical_members_effect_def] >> strip_tac >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  `abi_encoder_registered_effect sites [(d,n)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `eval_operand op u = SOME w` by metis_tac[] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem canonical_members_step_frame[local]:
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d n st s /\
  canonical_member_result ctx fn oid root extent sites b cap site limit_st
    st last childd tv v s t /\
  entry_owned_region oid root extent d n t /\
  st.cs_next_var <= last.cs_next_var /\ d <= childd /\ childd+type_memory_size tv <= d+n ==>
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d n last t /\ canonical_members_effect ctx fn sites d n st s t
Proof
  simp_tac bool_ss [canonical_members_frame_def, canonical_member_result_def,
    canonical_members_effect_def] >> strip_tac >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_operand_live last.cs_next_var src /\
   abi_decoder_operand_live last.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_encoder_registered_effect sites [(d,n)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem canonical_members_child_bounds[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s ==>
  type_memory_size tv = type_memory_bytes ce ty /\
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_size tv <=
    d + SUM (MAP (type_memory_bytes ce) fulltys)
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by fs[abi_decoder_members_def] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"]
QED

Theorem canonical_members_interval_restrict[local]:
  first <= child_first /\ child_last <= last /\
  oid NOTIN abi_decoder_ids first last /\
  window_alloca_sites fn (abi_decoder_ids first last) SUBSET sites ==>
  oid NOTIN abi_decoder_ids child_first child_last /\
  window_alloca_sites fn (abi_decoder_ids child_first child_last) SUBSET sites
Proof
  strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids child_first child_last) SUBSET
    window_alloca_sites fn (abi_decoder_ids first last)` by
    (irule entry_decoder_sites_interval_subset >> simp[]) >>
  conj_tac >- (fs[abi_decoder_ids_def] >> decide_tac) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem canonical_members_cons_step[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  canonical_member_child ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce (ty::tys))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?mid t.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      (abi_decoder_member_infos ce.ce_struct_fields ce tys)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
      (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) mid = ((),last) /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) mid t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v]) tys tvs avs vs t /\
    canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) fulltys)) st s t /\
    st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
    mid.cs_next_id <= last.cs_next_id /\ fn_has_code mid last fn
Proof
  strip_tac >> drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `oid NOTIN abi_decoder_ids middle.cs_next_id end_st.cs_next_id /\
   window_alloca_sites fn (abi_decoder_ids middle.cs_next_id end_st.cs_next_id) SUBSET sites` by
    (irule canonical_members_interval_restrict >>
     qexistsl_tac [`st.cs_next_id`, `last.cs_next_id`] >> simp[]) >>
  `abi_decoder_code middle end_st` by (drule_all abi_decoder_to_buf_code >> simp[]) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `canonical_members_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_frame_def]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) canonical_members_advance >>
  disch_then (drule_at (Pat `abi_decode_member_setup _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule canonical_members_child_bounds >> strip_tac >>
  `canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) end_st t /\
   canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) fulltys)) st s t` by
    (irule canonical_members_step_frame >>
     qpat_assum `canonical_member_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     asm_rewrite_tac[] >> simp[]) >>
  qexistsl_tac [`end_st`, `t`] >> asm_rewrite_tac[] >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ end_st = _` mp_tac >>
  simp[MAP_APPEND, SUM_APPEND]
QED

Theorem canonical_members_suffix_lengths[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs tys tvs avs vs s ==>
  LENGTH tvs = LENGTH tys /\ LENGTH avs = LENGTH tys /\ LENGTH vs = LENGTH tys
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  drule_at (Pat `abi_decoder_members _ _ _ tys tvs avs vs`) abi_decoder_members_lengths >> simp[]
QED

Theorem canonical_members_semantics_complete[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs [] [] [] [] s ==>
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    fulltys fulltvs fullavs fullvs [] [] [] [] s
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  gvs[Excl "enc_def"]
QED

Theorem canonical_members_suffix[local]:
  !tys tvs avs vs pretys pretvs preavs prevs st last s.
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs tys tvs avs vs s /\
  (!i. i < LENGTH tys ==> canonical_member_child ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) fulltys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) last t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      fulltys fulltvs fullavs fullvs [] [] [] [] t
Proof
  Induct_on `tys` >> rpt gen_tac >> strip_tac
  >- (drule canonical_members_suffix_lengths >> simp[] >> strip_tac >> gvs[] >>
      fs[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def, comp_return_def] >>
      qexists_tac `s` >> gvs[canonical_members_effect_refl] >>
      drule canonical_members_semantics_complete >> simp[]) >>
  drule canonical_members_suffix_lengths >> strip_tac >>
  Cases_on `tvs` >- gvs[] >> Cases_on `avs` >- gvs[] >> Cases_on `vs` >- gvs[] >>
  `canonical_member_child ce env h h' h'' h''' ctx fn oid root extent sites b cap site limit_st` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all canonical_members_cons_step >> strip_tac >>
  `!i. i < LENGTH tys ==> canonical_member_child ce env
    (EL i tys) (EL i t) (EL i t') (EL i t'')
    ctx fn oid root extent sites b cap site limit_st` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH (h::tys) ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  `oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
   window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites` by
    (irule canonical_members_interval_restrict >>
     qexistsl_tac [`st.cs_next_id`, `last.cs_next_id`] >> simp[]) >>
  qpat_x_assum `!tvs avs vs pretys pretvs preavs prevs st last s. _`
    (drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  irule canonical_members_effect_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem entry_canonical_members_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> canonical_member_child ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0 st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory
Proof
  strip_tac >>
  `canonical_members_semantics ce env tys tvs avs vs sb d
     [] [] [] [] tys tvs avs vs s` by
    (irule canonical_members_semantics_initial >> simp[]) >>
  drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    canonical_members_suffix >>
  simp_tac bool_ss [MAP, SUM] >> disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  drule canonical_members_semantics_final >> simp[]
QED
