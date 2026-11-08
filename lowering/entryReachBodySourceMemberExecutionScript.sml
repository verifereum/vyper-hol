(* Source semantic advancement for the shared member execution engine. *)
Theory entryReachBodySourceMemberExecution
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySourceMemberCoreProbe entryReachBodyMemberExecutionCore
  entryReachBodySourceAggregateInputs entryReachBodySourceMemberEntry
  entryReachBodySourceProducer entryReachBodyCanonicalArrayChild
  entryReachBodyCanonicalMembers entryReachBodyOperationalPath abiDecoderDynamicLoopSetup
  entryReachBodyEmptyMember entryReachBodyScratchSites abiDecoderAllocation abiEncoderWindowContract
  entryReachBodyMemberPrefix entryReachBodyOwnedRegion
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect abiDecoderContract
  abiDecoderCoherence valueEncodingTyping valueEncoding list rich_list arithmetic pred_set
  entryReachBodyMemberSetup abiDecoderEmpty abiDecoderComplexHead abiDecoderOffset
  abiDecoderDynamic abiDecoderReentry abiEncoder compileEnv emitHelper

Theorem source_members_append[local]:
  !pre pt pa pv tys tvs avs vs.
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf tys tvs avs vs ==>
  entry_source_members ce env sf (pre++tys) (pt++tvs) (pa++avs) (pv++vs)
Proof
  Induct >> Cases_on `pt` >> Cases_on `pa` >> Cases_on `pv` >>
  simp[entry_source_members_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem source_members_wf[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  LIST_REL val_wf tvs vs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (irule (cj 1 value_has_type_val_wf) >> goal_assum (drule_at Any)) >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem source_member_prefix_extend[local]:
  entry_source_members ce env sf pre pt pa pv /\
  tuple_in_memory pv pt d s.vs_memory /\
  entry_owned_region oid root extent d outsz s /\
  SUM (MAP (type_memory_bytes ce) pre) <= outsz /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP (type_memory_bytes ce) pre),sz)] s t /\ alloca_inv t /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pre)) t.vs_memory ==>
  tuple_in_memory (pv++[v]) (pt++[tv]) d t.vs_memory
Proof
  strip_tac >>
  `LIST_REL val_wf pt pv` by metis_tac[source_members_wf] >>
  drule entry_source_members_lengths >> strip_tac >>
  drule entry_source_members_memory_sizes >> strip_tac >>
  irule entry_member_memory_extend >> metis_tac[]
QED

Theorem source_member_semantics_advance[local]:
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  tuple_in_memory pv pt d s.vs_memory /\
  entry_owned_region oid root extent d
    (SUM (MAP (type_memory_bytes ce) (pre++ty::tys))) s /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d+SUM (MAP (type_memory_bytes ce) pre),type_memory_size tv)] s t /\
  alloca_inv t /\ val_in_memory tv v
    (d+SUM (MAP (type_memory_bytes ce) pre)) t.vs_memory ==>
  entry_source_members ce env sf (pre++[ty]) (pt++[tv]) (pa++[av]) (pv++[v]) /\
  entry_source_members ce env sf tys tvs avs vs /\
  tuple_in_memory (pv++[v]) (pt++[tv]) d t.vs_memory
Proof
  strip_tac >>
  `entry_source_members ce env sf [ty] [tv] [av] [v] /\
   entry_source_members ce env sf tys tvs avs vs` by fs[entry_source_members_def] >>
  `entry_source_members ce env sf (pre++[ty]) (pt++[tv]) (pa++[av]) (pv++[v])` by
    (irule source_members_append >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> irule source_member_prefix_extend >>
  qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
  qpat_assum `entry_owned_region _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `entry_source_members _ _ _ pre _ _ _` (irule_at Any) >>
  simp[SUM_APPEND, MAP_APPEND]
QED

Theorem source_empty_member_endpoint[local]:
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv (DecComplex T []) av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (DecComplex T [])) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (DecComplex T []) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ val_in_memory tv v (d+vo) u.vs_memory /\
    type_memory_size tv = 0 /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = last.cs_current_bb /\ u.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  strip_tac >>
  `last = mid` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def, comp_return_def]) >>
  gvs[] >>
  drule_all entry_source_empty_descriptor_value >> strip_tac >>
  `~dec_info_needs_offset (DecComplex T [])` by simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.INST [`dyn` |-> `F`, `mid` |-> `last`, `ctx` |-> `ctx`]
    entry_member_setup_endpoint) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> qexists_tac `u` >> simp[]
QED

Theorem source_member_child_endpoint[local]:
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  ats = MAP (vyper_to_abi_type env) (pre++ty::tys) /\ vals = pa++av::avs /\
  off = abi_tuple_child_offset ats vals (LENGTH pre) /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre)) /\
  vo = SUM (MAP (type_memory_bytes ce) pre) /\
  outsz = SUM (MAP (type_memory_bytes ce) (pre++ty::tys)) /\
  ei = type_to_abi_dec_info sf ce ty /\
  dec_info_needs_offset ei = is_dynamic (vyper_to_abi_type env ty) /\
  mem_bytes_at sb (LENGTH (enc (Tuple ats) (ListV vals)))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple ats) (ListV vals) /\
  sb+LENGTH (enc (Tuple ats) (ListV vals)) < dimword (:256) /\
  d+outsz < dimword (:256) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset ei) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    ei mid = ((),next) /\
  entry_source_certified_child_producer cert ce env sf ty tv av v
    ctx fn oid root extent sites b cap site limit_st /\
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= next.cs_next_var /\
  next.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code st mid fn /\ fn_has_code mid next fn /\
  abi_decoder_code mid next /\ cert next /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id next.cs_next_id /\ oid NOTIN sites /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id next.cs_next_id) SUBSET sites ==>
  ?t. array_child_result ctx fn oid root extent sites
    (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id next.cs_next_id))
    b cap site limit_st st next (d+vo) tv v s t
Proof
  strip_tac >>
  qpat_assum `canonical_members_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_frame_def]) >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all entry_source_member_owned_entry >> strip_tac >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_source_members _ _ _ pre _ _ _` kall_tac >>
  qpat_x_assum `entry_source_members _ _ _ (ty::tys) _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` kall_tac >>
  qpat_x_assum `canonical_members_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qhdtm_x_assum `entry_source_certified_child_producer`
    (mp_tac o PURE_REWRITE_RULE [entry_source_certified_child_producer_def]) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t` >>
  qhdtm_x_assum `array_child_result`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  `abi_encoder_registered_effect
     (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id next.cs_next_id))
     [(d+vo,type_memory_size tv)] s u` by
    fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def,
       entry_loop_fields_def] >>
  `abi_encoder_registered_effect
     (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id next.cs_next_id))
     [(d+vo,type_memory_size tv)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  simp_tac bool_ss [array_child_result_def] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  `eval_operand op u = SOME w` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem source_empty_member_child_result[local]:
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv (DecComplex T []) av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\ vo <= outsz /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (DecComplex T [])) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (DecComplex T []) mid = ((),next) /\
  next.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st next fn ==>
  ?t. array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st next (d+vo) tv v s t
Proof
  strip_tac >>
  qhdtm_x_assum `canonical_members_frame`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_frame_def]) >>
  drule_all source_empty_member_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d outsz u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> simp[]) >>
  `entry_owned_region oid root extent (d+vo) (type_memory_size tv) u` by
    (fs[entry_owned_region_def] >> decide_tac) >>
  qexists_tac `u` >> simp_tac bool_ss [array_child_result_def] >> asm_rewrite_tac[] >>
  conj_tac
  >- fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def, entry_loop_fields_def] >>
  fs[abi_decoder_address_frame_def]
QED

Theorem source_member_cursor_advance[local]:
  fulltys = pre++ty::tys /\ fulltvs = pt++tv::tvs /\
  fullavs = pa++av::avs /\ fullvs = pv++v::vs /\
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs) /\
  tuple_in_memory pv pt d s.vs_memory /\
  entry_owned_region oid root extent d
    (SUM (MAP (type_memory_bytes ce) fulltys)) s /\ oid NOTIN ids /\
  array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st next (d+SUM (MAP (type_memory_bytes ce) pre)) tv v s t ==>
  entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d
    (pre++[ty]) tys next t
Proof
  strip_tac >>
  qhdtm_x_assum `array_child_result`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `entry_owned_region oid root extent d
     (SUM (MAP (type_memory_bytes ce) (pre++ty::tys))) s` by metis_tac[] >>
  drule_all source_member_semantics_advance >> strip_tac >>
  `abi_decode_source CALLDATALOAD t = abi_decode_source CALLDATALOAD s` by
    fs[entry_loop_fields_def, abi_decode_source_def] >>
  simp_tac bool_ss [entry_source_probe_cursor_def] >>
  qexistsl_tac [`pt++[tv]`, `pa++[av]`, `pv++[v]`, `tvs`, `avs`, `vs`] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >> asm_rewrite_tac[]
QED

Theorem source_indexed_member_producer[local]:
  entry_source_members ce env sf pre pt pa pv /\
  (!i. i < LENGTH (pre++ty::tys) ==>
    entry_source_certified_child_producer cert ce env sf
      (EL i (pre++ty::tys)) (EL i (pt++tv::tvs))
      (EL i (pa++av::avs)) (EL i (pv++v::vs))
      ctx fn oid root extent sites b cap site limit_st) ==>
  entry_source_certified_child_producer cert ce env sf ty tv av v
    ctx fn oid root extent sites b cap site limit_st
Proof
  strip_tac >> drule entry_source_members_lengths >> strip_tac >>
  first_x_assum (qspec_then `LENGTH pre` mp_tac) >>
  simp[EL_APPEND2] >>
  `LENGTH pt = LENGTH pa /\ LENGTH pv = LENGTH pa` by decide_tac >>
  ntac 3 (qpat_x_assum `LENGTH pre = _` kall_tac) >>
  simp[EL_APPEND2]
QED

Theorem entry_source_members_callback:
  (!i. i < LENGTH fulltys ==>
    entry_source_certified_child_producer cert ce env sf
      (EL i fulltys) (EL i fulltvs) (EL i fullavs) (EL i fullvs)
      ctx fn oid root extent sites b cap site limit_st) /\
  outsz = SUM (MAP (type_memory_bytes ce) fulltys) /\
  sb+LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d+outsz < dimword (:256) ==>
  entry_members_callback
    (entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d)
    cert sf ce ctx fn oid root extent sites b cap site limit_st dst src sb d outsz
Proof
  strip_tac >> simp_tac bool_ss [entry_members_callback_def] >> rpt gen_tac >> strip_tac >>
  drule source_probe_cursor_offsets >> strip_tac >>
  qhdtm_x_assum `entry_source_probe_cursor`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_source_probe_cursor_def]) >>
  Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  qpat_assum `entry_source_members _ _ _ (ty::tys) _ _ _`
    (mp_tac o PURE_REWRITE_RULE [entry_source_members_def]) >>
  simp_tac bool_ss [] >> strip_tac >>
  rename1 `entry_source_metadata ce env sf ty tv _ av v` >>
  `next.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= next.cs_next_var` by decide_tac >>
  `window_alloca_sites fn (abi_decoder_ids middle.cs_next_id next.cs_next_id) SUBSET
   window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` by
    (irule entry_decoder_sites_interval_subset >> decide_tac) >>
  `window_alloca_sites fn (abi_decoder_ids middle.cs_next_id next.cs_next_id) SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  `oid NOTIN abi_decoder_ids middle.cs_next_id next.cs_next_id` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  `SUM (MAP (type_memory_bytes ce) pre) + type_memory_size tv <= outsz` by
    (fs[entry_source_metadata_def] >>
     qpat_x_assum `outsz = _` mp_tac >> asm_rewrite_tac[] >> simp[MAP_APPEND, SUM_APPEND]) >>
  `?t. array_child_result ctx fn oid root extent sites
    (window_alloca_sites fn (abi_decoder_ids middle.cs_next_id next.cs_next_id))
    b cap site limit_st st next (d+SUM (MAP (type_memory_bytes ce) pre)) tv v s t` by
    suspend "child" >>
  rename1 `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ endpoint` >>
  qpat_x_assum `!i. _ ==> _` kall_tac >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  qhdtm_assum `canonical_members_frame`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_frame_def]) >>
  `entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d
     (pre++[ty]) tys next endpoint` by
    (irule source_member_cursor_advance >> goal_assum (drule_at Any) >> metis_tac[SUBSET_DEF]) >>
  qexists_tac `endpoint` >> (conj_tac >- first_assum ACCEPT_TAC) >>
  irule entry_members_resource_advance >>
  qhdtm_assum `canonical_members_frame` (irule_at Any) >>
  qhdtm_assum `array_child_result` (irule_at Any) >>
  qpat_x_assum `outsz = _` kall_tac >> asm_rewrite_tac[] >> decide_tac
QED

Resume entry_source_members_callback[child]:
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (qpat_x_assum `type_to_abi_dec_info _ _ _ = _`
        (fn th => rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
      irule source_empty_member_child_result >>
      qhdtm_assum `entry_source_metadata` (irule_at Any) >>
      qhdtm_assum `canonical_members_frame` (irule_at Any) >>
      qhdtm_assum `abi_decode_member_setup` (irule_at Any) >>
      qpat_x_assum `outsz = _` kall_tac >> asm_rewrite_tac[] >> decide_tac) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[entry_nonempty_member_offset] >>
  `entry_source_certified_child_producer cert ce env sf ty tv av v
     ctx fn oid root extent sites b cap site limit_st` by
    (qpat_x_assum `fulltys = _` SUBST_ALL_TAC >>
     qpat_x_assum `fulltvs = _` SUBST_ALL_TAC >>
     qpat_x_assum `fullavs = _` SUBST_ALL_TAC >>
     qpat_x_assum `fullvs = _` SUBST_ALL_TAC >>
     drule_all source_indexed_member_producer >> simp[]) >>
  irule source_member_child_endpoint >>
  qhdtm_assum `entry_source_certified_child_producer` (irule_at Any) >>
  qhdtm_assum `abi_decode_member_setup` (irule_at Any) >>
  qhdtm_assum `canonical_members_frame` (irule_at Any) >>
  qpat_assum `entry_source_members _ _ _ pre _ _ _` (irule_at Any) >>
  qpat_assum `entry_source_members _ _ _ (ty::tys) _ _ _` (irule_at Any) >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >>
  qpat_x_assum `fulltys = _` SUBST_ALL_TAC >>
  qpat_x_assum `fullavs = _` SUBST_ALL_TAC >> asm_rewrite_tac[]
QED

Finalise entry_source_members_callback

(* Conditional source endpoint: recursive child certification remains a premise. *)
Theorem entry_source_certified_members_endpoint:
  (!i. i < LENGTH tys ==>
    entry_source_certified_child_producer cert ce env sf
      (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
      ctx fn oid root extent sites b cap site limit_st) /\
  entry_source_members ce env sf tys tvs avs vs /\
  outsz = SUM (MAP (type_memory_bytes ce) tys) /\
  sb+LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d+outsz < dimword (:256) /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys) 0 0 st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
  oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. tuple_in_memory vs tvs d t.vs_memory /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz last t /\
    canonical_members_effect ctx fn sites d outsz st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,outsz)] s t
Proof
  strip_tac >> irule source_probe_execution >>
  `entry_members_callback
    (entry_source_probe_cursor ce env sf tys tvs avs vs sb d)
    cert sf ce ctx fn oid root extent sites b cap site limit_st dst src sb d outsz` by
    (irule entry_source_members_callback >> asm_rewrite_tac[]) >>
  `entry_source_probe_cursor ce env sf tys tvs avs vs sb d [] tys st s` by
    (simp_tac bool_ss [entry_source_probe_cursor_def] >>
     qexistsl_tac [`[]`, `[]`, `[]`, `tvs`, `avs`, `vs`] >>
     simp[entry_source_members_def, val_in_memory_def, Excl "enc_def"]) >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`avs`, `ce`, `cert`, `env`, `sf`, `tys`] >> asm_rewrite_tac[] >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED
