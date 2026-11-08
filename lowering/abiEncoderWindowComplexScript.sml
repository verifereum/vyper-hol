(* Checked diagnostic for the proof-internal typed member-entry interface. *)
Theory abiEncoderWindowComplex
Ancestors
  abiEncoderWindow abiEncoderInput abiEncoderMembersDefs contractABI
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers abiEncoderWindowContract
  abiEncoderWindowPhase abiEncoderRegisteredEffect allocaSiteResource
  exprLoweringProps venomMemDefs venomState finite_map pred_set compileEnv emitHelper
  valueEncoding valueEncodingProps abiCanonicalWindows abiDecodeRanges list rich_list arithmetic words

Theorem window_complex_empty_zero:
  abi_encoder_window_input (AbiComplex []) (Tuple []) (ListV []) sb 0 mem
Proof
  irule window_complex >> qexists_tac `[]` >>
  simp[abi_encoder_tuple_type_def]
QED

Theorem window_complex_replicate_span[local]:
  !n k. abi_encoder_member_span (TAKE k (REPLICATE n (AbiComplex [],0,0,F))) = 0
Proof
  Induct >> Cases_on `k` >>
  fs[abi_encoder_member_span_def, REPLICATE]
QED

Theorem window_complex_replicate_zero:
  abi_encoder_window_input
    (AbiComplex (REPLICATE n (AbiComplex [],0,0,F)))
    (Tuple (REPLICATE n (Tuple []))) (ListV (REPLICATE n (ListV []))) sb 0 mem
Proof
  irule window_complex >> qexists_tac `REPLICATE n (Tuple [])` >>
  simp[abi_encoder_tuple_type_def] >> rpt strip_tac >>
  gvs[EL_REPLICATE] >>
  simp[abi_member_head_size_def, is_dynamic_def, static_length_def,
    window_complex_empty_zero, window_complex_replicate_span]
QED

Theorem window_complex_nested_untyped:
  let n = dimword (:256);
      zs = REPLICATE n (AbiComplex [],0,0,F);
      ts = REPLICATE n (Tuple []);
      vs = REPLICATE n (ListV [])
  in
  abi_encoder_window_input
    (AbiComplex [(AbiComplex zs,abi_member_head_size (Tuple ts),0,is_dynamic (Tuple ts))])
    (Tuple [Tuple ts]) (ListV [ListV vs]) 0 0 mem /\
  ~has_types [Tuple ts] [ListV vs]
Proof
  simp_tac bool_ss [LET_THM] >> conj_tac
  >- (irule window_complex >> qexists_tac `[Tuple (REPLICATE (dimword (:256)) (Tuple []))]` >>
      simp[abi_encoder_tuple_type_def] >> rpt strip_tac >>
      simp[abi_encoder_member_span_def, window_complex_replicate_zero]) >>
  simp[has_type_def]
QED

(* Regression: the structural entry boundary accepts the untyped family. *)
Theorem window_complex_nested_structural:
  LIST_REL abi_encoder_structural_valid
    [Tuple (REPLICATE (dimword (:256)) (Tuple []))]
    [ListV (REPLICATE (dimword (:256)) (ListV []))]
Proof
  mp_tac window_complex_nested_untyped >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule window_complex_structural_members >>
  simp[abi_encoder_tuple_type_def]
QED

Theorem window_complex_singleton_bytes_structural:
  (ct = Bytes NONE \/ ct = String) /\ has_type ct (BytesV bs) /\
  LENGTH bs <= maxlen /\ 32+LENGTH bs < ms /\
  mem_word_at sb mem = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) mem = bs ==>
  LIST_REL abi_encoder_structural_valid [ct] [BytesV bs]
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abiEncoderWindowMembersTheory.window_member_singleton_actual_source >> strip_tac >>
  drule window_complex_structural_members >> simp[abi_encoder_tuple_type_def]
QED

(* The cursor may be reused: protection is derived from the root site precondition. *)
Theorem window_complex_cursor_protected:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  window_phase ctx func st mid {site} [] s t /\
  site IN window_alloca_sites func (frag_ids st en) /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) ==>
  slot < dimword (:256) /\
  regions_disjoint (sb,cap) (slot,32) /\
  regions_disjoint (d,LENGTH (enc at av)) (slot,32)
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `(!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `sb+cap <= s.vs_alloca_next /\ d+LENGTH (enc at av) <= s.vs_alloca_next` by
    fs[abi_encoder_window_pre_def] >>
  `!i b sz. i IN {site} /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
     regions_disjoint (sb,cap) (b,sz)` by
    (simp[] >> metis_tac[window_pre_sites]) >>
  `!i b sz. i IN {site} /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
     regions_disjoint (d,LENGTH (enc at av)) (b,sz)` by
    (simp[] >> metis_tac[window_pre_sites]) >>
  `regions_disjoint (sb,cap) (slot,32) /\
   regions_disjoint (d,LENGTH (enc at av)) (slot,32)` by
    (conj_tac >> irule window_alloca_growth_protected >>
     qexistsl_tac [`site`, `{site}`, `s`, `t`] >> simp[] >> metis_tac[]) >>
  `slot+32 <= t.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  simp[] >> decide_tac
QED

Theorem window_complex_emit_alloca_shape[local]:
  emit_op ALLOCA [Lit 32w] st = (dp,mid) ==>
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id = SUC st.cs_next_id /\
  ?x. dp = Var x /\ not_fresh_at mid x
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def]
QED

Theorem window_complex_allocate_cursor:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  emit_op ALLOCA [Lit 32w] st = (dp,mid) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) ==>
  ?t slot. window_phase ctx func st mid {st.cs_next_id} [] s t /\
    abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
      (ListV avs) sb cap d t /\
    window_member_cursor infos dp st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) mid t
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  drule_all window_emit_alloca32_phase >> strip_tac >>
  drule window_complex_emit_alloca_shape >> strip_tac >>
  `b < dimword (:256) /\ regions_disjoint (sb,cap) (b,32) /\
   regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,32)` by
    metis_tac[window_complex_cursor_protected] >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids mid en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
     (ListV avs) sb cap d t` by
    (irule window_member_remaining_pre >>
     asm_rewrite_tac[] >>
     (conj_tac >- fs[abi_encoder_window_pre_def]) >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `s`, `st`] >>
     simp[]) >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp[window_member_cursor_def] >> metis_tac[]
QED

Theorem window_complex_initialize_store:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  window_member_cursor infos dp site slot sb cap d
    (LENGTH (enc at (ListV avs))) st s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  emit_void MSTORE [dp; Lit (n2w (window_member_head_size infos))] st = ((),ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func ==>
  ?u. window_phase ctx func st ready {site} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos dp site slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)
Proof
  strip_tac >>
  `eval_operand dp s = SOME (n2w slot) /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
   slot < dimword (:256) /\ regions_disjoint (sb,cap) (slot,32)` by
    fs[window_member_cursor_def] >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `window_phase ctx func st ready {site} [] s
     ((mstore slot (n2w (window_member_head_size infos)) s) with
       vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >>
     qexistsl_tac [`dp`, `Lit (n2w (window_member_head_size infos))`] >>
     simp[eval_operand_def]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st ready {site} [] s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `DISJOINT {site} (window_alloca_sites func (frag_ids ready en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap u.vs_memory` by
    (irule window_alloca_growth_source >> qexistsl_tac [`{site}`, `[]`, `s`] >>
     simp[] >>
     `abi_encoder_registered_effect {site} [] s u /\ window_alloca_growth s u` by
       metis_tac[window_phase_effect, window_phase_resources] >>
     asm_rewrite_tac[] >>
     fs[abi_encoder_window_pre_def]) >>
  `eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     qexistsl_tac [`{site}`, `[]`, `s`, `st`] >> simp[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_member_cursor_phase >>
      qexistsl_tac [`ctx`, `func`, `{site}`, `[]`, `s`, `st`] >> simp[]) >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem window_complex_initialize_phase_core[local]:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en)
Proof
  strip_tac >>
  `cs_extends ready en` by fs[ci_mono_def] >>
  `emit_op ALLOCA [Lit 32w] st = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  `ci_mono st mid /\ ci_mono mid ready` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends st mid /\ cs_extends mid ready` by fs[ci_mono_def] >>
  `fn_has_code st mid func /\ fn_has_code mid ready func /\ fn_has_code ready en func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `fn_has_code st mid func` mp_tac >>
     simp_tac bool_ss [fragExecTheory.fn_has_code_def] >> strip_tac >>
     gvs[IS_PREFIX_APPEND] >>
     irule fragExecTheory.lookup_block_fn_insts >>
     goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `fn_has_code mid en func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (drule window_complex_emit_alloca_shape >> strip_tac >>
     `st.cs_next_id < en.cs_next_id` by
       (fs[ci_mono_def] >> decide_tac) >>
     simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
  drule_all window_complex_allocate_cursor >> strip_tac >>
  drule_all window_complex_initialize_store >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >>
  irule window_phase_chain >>
  qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >>
  simp[] >> metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND]
QED

Theorem window_complex_initialize_phase:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)
Proof
  strip_tac >> drule_all window_complex_initialize_phase_core >> metis_tac[]
QED

(* Reverse phase packaging: byte/value facts and site sizes are explicit. *)
Theorem window_complex_phase_result:
  window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t /\
  mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
  window_strong_result ctx func st en out at av d s t
Proof
  simp_tac bool_ss [window_phase_def, window_strong_result_def,
    abi_encoder_window_result_def] >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
        `[(d,LENGTH (enc at av))]`] >> simp[window_alloca_sites_subset]) >>
  metis_tac[abiEncoderExtendSimTheory.abi_encoder_extend_sim_sim]
QED

Theorem window_complex_finish_load:
  window_phase ctx func st load ids [(d,LENGTH (enc at av))] s u /\
  ids SUBSET window_alloca_sites func (frag_ids st en) /\
  st.cs_next_var <= load.cs_next_var /\
  mem_bytes_at d (LENGTH (enc at av)) u.vs_memory = enc at av /\
  eval_operand dp u = SOME (n2w slot) /\ slot < dimword (:256) /\
  mem_word_at slot u.vs_memory = n2w (LENGTH (enc at av)) /\
  emit_op MLOAD [dp] load = (out,en) /\ fn_has_code load en func /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
  ?t. window_strong_result ctx func st en out at av d s t
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule_all window_cursor_load_phase >> strip_tac >>
  `abi_encoder_registered_effect {} [] u t` by metis_tac[window_phase_effect] >>
  `mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av` by
    (irule EQ_TRANS >> qexists_tac `mem_bytes_at d (LENGTH (enc at av)) u.vs_memory` >>
     conj_tac
     >- (irule abi_encoder_window_effect_bytes >>
         qexistsl_tac [`{}`, `[]`] >> simp[]) >>
     asm_rewrite_tac[]) >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_x_assum `abi_encoder_registered_effect {} [] u t` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >>
     simp[] >> metis_tac[]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc at av))]`, `load`, `{}`, `[]`, `u`] >>
     asm_rewrite_tac[EVERY_DEF, EMPTY_SUBSET]) >>
  qexists_tac `t` >> irule window_complex_phase_result >> asm_rewrite_tac[] >>
  qpat_x_assum `mem_word_at slot _ = _` mp_tac >>
  asm_rewrite_tac[mem_word_at_eq_mload] >> disch_then SUBST1_TAC >> REFL_TAC
QED

Theorem window_complex_initialize_phase_sizes:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >> drule_all window_complex_initialize_phase_core >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     strip_tac >> rpt gen_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule window_phase_effect >> strip_tac >>
  drule window_registered_sizes_transport >>
  disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]
QED

Theorem window_complex_strong_contract:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> window_strong_contract ei) ==>
  window_strong_contract (AbiComplex infos)
Proof
  strip_tac >> simp_tac bool_ss [window_strong_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `abi_encoder_window_input (AbiComplex infos) at av sb cap s.vs_memory` by
    fs[abi_encoder_window_pre_def] >>
  `?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> metis_tac[]) >>
  gvs[] >> Cases_on `infos`
  >- suspend "empty" >>
  rename1 `h::rest` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) (h::rest)`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume window_complex_strong_contract[empty]:
  gvs[Once abiEncoderTheory.compile_abi_encode_child_def, comp_return_def] >>
  `enc at (ListV avs) = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> strip_tac >>
     gvs[abi_encoder_tuple_type_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, LENGTH, mem_bytes_at_def, eval_operand_def] >>
  metis_tac[window_pre_sites, window_phase_refl, abi_encoder_window_pre_def]
QED
Resume window_complex_strong_contract[dynamic]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocated)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))] allocated` >>
  rename1 `emit_void MSTORE _ allocated = (unit,ready)` >> Cases_on `unit` >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 buf.buf_operand ready` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,load)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >>
  fs[LET_THM] >>
  gvs[pairTheory.UNCURRY_DEF] >>
  `ci_mono ready load /\ ci_mono load st'` by
    metis_tac[cj 3 ci_mono_compile_abi_encode, ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono ready st'` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all window_complex_initialize_phase_sizes >> strip_tac >>
  `abi_encoder_window_pre ctx func ready load dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by
    (qpat_assum `abi_encoder_window_pre _ _ ready st' _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     asm_rewrite_tac[] >>
     `cs_extends ready load /\ cs_extends load st' /\ load.cs_next_id <= st'.cs_next_id` by
       (qpat_assum `ci_mono ready load` mp_tac >>
        qpat_assum `ci_mono load st'` mp_tac >>
        simp_tac bool_ss [ci_mono_def] >> metis_tac[]) >>
     (conj_tac >- metis_tac[fragExecTheory.fn_has_code_split]) >>
     rpt gen_tac >> strip_tac >>
     `inst.inst_id IN frag_ids ready st'` by
       (qpat_x_assum `inst.inst_id IN frag_ids ready load` mp_tac >>
        simp_tac (srw_ss()) [NoAsms, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
     qpat_x_assum `!inst b sz. _` drule_all >> simp_tac bool_ss []) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
     mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)` by asm_rewrite_tac[] >>
  drule_all window_complex_initialized_run_sizes >> strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (`!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
        FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by metis_tac[window_pre_sites] >>
     qpat_x_assum `!R. _ ==> !i b sz. _ /\ FLOOKUP u.vs_allocas i = _ ==> _`
       (qspec_then `window_alloca_sites func (frag_ids st st')` mp_tac) >>
     asm_rewrite_tac[] >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `window_alloca_sites func (frag_ids st st')` mp_tac) >>
     asm_rewrite_tac[]) >>
  rpt (qpat_x_assum `!R. (!i b sz. _) ==> _` kall_tac) >>
  `ready.cs_next_var <= load.cs_next_var /\ ready.cs_next_id <= load.cs_next_id` by
    (qpat_assum `ci_mono ready load` mp_tac >> simp_tac bool_ss [ci_mono_def] >> metis_tac[]) >>
  `window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
     (LENGTH (enc at (ListV avs))) load t` by
    (irule window_member_cursor_phase >> goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `eval_operand buf.buf_operand t = SOME (n2w slot) /\ slot < dimword (:256)` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ load t` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `ci_mono st allocated /\ ci_mono allocated ready` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, pairTheory.SND] >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
   load.cs_next_id <= st'.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `window_alloca_sites func (frag_ids ready load) SUBSET
   window_alloca_sites func (frag_ids st st')` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def, SUBSET_DEF,
       abiEncoderPropsTheory.frag_ids_def] >> rpt strip_tac >>
     decide_tac) >>
  qpat_x_assum `window_phase _ _ ready load _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `window_phase ctx func st load (window_alloca_sites func (frag_ids st st'))
    [(d,LENGTH (enc at (ListV avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready load) UNION {st.cs_next_id}`,
       `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
     asm_rewrite_tac[] >> simp[EVERY_DEF, UNION_SUBSET, INSERT_SUBSET]) >>
  irule window_complex_finish_load >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[SUBSET_REFL] >>
  `fn_has_code load st' func` by
    (qpat_assum `ci_mono ready load` mp_tac >>
     qpat_assum `ci_mono load st'` mp_tac >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
     `fn_has_code ready st' func` by
       metis_tac[abi_encoder_window_pre_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  qexistsl_tac [`buf.buf_operand`, `slot`] >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >> metis_tac[]
QED
Resume window_complex_strong_contract[static]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,en)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >> gvs[] >>
  `~EXISTS (\(_,_,_,dyn). dyn) infos` by
    (qpat_assum `EVERY _ infos` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `window_member_cursor infos (Lit 0w) 0 0 sb cap d
      (LENGTH (enc at (ListV avs))) st s` by simp[window_member_cursor_def] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at 0 s.vs_memory = n2w (window_member_head_size infos)` by simp[] >>
  drule_all window_complex_initialized_run_sizes >> strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (`!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by metis_tac[window_pre_sites] >>
     qpat_x_assum `!R. (!i b sz. _) ==> _`
       (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `!R. (!i b sz. _) ==> _` kall_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_dynamic_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    metis_tac[window_complex_structural_members, abiEncoderOpenInputTheory.abi_encoder_structural_list_layout] >>
  `SUM (MAP2 abi_member_tail_size ats avs) = 0` by
    (`!ts vs. ~any_dynamic ts /\ LENGTH ts = LENGTH vs ==>
       SUM (MAP2 abi_member_tail_size ts vs) = 0` suffices_by metis_tac[] >>
     Induct >> Cases_on `vs` >> simp[is_dynamic_def, abi_member_tail_size_def]) >>
  `LENGTH (enc at (ListV avs)) = window_member_head_size infos` by
    (`enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
       (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
     drule abiEncoderOpenInputTheory.abi_encoder_open_tuple_length >>
     asm_rewrite_tac[] >> simp_tac bool_ss [head_lengths_acc] >> decide_tac) >>
  `~any_dynamic ats` by metis_tac[] >>
  qexists_tac `t` >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >>
  simp[eval_operand_def] >>
  qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac[] >> simp_tac (srw_ss()) [UNION_EMPTY]
QED
Finalise window_complex_strong_contract
