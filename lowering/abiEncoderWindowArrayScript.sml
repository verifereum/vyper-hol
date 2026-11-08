(* Actual-window array constructor assembly. *)
Theory abiEncoderWindowArray
Ancestors
  abiEncoderWindowArrayEntry abiEncoderWindowArrayRound abiEncoderWindowArrayFinish
  abiEncoderArrayContext abiEncoderArrayLoopCode abiEncoderWindowContract
  context abiEncoder abiEncoderProps fragExec compileEnv emitHelper venomInst list rich_list
  pred_set arithmetic

Theorem window_array_code_member:
  fn_has_code st en func /\
  MEM inst en.cs_current_insts ==>
  MEM inst (fn_insts func)
Proof
  simp_tac bool_ss [fn_has_code_def] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  fs[IS_PREFIX_APPEND] >> simp[]
QED

Theorem window_array_prefix_alloca_member:
  abi_encode_array_prefix src dst st = (ops,mid) /\
  fn_has_code st mid func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> irule window_array_code_member >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `abi_encode_array_prefix _ _ _ = _` mp_tac >>
  simp[abiEncoderArrayPhasesTheory.abi_encode_array_prefix_def,
    abiDecoderIndexInitTheory.abi_decode_index_init_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[]
QED

Theorem window_array_index_alloca_member:
  abi_decode_index_init st = (ip,owner) /\ fn_has_code st owner func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> irule window_array_code_member >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
  simp[abiDecoderIndexInitTheory.abi_decode_index_init_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[]
QED

Theorem window_array_dynamic_alloca_members:
  abi_encode_array_dynamic_init count_op asz st = (ptrs,owner) /\
  fn_has_code st owner func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (st.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (st.cs_next_var+1))]) (fn_insts func)
Proof
  strip_tac >> conj_tac >> irule window_array_code_member >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `abi_encode_array_dynamic_init _ _ _ = _` mp_tac >>
  simp[abiEncoderArrayCodeTheory.abi_encode_array_dynamic_init_def,
    abiDecoderIndexInitTheory.abi_decode_index_init_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[]
QED

Theorem window_array_loop_context:
  abi_encoder_admissible (AbiDynArray ei asz msz active) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op mid = (size_op,loop_end)
   else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op mid = (size_op,loop_end)) /\
  fn_has_code mid loop_end func ==>
  ?ip dp owner labels body_st idx body_end exit_st.
    (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
     else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
    abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
    (if active then abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
     else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
    (if active then abi_encode_array_dynamic_exit src dp exit_st
     else abi_encode_array_static_exit src asz exit_st) = (size_op,loop_end) /\
    fn_has_code mid owner func /\ fn_has_code exit_st loop_end func /\
    owner.cs_next_var = mid.cs_next_var + (if active then 3 else 1) /\
    owner.cs_next_id = mid.cs_next_id + (if active then 5 else 2) /\
    body_end.cs_next_var+4 = loop_end.cs_next_var /\
    body_end.cs_next_id+6 = loop_end.cs_next_id
Proof
  Cases_on `active` >> simp_tac bool_ss [] >> strip_tac
  >- (drule_all abi_encode_array_dynamic_loop_code >> strip_tac >>
      PairCases_on `ptrs` >>
      qexistsl_tac [`ptrs0`, `ptrs1`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
      fs[]) >>
  `abi_encoder_static_leaf ei` by
    fs[abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  qexistsl_tac [`ip`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_rewrite_tac[]
QED

Theorem window_array_body_sites:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id <= mid.cs_next_id /\
  owner.cs_next_id = mid.cs_next_id + (if active then 5 else 2) /\
  body_end.cs_next_id+6 = loop_end.cs_next_id /\
  loop_end.cs_next_id <= en.cs_next_id ==>
  window_alloca_sites func (frag_ids body_st body_end) SUBSET
    window_alloca_sites func (frag_ids st en) /\
  mid.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  mid.cs_next_id+2 NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end)
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  simp[window_alloca_sites_def, frag_ids_def, SUBSET_DEF] >>
  Cases_on `active` >> gvs[] >> rpt strip_tac >> decide_tac
QED

Theorem window_array_pre_root:
  abi_encoder_window_pre ctx func st en dst src (AbiDynArray ei asz msz active)
    at av sb cap d s ==>
  ?ty avs. at = Array NONE ty /\ av = ListV avs /\
    window_array_root ctx func st (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst sb cap d s
Proof
  strip_tac >>
  `?ty avs. at = Array NONE ty /\ av = ListV avs` by
    fs[abi_encoder_window_pre_def, abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  gvs[] >>
  simp_tac bool_ss [abiEncoderWindowArrayInvariantTheory.window_array_root_def] >>
  qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (simp[abiEncoderWindowArrayInvariantTheory.window_sizes32_def] >>
      metis_tac[window_pre_sites]) >>
  metis_tac[window_pre_sites]
QED

Theorem window_array_alloca_site:
  MEM (mk_inst id ALLOCA [Lit 32w] [v]) (fn_insts func) /\
  st.cs_next_id <= id /\ id < en.cs_next_id ==>
  id IN window_alloca_sites func (frag_ids st en)
Proof
  simp[window_alloca_sites_def, frag_ids_def] >> strip_tac >>
  qexists_tac `mk_inst id ALLOCA [Lit 32w] [v]` >> simp[mk_inst_def]
QED


Theorem window_array_constructor_entry:
  window_array_root ctx func st (window_alloca_sites func (frag_ids st en))
    ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  mid.cs_next_id = st.cs_next_id+4 /\
  owner.cs_next_id = mid.cs_next_id+(if active then 5 else 2) /\
  owner.cs_next_id <= en.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  mid.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  (active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en)) /\
  ?t pb bi bd.
    window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d,32)] s t /\
    window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst ip mid.cs_next_id bi dp
      (if active then mid.cs_next_id+2 else 0) bd count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    metis_tac[window_array_prefix_alloca_member] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
   (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func))` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule_all window_array_dynamic_alloca_members >> simp[]) >>
     drule_all window_array_index_alloca_member >> simp[]) >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (Cases_on `active` >> gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]` >>
     asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  `mid.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (Cases_on `active` >> gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst mid.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString mid.cs_next_var)]` >>
     asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  `(active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en))` by
    (strip_tac >>
     simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
       [STRING #"%" (toString (mid.cs_next_var+1))]` >>
     asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  drule_all window_array_entry_run >> strip_tac >> asm_rewrite_tac[] >>
  qexistsl_tac [`t`, `pb`, `bi`, `bd`] >> gvs[]
QED

Theorem window_array_inv_sites_subset:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s /\
  smaller SUBSET ids ==>
  window_array_inv ctx func owner smaller ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s
Proof
  simp_tac bool_ss [abiEncoderWindowArrayInvariantTheory.window_array_inv_def,
    abiEncoderWindowArrayInvariantTheory.window_array_root_def,
    abiEncoderWindowArrayInvariantTheory.window_sizes32_def] >>
  strip_tac >> asm_rewrite_tac[] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem window_array_completed_exit:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (out,en) /\
  fn_has_code exit_st en func ==>
  ?t. window_array_transition ctx func owner {} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
   abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
   alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = exit_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH exit_st.cs_current_insts` by
    (fs[abiEncoderWindowArrayInvariantTheory.window_array_inv_def,
        abiEncoderWindowArrayInvariantTheory.window_array_root_def] >>
     `s.vs_alloca_next < dimword (:256)` by
       metis_tac[exprLoweringPropsTheory.alloca_room_next_lt] >> decide_tac) >>
  `(active ==> eval_operand dp s = SOME (n2w dslot) /\ dslot < dimword (:256) /\
      (!x. dp = Var x ==> not_fresh_at exit_st x) /\
      mload dslot s = n2w (LENGTH avs * abi_member_head_size ty +
        SUM (MAP (abi_member_tail_size ty) avs)))` by
    (strip_tac >>
     fs[abiEncoderWindowArrayInvariantTheory.window_array_inv_def,
        abiEncoderWindowArrayInvariantTheory.window_array_cursor_def,
        venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all abiEncoderWindowArrayExitTheory.window_array_scalar_exit_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  metis_tac[abiEncoderWindowPhaseTheory.window_phase_control]
QED

Theorem window_array_loop_parent:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  window_strong_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  (active ==> dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
    dsite <> isite) /\ psite NOTIN ids /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d 0 s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t /\
    window_array_cursor T owner pp psite pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >>
  `0 <= LENGTH avs` by simp[] >>
  drule_all window_array_actual_control_loop >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_cursor_frame >>
  qexistsl_tac [`ids`, `ctx`, `func`,
    `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  fs[abiEncoderWindowArrayInvariantTheory.window_array_cursor_def,
     venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem window_array_exit_parent:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (size_op,mid) /\
  abi_encode_array_finish pp size_op mid = (out,en) /\
  fn_has_code exit_st mid func /\ fn_has_code mid en func ==>
  ?t. window_array_transition ctx func owner {psite} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> drule_all window_array_completed_exit >> strip_tac >>
  rename1 `window_array_transition ctx func owner {} [] s u` >>
  `window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`{}`, `ctx`, `func`, `[]`, `s`] >> asm_rewrite_tac[] >> simp[]) >>
  `exit_st.cs_next_var <= mid.cs_next_var` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule (cj 2 abi_encode_array_exit_shape) >> simp[]) >>
     drule (cj 1 abi_encode_array_exit_shape) >> simp[]) >>
  `!x. not_fresh_at owner x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `owner` >> asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand pp u = SOME (n2w pb) /\ pb < dimword (:256) /\
   mload pb u = 0w /\ FLOOKUP u.vs_allocas psite = SOME (pb,32) /\
   (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at mid x) /\
   alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted` by
    (fs[abiEncoderWindowArrayInvariantTheory.window_array_cursor_def,
        abiEncoderWindowArrayInvariantTheory.window_array_transition_def,
        venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >> metis_tac[]) >>
  drule_all window_array_parent_finish >> strip_tac >>
  suspend "finish"
QED

Resume window_array_exit_parent[finish]:
  `window_array_transition ctx func owner {psite} [] u t` by
    (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) u.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{psite}`, `[]`] >>
     `abi_encoder_registered_effect {psite} [] u t` by
       metis_tac[abiEncoderWindowArrayInvariantTheory.window_array_transition_effect] >>
     asm_rewrite_tac[EVERY_DEF, IN_SING] >>
     rpt strip_tac >>
     `FLOOKUP t.vs_allocas psite = SOME (pb,32)` by
       metis_tac[abiEncoderWindowArrayInvariantTheory.window_array_transition_effect,
         abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated] >>
     gvs[abiEncoderWindowArrayInvariantTheory.window_array_cursor_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule abiEncoderWindowArrayInvariantTheory.window_array_transition_trans >>
      qexists_tac `u` >> asm_rewrite_tac[] >>
      irule window_array_transition_enlarge >>
      qexistsl_tac [`{}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  metis_tac[abiEncoderWindowPhaseTheory.window_phase_control]
QED

Finalise window_array_exit_parent
Theorem window_array_loop_code_bounds:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels ==>
  owner.cs_next_id <= body_end.cs_next_id /\
  owner.cs_next_var <= exit_st.cs_next_var /\
  exit_st.cs_current_bb = SND (SND labels) /\ exit_st.cs_current_insts = []
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  asm_rewrite_tac[] >> decide_tac
QED


Theorem window_array_strong_contract:
  window_strong_contract ei ==>
  window_strong_contract (AbiDynArray ei asz msz active)
Proof
  strip_tac >> simp_tac bool_ss [window_strong_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule window_array_pre_root >> strip_tac >> gvs[] >>
  `fn_has_code st st' func /\ abi_encoder_admissible (AbiDynArray ei asz msz active)` by
    fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_array_context >> strip_tac >>
  drule_all window_array_loop_context >> strip_tac >>
  PairCases_on `ops` >>
  rename1 `abi_encode_array_prefix src dst st = ((pp,count_op),loop_st)` >>
  suspend "code"
QED

Resume window_array_strong_contract[code]:
  full_simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
  drule window_array_loop_code_bounds >> strip_tac >>
  `owner.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all window_array_constructor_entry >> strip_tac >>
  rename1 `window_array_transition ctx func st _ [(d,32)] s entry` >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids st st')` >>
  qabbrev_tac `loop_ids = ids DELETE st.cs_next_id` >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
   loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   loop_st.cs_next_id+2 NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end)` by
    (simp_tac bool_ss [Abbr `ids`] >> irule window_array_body_sites >>
     conj_tac >- decide_tac >>
     conj_tac >- (qexists_tac `loop_end` >> asm_rewrite_tac[] >> decide_tac) >>
     qexistsl_tac [`active`, `count_op`, `exit_st`, `ip`, `labels`, `owner`] >>
     asm_rewrite_tac[]) >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET loop_ids /\
   loop_st.cs_next_id IN loop_ids /\
   (active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) <>
       loop_st.cs_next_id) /\ st.cs_next_id NOTIN loop_ids /\ loop_ids SUBSET ids` by
    (simp_tac (srw_ss()) [Abbr `loop_ids`, SUBSET_DEF] >>
     rpt conj_tac >> rpt strip_tac >> gvs[] >>
     fs[SUBSET_DEF] >> metis_tac[]) >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op (FST labels) sb cap d 0 entry` by
    (irule window_array_inv_sites_subset >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  suspend "loop"
QED

Resume window_array_strong_contract[loop]:
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) NOTIN
    window_alloca_sites func (frag_ids body_st body_end))` by
    (Cases_on `active` >> gvs[]) >>
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) NOTIN
      window_alloca_sites func (frag_ids body_st body_end) /\
    (if active then loop_st.cs_next_id+2 else 0) <> loop_st.cs_next_id)` by
    metis_tac[] >>
  drule_all window_array_loop_parent >> strip_tac >>
  rename1 `window_array_transition ctx func owner loop_ids _ entry completed` >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op exit_st.cs_current_bb sb cap d (LENGTH avs) completed` by
    metis_tac[] >>
  drule_all window_array_exit_parent >> strip_tac >>
  suspend "package"
QED

Resume window_array_strong_contract[package]:
  `!x. not_fresh_at st x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st` >> asm_rewrite_tac[] >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] entry completed` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`loop_ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] completed t` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (`abi_encoder_window_input (AbiDynArray ei asz msz active)
       (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
       fs[abiEncoderWindowArrayInvariantTheory.window_array_root_def] >>
     drule abiEncoderWindowArrayLayoutTheory.window_array_layout >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s entry` by
    (irule window_array_transition_region >> qexistsl_tac [`ids`, `[(d,32)]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule abiEncoderWindowArrayInvariantTheory.window_array_transition_trans >>
     qexists_tac `entry` >> asm_rewrite_tac[] >>
     irule abiEncoderWindowArrayInvariantTheory.window_array_transition_trans >>
     qexists_tac `completed` >> asm_rewrite_tac[]) >>
  suspend "result"
QED

Resume window_array_strong_contract[result]:
  `window_sizes32 ids s` by
    fs[abiEncoderWindowArrayInvariantTheory.window_array_root_def] >>
  `window_sizes32 ids t` by
    (qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
     simp_tac bool_ss [abiEncoderWindowArrayInvariantTheory.window_array_transition_def] >>
     strip_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
  simp_tac bool_ss [abiEncoderWindowArrayInvariantTheory.window_array_transition_def] >>
  strip_tac >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >>
     simp_tac bool_ss [Abbr `ids`] >> irule window_alloca_sites_subset) >>
  qexists_tac `t` >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[abiEncoderExtendSimTheory.abi_encoder_extend_sim_sim] >>
  qpat_x_assum `window_sizes32 ids t` mp_tac >>
  simp_tac bool_ss [abiEncoderWindowArrayInvariantTheory.window_sizes32_def, Abbr `ids`] >>
  strip_tac >> asm_rewrite_tac[]
QED

Finalise window_array_strong_contract
