(* Owner and narrow-effect transport for concrete actual-window array rounds. *)
Theory abiEncoderWindowArrayRound
Ancestors
  abiEncoderWindowArrayLoop abiEncoderWindowArrayBody
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout abiEncoderRegisteredEffect
  abiEncoderArrayLoopCode abiEncoderArrayBodyCode abiEncoderWindowContract
  compileEnv freshWrites venomState finite_map pred_set list arithmetic

Theorem window_array_root_owner_mono:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  (!x. not_fresh_at owner x ==> not_fresh_at later x) ==>
  window_array_root ctx func later ids ei asz msz active ty avs src dst sb cap d s
Proof
  simp_tac bool_ss [window_array_root_def] >> strip_tac >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_cursor_owner_mono:
  window_array_cursor enabled owner op site slot value sb cap d n s /\
  (!x. not_fresh_at owner x ==> not_fresh_at later x) ==>
  window_array_cursor enabled later op site slot value sb cap d n s
Proof
  simp_tac bool_ss [window_array_cursor_def] >> metis_tac[]
QED

Theorem window_array_transition_owner_weaken:
  window_array_transition ctx func later ids outs s t /\
  (!x. not_fresh_at owner x ==> not_fresh_at later x) ==>
  window_array_transition ctx func owner ids outs s t
Proof
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_transition_enlarge:
  window_array_transition ctx func owner child_ids outs s t /\
  child_ids SUBSET ids /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) more ==>
       EVERY (\(b,n). a < b \/ b+n <= a) outs) ==>
  window_array_transition ctx func owner ids more s t
Proof
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_encoder_registered_effect_enlarge >> metis_tac[]
QED

Theorem window_array_transition_region:
  window_array_transition ctx func owner child_ids outs s t /\
  child_ids SUBSET ids /\
  EVERY (\(b,n). d <= b /\ b+n <= d+len) outs ==>
  window_array_transition ctx func owner ids [(d,len)] s t
Proof
  strip_tac >> irule window_array_transition_enlarge >>
  goal_assum (drule_at Any) >> qexists_tac `outs` >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> fs[EVERY_MEM] >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem window_array_cursor_word:
  window_array_cursor enabled owner op site slot value sb cap d n s /\
  window_array_transition ctx func owner child_ids outs s t /\
  (enabled ==> mem_word_at slot t.vs_memory = n2w new_value) ==>
  window_array_cursor enabled owner op site slot new_value sb cap d n t
Proof
  reverse (Cases_on `enabled`) >- simp[window_array_cursor_def] >>
  simp_tac bool_ss [window_array_cursor_def] >> strip_tac >>
  `eval_operand op t = SOME (n2w slot)` by
    (irule window_array_transition_eval >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas site = SOME (slot,32)` by
    metis_tac[abi_encoder_registered_effect_allocated, window_array_transition_effect] >>
  asm_rewrite_tac[]
QED

Theorem window_array_cursor_frame:
  window_array_cursor enabled owner op site slot value sb cap d n s /\
  window_array_transition ctx func owner child_ids outs s t /\
  (enabled ==> site NOTIN child_ids /\
    EVERY (\r. venomMemDefs$regions_disjoint (slot,32) r) outs) ==>
  window_array_cursor enabled owner op site slot value sb cap d n t
Proof
  strip_tac >> irule window_array_cursor_word >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  strip_tac >>
  `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
    (irule window_array_transition_cursor_frame >>
     fs[window_array_cursor_def] >> metis_tac[]) >>
  fs[window_array_cursor_def]
QED

Theorem window_array_static_round:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  window_strong_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz F ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz F ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t
Proof
  strip_tac >>
  `!x. not_fresh_at owner x ==> not_fresh_at body_st x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `owner` >>
     fs[abi_encoder_array_loop_code_def]) >>
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
   abi_encoder_array_prefix ty avs k d s.vs_memory /\
   window_array_cursor T owner ip isite islot k sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
   (!x. count_op = Var x ==> not_fresh_at owner x) /\
   eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
   ~s.vs_halted /\ s.vs_current_bb = body_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH body_st.cs_current_insts` by
    fs[window_array_inv_def, abi_encoder_array_loop_code_def] >>
  `window_array_root ctx func body_st ids ei asz msz F ty avs src dst sb cap d s` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `?u. window_array_transition ctx func body_st
      (window_alloca_sites func (frag_ids body_st body_end))
      [(d+32+k*asz,LENGTH (enc ty (EL k avs)))] s u /\
    abi_encoder_array_prefix ty avs (SUC k) d u.vs_memory /\
    eval_operand idx u = SOME (n2w k) /\
    u.vs_current_bb = body_end.cs_current_bb /\
    u.vs_inst_idx = LENGTH body_end.cs_current_insts` by
    (`eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
      mload islot s = n2w k /\ fn_has_code body_st body_end func` by
       fs[window_array_cursor_def, abi_encoder_array_loop_code_def,
         venomStateTheory.mload_def, valueEncodingTheory.mem_word_at_def] >>
     drule_all window_array_static_body_run >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume window_array_static_round[finish]:
  `window_array_transition ctx func owner
    (window_alloca_sites func (frag_ids body_st body_end))
    [(d+32+k*asz,LENGTH (enc ty (EL k avs)))] s u` by
    (irule window_array_transition_owner_weaken >> metis_tac[]) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz F)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty /\
   LENGTH avs < dimword (:256)` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff, contractABITheory.valid_length_def] >>
  `d <= d+32+k*asz /\ d+32+k*asz+LENGTH (enc ty (EL k avs)) <=
     d+LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule_all window_array_prefix_step_geometry >>
     drule window_array_layout >> simp[] >> decide_tac) >>
  suspend "framing"
QED

Resume window_array_static_round[framing]:
  `window_array_cursor T owner ip isite islot k sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`window_alloca_sites func (frag_ids body_st body_end)`,
       `ctx`, `func`,
       `[(d+32+k*asz,LENGTH (enc ty (EL k avs)))]`, `s`] >>
     asm_rewrite_tac[] >>
     simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     qpat_x_assum `window_array_cursor T _ _ _ _ _ _ _ _ _ s` mp_tac >>
     simp_tac bool_ss [window_array_cursor_def] >> strip_tac >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (islot,32)` mp_tac >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >>
     qpat_x_assum `asz = _` SUBST_ALL_TAC >> decide_tac) >>
  `window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_transition_region >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     asm_rewrite_tac[]) >>
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d u` by
    (irule window_array_root_transition >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
     simp_tac bool_ss [EVERY_DEF] >>
     full_simp_tac bool_ss [window_array_root_def] >>
     asm_rewrite_tac[SUBSET_REFL]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >>
  suspend "backedge"
QED

Resume window_array_static_round[backedge]:
  drule abiEncoderArrayRoundTheory.abi_encode_array_static_body_index >> disch_tac >>
  `!x. not_fresh_at owner x ==>
    x <> STRING #"%" (toString body_end.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def, abi_encoder_array_loop_code_def] >>
     first_x_assum (qspec_then `body_end.cs_next_var` mp_tac) >> simp[]) >>
  `ip <> Var (STRING #"%" (toString body_end.cs_next_var))` by
    (fs[window_array_cursor_def] >> metis_tac[]) >>
  `?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
     qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
     qexists_tac `header_bb` >> asm_rewrite_tac[] >>
     simp[Abbr `header_bb`, abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
       venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]) >>
  suspend "execute"
QED

Resume window_array_static_round[execute]:
  qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
  qabbrev_tac `t = jump_to (FST labels)
    (mstore islot (n2w (SUC k)) (update_var nv (n2w (SUC k)) u))` >>
  `window_array_transition ctx func owner {isite} [] u t` by
    (`islot < dimword (:256)` by fs[window_array_cursor_def] >>
     `window_array_transition ctx func owner {isite} [] u
       (jump_to (FST labels) (mstore (w2n (n2w islot : bytes32)) (n2w (SUC k))
         (update_var nv (n2w (SUC k)) u)))` suffices_by
       simp[Abbr `t`] >>
     irule window_array_backedge_run >>
     asm_rewrite_tac[] >> rpt conj_tac
     >- fs[window_array_transition_def]
     >- fs[window_array_transition_def]
     >- (qexists_tac `LENGTH avs` >> asm_rewrite_tac[])
     >- (qexists_tac `hdr_bb` >> asm_rewrite_tac[])
     >- (qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
         qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb _ = SOME back_bb` >>
         qexistsl_tac [`back_bb`, `body_end.cs_next_id`, `ip`,
           `STRING #"%" (toString body_st.cs_next_var)`, `body_end.cs_current_insts`] >>
         simp[Abbr `back_bb`, Abbr `nv`] >> fs[window_array_cursor_def])
     >- (qexists_tac `isite` >> fs[window_array_cursor_def]) >>
     fs[window_array_transition_def]) >>
  suspend "compose"
QED

Resume window_array_static_round[compose]:
  `window_array_inv ctx func owner ids ei asz msz F ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (qpat_assum `window_array_transition _ _ _ {isite} [] u t` mp_tac >>
     simp_tac bool_ss [Abbr `t`] >> strip_tac >>
     irule window_array_backedge_inv >> asm_rewrite_tac[] >>
     simp[window_array_cursor_def]) >>
  `window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t` by
    (irule window_array_transition_region >>
     qexistsl_tac [`{isite}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_transition_trans >> qexists_tac `u` >> asm_rewrite_tac[]
QED

Finalise window_array_static_round


Theorem window_array_dynamic_round:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end) /\
  window_strong_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite <> isite /\ k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz T ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t
Proof
  strip_tac >>
  `!x. not_fresh_at owner x ==> not_fresh_at body_st x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `owner` >>
     fs[abi_encoder_array_loop_code_def]) >>
  qabbrev_tac `off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE k avs))` >>
  `window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d s /\
   abi_encoder_array_prefix ty avs k d s.vs_memory /\
   window_array_cursor T owner ip isite islot k sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
   window_array_cursor T owner dp dsite dslot off sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
   (!x. count_op = Var x ==> not_fresh_at owner x) /\
   eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
   ~s.vs_halted /\ s.vs_current_bb = body_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH body_st.cs_current_insts` by
    fs[window_array_inv_def, abi_encoder_array_loop_code_def, Abbr `off`] >>
  `window_array_root ctx func body_st ids ei asz msz T ty avs src dst sb cap d s` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `window_array_cursor T body_st dp dsite dslot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s` by
    (irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `?u. window_array_transition ctx func body_st
      (window_alloca_sites func (frag_ids body_st body_end) UNION {dsite})
      [(d+32+k*abi_member_head_size ty,32);
       (d+32+off,LENGTH (enc ty (EL k avs)))] s u /\
    abi_encoder_array_prefix ty avs (SUC k) d u.vs_memory /\
    mem_word_at dslot u.vs_memory = n2w (off+LENGTH (enc ty (EL k avs))) /\
    eval_operand idx u = SOME (n2w k) /\
    u.vs_current_bb = body_end.cs_current_bb /\
    u.vs_inst_idx = LENGTH body_end.cs_current_insts` by
    (`eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
      mload islot s = n2w k /\ fn_has_code body_st body_end func` by
       fs[window_array_cursor_def, abi_encoder_array_loop_code_def,
         venomStateTheory.mload_def, valueEncodingTheory.mem_word_at_def] >>
     `off = LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) (TAKE k avs))` by simp[Abbr `off`] >>
     drule_all window_array_dynamic_body_run >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "dynamic_frame"
QED

Resume window_array_dynamic_round[dynamic_frame]:
  `window_array_transition ctx func owner
    (window_alloca_sites func (frag_ids body_st body_end) UNION {dsite})
    [(d+32+k*abi_member_head_size ty,32);
     (d+32+off,LENGTH (enc ty (EL k avs)))] s u` by
    (irule window_array_transition_owner_weaken >> metis_tac[]) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ is_dynamic ty /\
   LENGTH avs < dimword (:256)` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff, contractABITheory.valid_length_def] >>
  `32+off+LENGTH (enc ty (EL k avs)) <=
     LENGTH (enc (Array NONE ty) (ListV avs)) /\
   k*abi_member_head_size ty+32 <= off` by
    (drule_all window_array_prefix_step_geometry >>
     asm_simp_tac bool_ss [Abbr `off`] >> strip_tac >> decide_tac) >>
  `isite <> dsite` by metis_tac[] >>
  `window_array_cursor T owner ip isite islot k sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`window_alloca_sites func (frag_ids body_st body_end) UNION {dsite}`,
       `ctx`, `func`,
       `[(d+32+k*abi_member_head_size ty,32);
         (d+32+off,LENGTH (enc ty (EL k avs)))]`, `s`] >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [IN_UNION, IN_SING, EVERY_DEF] >>
     qpat_x_assum `window_array_cursor T _ ip _ _ _ _ _ _ _ s` mp_tac >>
     simp_tac bool_ss [window_array_cursor_def] >> strip_tac >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (islot,32)` mp_tac >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >>
     asm_rewrite_tac[] >> decide_tac) >>
  suspend "dynamic_cursor"
QED

Resume window_array_dynamic_round[dynamic_cursor]:
  `off + LENGTH (enc ty (EL k avs)) =
    LENGTH avs * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))` by
    (`TAKE (SUC k) avs = TAKE k avs ++ [EL k avs]` by
       simp[rich_listTheory.TAKE_SUC, TAKE1_DROP] >>
     asm_simp_tac bool_ss [Abbr `off`, MAP_APPEND, MAP, SUM_APPEND, SUM,
       abiDecodeRangesTheory.abi_member_tail_size_def, ADD_ASSOC, ADD_CLAUSES]) >>
  `window_array_cursor T owner dp dsite dslot
      (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_word >> conj_tac
     >- asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_transition_region >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [EVERY_DEF] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     conj_tac >- decide_tac >> simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]) >>
  `window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d u` by
    (irule window_array_root_transition >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
     simp_tac bool_ss [EVERY_DEF] >>
     full_simp_tac bool_ss [window_array_root_def] >>
     asm_rewrite_tac[SUBSET_REFL]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >>
  suspend "dynamic_backedge"
QED

Resume window_array_dynamic_round[dynamic_backedge]:
  drule abiEncoderArrayRoundTheory.abi_encode_array_dynamic_body_index >> disch_tac >>
  `!x. not_fresh_at owner x ==>
    x <> STRING #"%" (toString body_end.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def, abi_encoder_array_loop_code_def] >>
     first_x_assum (qspec_then `body_end.cs_next_var` mp_tac) >> simp[]) >>
  `ip <> Var (STRING #"%" (toString body_end.cs_next_var))` by
    (fs[window_array_cursor_def] >> metis_tac[]) >>
  `?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
     qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
     qexists_tac `header_bb` >> asm_rewrite_tac[] >>
     simp[Abbr `header_bb`, abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
       venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]) >>
  suspend "dynamic_execute"
QED

Resume window_array_dynamic_round[dynamic_execute]:
  qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
  qabbrev_tac `t = jump_to (FST labels)
    (mstore islot (n2w (SUC k)) (update_var nv (n2w (SUC k)) u))` >>
  `window_array_transition ctx func owner {isite} [] u t` by
    (`islot < dimword (:256)` by fs[window_array_cursor_def] >>
     `window_array_transition ctx func owner {isite} [] u
       (jump_to (FST labels) (mstore (w2n (n2w islot : bytes32)) (n2w (SUC k))
         (update_var nv (n2w (SUC k)) u)))` suffices_by
       simp[Abbr `t`] >>
     irule window_array_backedge_run >>
     asm_rewrite_tac[] >> rpt conj_tac
     >- fs[window_array_transition_def]
     >- fs[window_array_transition_def]
     >- (qexists_tac `LENGTH avs` >> asm_rewrite_tac[])
     >- (qexists_tac `hdr_bb` >> asm_rewrite_tac[])
     >- (qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
         qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb _ = SOME back_bb` >>
         qexistsl_tac [`back_bb`, `body_end.cs_next_id`, `ip`,
           `STRING #"%" (toString body_st.cs_next_var)`, `body_end.cs_current_insts`] >>
         simp[Abbr `back_bb`, Abbr `nv`] >> fs[window_array_cursor_def])
     >- (qexists_tac `isite` >> fs[window_array_cursor_def]) >>
     fs[window_array_transition_def]) >>
  `window_array_inv ctx func owner ids ei asz msz T ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (qpat_assum `window_array_transition _ _ _ {isite} [] u t` mp_tac >>
     simp_tac bool_ss [Abbr `t`] >> strip_tac >>
     irule window_array_backedge_inv >> asm_rewrite_tac[]) >>
  `window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t` by
    (irule window_array_transition_region >>
     qexistsl_tac [`{isite}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_transition_trans >> qexists_tac `u` >> asm_rewrite_tac[]
QED

Finalise window_array_dynamic_round


Theorem window_array_actual_control_loop:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then
     abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  window_strong_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  (active ==> dsite IN ids /\
    dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\ dsite <> isite) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d j s /\
  j <= LENGTH avs ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t
Proof
  strip_tac >>
  `!k u. k < LENGTH avs /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k u ==>
    ?v. window_array_transition ctx func owner ids
        [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) v` by
    (rpt gen_tac >> strip_tac >> Cases_on `active` >> full_simp_tac bool_ss []
     >- (irule window_array_dynamic_round >> goal_assum (drule_at Any) >> metis_tac[])
     >> irule window_array_static_round >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule window_array_control_loop >>
  full_simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
  conj_tac
  >- metis_tac[] >>
  qmatch_asmsub_rename_tac `lookup_block body_st.cs_current_bb _ = SOME body_bb` >>
  qexistsl_tac [`body_bb`, `FST (SND labels)`,
    `STRING #"%" (toString (owner.cs_next_var+1))`,
    `STRING #"%" (toString (owner.cs_next_var+2))`, `FST labels`,
    `owner.cs_next_id+1`, `STRING #"%" (toString owner.cs_next_var)`, `j`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  fs[not_fresh_at_def] >> metis_tac[]
QED
