Theory exprSimAbiEncodeFramedArrayControl
Ancestors
  exprSimAbiEncodeFramedArrayBody exprSimAbiEncodeExecFrame
  abiEncoderWindowArrayLoop abiEncoderWindowArrayRound abiEncoderArrayCode
  abiEncoderWindowArrayInvariant abiEncoderWindowPhase abiEncoderWindowContract
  venomState venomExecSemantics compileEnv list arithmetic
  exprLoweringProps abiEncoderArrayHeader abiEncoderArrayLoopCode
  abiEncoderWindowArrayLayout abiEncoderWindowChild freshWrites finite_map pred_set
  abiEncoderWindowArrayBody

Theorem abi_encode_framed_array_header:
  abi_encode_exec_frame func s
    (jump_to label (abi_encode_array_header_state iv cmp done i n s))
Proof
  simp[abi_encode_exec_frame_def, pending_alloca_size_def,
    jump_to_def, abi_encode_array_header_state_def, update_var_def]
QED

Theorem abi_encode_framed_array_backedge:
  abi_encode_exec_frame func s
    (jump_to hdr (mstore islot w (update_var nv w s)))
Proof
  qspecl_then [`func`, `islot`, `w`, `update_var nv w s`]
    mp_tac abi_encode_exec_frame_mstore >>
  pure_rewrite_tac[abi_encode_exec_frame_def] >>
  simp[pending_alloca_size_def, jump_to_def, update_var_def,
    exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]
QED

Theorem abi_encode_framed_array_loop_run:
  j <= N /\ P j s /\
  (!k u. k < N /\ P k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ P (SUC k) v /\
      abi_encode_exec_frame func u v) /\
  (!u. P N u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ Q v /\
      abi_encode_exec_frame func u v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\ Q t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`P` |->
    `\k u. P k u /\ abi_encode_exec_frame func s u`]
    window_array_loop_run) >>
  simp[abi_encode_exec_frame_refl] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
      qexists_tac `v` >> asm_rewrite_tac[] >>
      irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]
QED

Theorem abi_encode_framed_array_control_loop:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op hdr sb cap d j s /\
  j <= LENGTH avs /\
  (!k u. k < LENGTH avs /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op body_lbl sb cap d k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op hdr sb cap d (SUC k) v /\
      abi_encode_exec_frame func u v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`N` |-> `LENGTH (avs:abi_value list)`, `P` |->
    `\k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op hdr sb cap d k u`]
    abi_encode_framed_array_loop_run) >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
      `k <= LENGTH avs` by decide_tac >>
      `window_array_transition ctx func owner ids outs u
         (jump_to body_lbl (abi_encode_array_header_state iv cmp done k (LENGTH avs) u)) /\
       window_array_inv ctx func owner ids ei asz msz active ty avs src dst
         ip isite islot dp dsite dslot count_op body_lbl sb cap d k
         (jump_to body_lbl (abi_encode_array_header_state iv cmp done k (LENGTH avs) u))` by
        (drule_all window_array_header_step >> simp[] >> decide_tac) >>
      first_x_assum drule_all >> strip_tac >> qexists_tac `v` >>
      asm_rewrite_tac[] >> conj_tac
      >- metis_tac[window_array_transition_trans] >>
      irule abi_encode_exec_frame_trans >>
      qexists_tac `jump_to body_lbl (abi_encode_array_header_state iv cmp done k (LENGTH avs) u)` >>
      asm_rewrite_tac[] >> irule abi_encode_framed_array_header) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
  `LENGTH avs <= LENGTH avs` by decide_tac >>
  qexists_tac `jump_to exit_lbl
    (abi_encode_array_header_state iv cmp done (LENGTH avs) (LENGTH avs) u)` >>
  conj_tac >- (drule_all window_array_header_step >> simp[]) >>
  conj_tac >- (drule_all window_array_header_step >> simp[]) >>
  irule abi_encode_framed_array_header
QED

Theorem abi_encode_framed_array_static_round:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encode_framed_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz F ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz F ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t /\
    abi_encode_exec_frame func s t
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
    u.vs_inst_idx = LENGTH body_end.cs_current_insts /\
    abi_encode_exec_frame func s u` by
    (`eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
      mload islot s = n2w k /\ fn_has_code body_st body_end func` by
       fs[window_array_cursor_def, abi_encoder_array_loop_code_def,
         mload_def, valueEncodingTheory.mem_word_at_def] >>
     drule_all abi_encode_framed_array_static_body_run >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "geometry"
QED

Resume abi_encode_framed_array_static_round[geometry]:
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
  suspend "root"
QED

Resume abi_encode_framed_array_static_round[root]:
  `window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_transition_region >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> asm_rewrite_tac[]) >>
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d u` by
    (irule window_array_root_transition >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
     simp_tac bool_ss [EVERY_DEF] >>
     full_simp_tac bool_ss [window_array_root_def] >> asm_rewrite_tac[SUBSET_REFL]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >>
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
     simp[Abbr `header_bb`, abi_encode_array_header_insts_def,
       phi_prefix_length_def, venomInstTheory.mk_inst_def]) >>
  suspend "execute"
QED

Resume abi_encode_framed_array_static_round[execute]:
  qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
  qabbrev_tac `t = jump_to (FST labels)
    (mstore islot (n2w (SUC k)) (update_var nv (n2w (SUC k)) u))` >>
  `abi_encode_exec_frame func u t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_encode_framed_array_backedge) >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `window_array_transition ctx func owner {isite} [] u t` by
    (`islot < dimword (:256)` by fs[window_array_cursor_def] >>
     `window_array_transition ctx func owner {isite} [] u
       (jump_to (FST labels) (mstore (w2n (n2w islot : bytes32)) (n2w (SUC k))
         (update_var nv (n2w (SUC k)) u)))` suffices_by simp[Abbr `t`] >>
     irule window_array_backedge_run >> asm_rewrite_tac[] >> rpt conj_tac
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
     fs[window_array_transition_def]) >> suspend "compose"
QED

Resume abi_encode_framed_array_static_round[compose]:
  `window_array_inv ctx func owner ids ei asz msz F ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (qpat_assum `window_array_transition _ _ _ {isite} [] u t` mp_tac >>
     simp_tac bool_ss [Abbr `t`] >> strip_tac >>
     irule window_array_backedge_inv >> asm_rewrite_tac[] >> simp[window_array_cursor_def]) >>
  `window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t` by
    (irule window_array_transition_region >>
     qexistsl_tac [`{isite}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_transition_trans >> qexists_tac `u` >> asm_rewrite_tac[]
QED

Finalise abi_encode_framed_array_static_round

Theorem abi_encode_framed_array_dynamic_round:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end) /\
  abi_encode_framed_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite <> isite /\ k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz T ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t /\
    abi_encode_exec_frame func s t
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
    u.vs_inst_idx = LENGTH body_end.cs_current_insts /\
    abi_encode_exec_frame func s u` by
    (`eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
      mload islot s = n2w k /\ fn_has_code body_st body_end func` by
       fs[window_array_cursor_def, abi_encoder_array_loop_code_def,
         mload_def, valueEncodingTheory.mem_word_at_def] >>
     `off = LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) (TAKE k avs))` by simp[Abbr `off`] >>
     drule_all abi_encode_framed_array_dynamic_body_run >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "geometry"
QED

Resume abi_encode_framed_array_dynamic_round[geometry]:
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
     asm_rewrite_tac[] >> decide_tac) >> suspend "cursor"
QED

Resume abi_encode_framed_array_dynamic_round[cursor]:
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
    (irule window_array_cursor_word >> conj_tac >- asm_rewrite_tac[] >>
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
     full_simp_tac bool_ss [window_array_root_def] >> asm_rewrite_tac[SUBSET_REFL]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >> suspend "backedge"
QED

Resume abi_encode_framed_array_dynamic_round[backedge]:
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
     simp[Abbr `header_bb`, abi_encode_array_header_insts_def,
       phi_prefix_length_def, venomInstTheory.mk_inst_def]) >> suspend "execute"
QED

Resume abi_encode_framed_array_dynamic_round[execute]:
  qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
  qabbrev_tac `t = jump_to (FST labels)
    (mstore islot (n2w (SUC k)) (update_var nv (n2w (SUC k)) u))` >>
  `abi_encode_exec_frame func u t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_encode_framed_array_backedge) >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `window_array_transition ctx func owner {isite} [] u t` by
    (`islot < dimword (:256)` by fs[window_array_cursor_def] >>
     `window_array_transition ctx func owner {isite} [] u
       (jump_to (FST labels) (mstore (w2n (n2w islot : bytes32)) (n2w (SUC k))
         (update_var nv (n2w (SUC k)) u)))` suffices_by simp[Abbr `t`] >>
     irule window_array_backedge_run >> asm_rewrite_tac[] >> rpt conj_tac
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
     fs[window_array_transition_def]) >> suspend "compose"
QED

Resume abi_encode_framed_array_dynamic_round[compose]:
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

Finalise abi_encode_framed_array_dynamic_round

Theorem abi_encode_framed_array_actual_control_loop:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then
     abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encode_framed_contract ei /\
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
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!k u. k < LENGTH avs /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k u ==>
    ?v. window_array_transition ctx func owner ids
        [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) v /\
      abi_encode_exec_frame func u v` by
    (rpt gen_tac >> strip_tac >> Cases_on `active` >> full_simp_tac bool_ss []
     >- (irule abi_encode_framed_array_dynamic_round >> goal_assum (drule_at Any) >> metis_tac[])
     >> irule abi_encode_framed_array_static_round >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule abi_encode_framed_array_control_loop >>
  full_simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
  conj_tac >- metis_tac[] >>
  qmatch_asmsub_rename_tac `lookup_block body_st.cs_current_bb _ = SOME body_bb` >>
  qexistsl_tac [`body_bb`, `FST (SND labels)`,
    `STRING #"%" (toString (owner.cs_next_var+1))`,
    `STRING #"%" (toString (owner.cs_next_var+2))`, `FST labels`,
    `owner.cs_next_id+1`, `STRING #"%" (toString owner.cs_next_var)`, `j`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  fs[not_fresh_at_def] >> metis_tac[]
QED
