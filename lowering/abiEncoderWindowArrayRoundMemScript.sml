(* Same-endpoint memory companions for array rounds. *)
Theory abiEncoderWindowArrayRoundMem
Ancestors
  abiEncoderWindowArrayRecursiveMem abiEncoderWindowLoopMem
  abiEncoderWindowArrayRound abiEncoderWindowControlMem windowTransitionMem
  abiEncoderWindowArrayLoop abiEncoderWindowArrayInvariant abiEncoderArrayLoopCode
  abiEncoderWindowArrayBody abiEncoderWindowArrayLayout
  abiEncoderArrayHeader abiEncoderArrayRound abiEncoderWindowContract
  compileEnv loweringStateRelDefs freshWrites venomState venomMemDefs valueEncoding valueEncodingDefs valueEncodingProps
  venomExecSemantics venomInst words finite_map pred_set list arithmetic

Theorem window_array_round_backedge_code:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (!x. ip = Var x ==> not_fresh_at owner x) ==>
  (!x. not_fresh_at owner x ==> x <> STRING #"%" (toString body_end.cs_next_var)) /\
  ip <> Var (STRING #"%" (toString body_end.cs_next_var)) /\
  (?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0)
Proof
  strip_tac >>
  `!x. not_fresh_at owner x ==> x <> STRING #"%" (toString body_end.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def, abi_encoder_array_loop_code_def] >>
     first_x_assum (qspec_then `body_end.cs_next_var` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
  qexists_tac `header_bb` >> asm_rewrite_tac[] >>
  simp[Abbr `header_bb`, abi_encode_array_header_insts_def,
    phi_prefix_length_def, mk_inst_def]
QED

Theorem window_array_round_backedge_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  window_array_cursor T owner ip isite islot k sb cap d n u /\
  eval_operand (Var (STRING #"%" (toString body_st.cs_next_var))) u = SOME (n2w k) /\
  k < ncount /\ ncount < dimword (:256) /\
  ~u.vs_halted /\ u.vs_current_bb = body_end.cs_current_bb /\
  u.vs_inst_idx = LENGTH body_end.cs_current_insts /\
  alloca_inv u /\ alloca_room ctx func u ==>
  window_array_transition ctx func owner {isite} [] u
    (jump_to (FST labels) (mstore islot (n2w (SUC k))
      (update_var (STRING #"%" (toString body_end.cs_next_var)) (n2w (SUC k)) u))) /\
  mem_cont_sim ctx func u
    (jump_to (FST labels) (mstore islot (n2w (SUC k))
      (update_var (STRING #"%" (toString body_end.cs_next_var)) (n2w (SUC k)) u)))
Proof
  strip_tac >>
  `!x. ip = Var x ==> not_fresh_at owner x` by fs[window_array_cursor_def] >>
  drule_all window_array_round_backedge_code >> strip_tac >>
  `islot+32 <= u.vs_alloca_next` by metis_tac[window_array_cursor_frontier] >>
  `eval_operand ip u = SOME (n2w islot) /\ islot < dimword (:256) /\
   FLOOKUP u.vs_allocas isite = SOME (islot,32)` by fs[window_array_cursor_def] >>
  `w2n (n2w islot : bytes32) = islot` by simp[] >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME
    <|bb_label := body_end.cs_current_bb; bb_instructions := body_end.cs_current_insts ++
      abi_decode_backedge_insts body_end.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
        (STRING #"%" (toString body_end.cs_next_var)) ip (FST labels)|>` by
    fs[abi_encoder_array_loop_code_def] >>
  qpat_assum `w2n (n2w islot : bytes32) = islot`
    (fn th => once_rewrite_tac [GSYM th]) >>
  irule window_array_backedge_run_mem >>
  qpat_assum `lookup_block u.vs_current_bb _ = _` (irule_at Any) >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`isite`, `body_end.cs_current_insts`, `ncount`] >>
  qexistsl_tac [`STRING #"%" (toString body_st.cs_next_var)`, `ip`, `body_end.cs_next_id`, `hdr_bb`] >>
  simp[]
QED

Theorem window_array_round_finish_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d u /\
  abi_encoder_array_prefix ty avs (SUC k) d u.vs_memory /\
  window_array_cursor T owner ip isite islot k sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
  window_array_cursor active owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
  (!x. count_op = Var x ==> not_fresh_at owner x) /\
  eval_operand count_op u = SOME (n2w (LENGTH avs)) /\
  eval_operand (Var (STRING #"%" (toString body_st.cs_next_var))) u = SOME (n2w k) /\
  k < LENGTH avs /\ isite IN ids /\ (active ==> dsite <> isite) /\
  ~u.vs_halted /\ u.vs_current_bb = body_end.cs_current_bb /\
  u.vs_inst_idx = LENGTH body_end.cs_current_insts ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t /\
    mem_cont_sim ctx func u t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t
Proof
  strip_tac >>
  `alloca_inv u /\ alloca_room ctx func u /\ LENGTH avs < dimword (:256)` by
    (fs[window_array_root_def, abiEncoderWindowTheory.abi_encoder_window_array_iff,
      contractABITheory.valid_length_def]) >>
  drule_all window_array_round_backedge_mem >> strip_tac >>
  `!x. ip = Var x ==> not_fresh_at owner x` by fs[window_array_cursor_def] >>
  drule_all window_array_round_backedge_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func u t` >>
  `window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (simp_tac bool_ss [Abbr `t`] >> irule window_array_backedge_inv >>
     asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_transition_region >>
  qexistsl_tac [`{isite}`, `[]`] >> asm_rewrite_tac[] >> simp[]
QED

Theorem window_array_round_output_frame:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  window_array_cursor T owner ip isite islot k sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_transition ctx func owner child_ids outs s u /\
  child_ids SUBSET ids /\ isite NOTIN child_ids /\
  EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc (Array NONE ty) (ListV avs))) outs ==>
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d u /\
  window_array_cursor T owner ip isite islot k sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
  window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u
Proof
  strip_tac >>
  `window_array_transition ctx func owner child_ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_transition_region >>
     qexistsl_tac [`child_ids`, `outs`] >> asm_rewrite_tac[SUBSET_REFL]) >>
  `window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d u` by
    (irule window_array_root_transition >>
     qexistsl_tac [`child_ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
     full_simp_tac bool_ss [window_array_root_def, EVERY_DEF] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_cursor_frame >>
      qexistsl_tac [`child_ids`, `ctx`, `func`,
        `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
      asm_rewrite_tac[] >>
      full_simp_tac bool_ss [window_array_cursor_def, EVERY_DEF] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  irule window_array_transition_region >>
  qexistsl_tac [`child_ids`, `outs`] >> asm_rewrite_tac[]
QED

Theorem window_array_static_round_geometry:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs k d s.vs_memory /\ k < LENGTH avs ==>
  d <= d+32+k*asz /\ d+32+k*asz+LENGTH (enc ty (EL k avs)) <=
    d+LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz F)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  drule_all window_array_prefix_step_geometry >> strip_tac >>
  drule window_array_layout >> strip_tac >>
  `k*abi_member_head_size ty+LENGTH (enc ty (EL k avs)) <=
    LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem window_array_static_round_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz F ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    mem_cont_sim ctx func s t /\
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
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\ alloca_inv s /\
   (!x. count_op = Var x ==> not_fresh_at owner x) /\
   eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
   ~s.vs_halted /\ s.vs_current_bb = body_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH body_st.cs_current_insts` by
    (full_simp_tac bool_ss [window_array_inv_def, abi_encoder_array_loop_code_def] >>
     simp_tac bool_ss [LENGTH] >>
     qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >> asm_rewrite_tac[]) >>
  `window_array_root ctx func body_st ids ei asz msz F ty avs src dst sb cap d s` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
   mload islot s = n2w k /\ fn_has_code body_st body_end func` by
    fs[window_array_cursor_def, abi_encoder_array_loop_code_def, mload_def, mem_word_at_def] >>
  `islot+32 <= s.vs_alloca_next` by metis_tac[window_array_cursor_frontier] >>
  drule_all window_array_static_body_run_mem >> strip_tac >>
  rename1 `mem_cont_sim ctx func s u` >>
  `window_array_transition ctx func owner
    (window_alloca_sites func (frag_ids body_st body_end))
    [(d+32+k*asz,LENGTH (enc ty (EL k avs)))] s u` by
    (irule window_array_transition_owner_weaken >> metis_tac[]) >>
  drule_all window_array_static_round_geometry >> strip_tac >>
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d u /\
   window_array_cursor T owner ip isite islot k sb cap d (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
   window_array_transition ctx func owner ids [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_round_output_frame >> asm_rewrite_tac[] >>
     qexistsl_tac [`window_alloca_sites func (frag_ids body_st body_end)`,
       `[(d+32+k*asz,LENGTH (enc ty (EL k avs)))]`] >>
     asm_rewrite_tac[] >> simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> asm_rewrite_tac[]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  `?t. window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t /\ mem_cont_sim ctx func u t /\
    window_array_inv ctx func owner ids ei asz msz F ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (irule window_array_round_finish_mem >>
     qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` (irule_at Any) >>
     asm_rewrite_tac[window_array_cursor_def] >>
     metis_tac[window_array_transition_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> metis_tac[window_array_transition_trans_mem]
QED

Theorem window_array_dynamic_offset_advance:
  is_dynamic ty /\ k < LENGTH avs /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE k avs)) ==>
  off + LENGTH (enc ty (EL k avs)) = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))
Proof
  strip_tac >>
  `TAKE (SUC k) avs = TAKE k avs ++ [EL k avs]` by
    simp[rich_listTheory.TAKE_SUC, TAKE1_DROP] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM,
    abiDecodeRangesTheory.abi_member_tail_size_def, ADD_ASSOC, ADD_CLAUSES]
QED

Theorem window_array_dynamic_round_frame:
  window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs k d s.vs_memory /\ k < LENGTH avs /\
  window_array_cursor T owner ip isite islot k sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_cursor T owner dp dsite dslot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE k avs)) /\
  child_ids SUBSET ids /\ dsite IN ids /\ isite NOTIN child_ids /\ isite <> dsite /\
  window_array_transition ctx func owner (child_ids UNION {dsite})
    [(d+32+k*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL k avs)))] s u /\
  mem_word_at dslot u.vs_memory = n2w (off+LENGTH (enc ty (EL k avs))) ==>
  window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d u /\
  window_array_cursor T owner ip isite islot k sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
  window_array_cursor T owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
  window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `is_dynamic ty` by fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  `32+off+LENGTH (enc ty (EL k avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   k*abi_member_head_size ty+32 <= off` by
    (drule_all window_array_prefix_step_geometry >>
     asm_simp_tac bool_ss [] >> strip_tac >> decide_tac) >>
  `window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d u /\
   window_array_cursor T owner ip isite islot k sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
   window_array_transition ctx func owner ids [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s u` by
    (irule window_array_round_output_frame >> asm_rewrite_tac[] >>
     qexistsl_tac [`child_ids UNION {dsite}`,
       `[(d+32+k*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL k avs)))]`] >>
     asm_rewrite_tac[] >> simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     asm_rewrite_tac [IN_UNION, IN_SING, UNION_SUBSET, INSERT_SUBSET, EMPTY_SUBSET] >>
     full_simp_tac bool_ss [] >> decide_tac) >>
  drule_all window_array_dynamic_offset_advance >> disch_tac >>
  asm_rewrite_tac[] >> irule window_array_cursor_word >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  metis_tac[]
QED

Theorem window_array_dynamic_round_complete_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end) /\
  window_array_inv ctx func owner ids ei asz msz T ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite IN ids /\ dsite <> isite /\ k < LENGTH avs /\
  off = LENGTH avs * abi_member_head_size ty + SUM (MAP (abi_member_tail_size ty) (TAKE k avs)) /\
  window_array_transition ctx func body_st
    (window_alloca_sites func (frag_ids body_st body_end) UNION {dsite})
    [(d+32+k*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL k avs)))] s u /\
  abi_encoder_array_prefix ty avs (SUC k) d u.vs_memory /\
  mem_word_at dslot u.vs_memory = n2w (off+LENGTH (enc ty (EL k avs))) /\
  eval_operand idx u = SOME (n2w k) /\ u.vs_current_bb = body_end.cs_current_bb /\
  u.vs_inst_idx = LENGTH body_end.cs_current_insts /\ mem_cont_sim ctx func s u ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t
Proof
  strip_tac >>
  `!x. not_fresh_at owner x ==> not_fresh_at body_st x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `owner` >>
     fs[abi_encoder_array_loop_code_def]) >>
  `window_array_transition ctx func owner
    (window_alloca_sites func (frag_ids body_st body_end) UNION {dsite})
    [(d+32+k*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL k avs)))] s u` by
    (irule window_array_transition_owner_weaken >> metis_tac[]) >>
  `window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d s /\
   abi_encoder_array_prefix ty avs k d s.vs_memory /\
   window_array_cursor T owner ip isite islot k sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
   window_array_cursor T owner dp dsite dslot off sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
   (!x. count_op = Var x ==> not_fresh_at owner x) /\
   eval_operand count_op s = SOME (n2w (LENGTH avs))` by
    (full_simp_tac bool_ss [window_array_inv_def] >> asm_rewrite_tac[]) >>
  `isite <> dsite` by metis_tac[] >>
  drule_all window_array_dynamic_round_frame >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> metis_tac[]) >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  `?t. window_array_transition ctx func owner ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u t /\ mem_cont_sim ctx func u t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) t` by
    (irule window_array_round_finish_mem >>
     qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` (irule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[window_array_transition_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> metis_tac[window_array_transition_trans_mem]
QED

Theorem window_array_dynamic_round_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end) /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  dsite <> isite /\ k < LENGTH avs /\
  window_array_inv ctx func owner ids ei asz msz T ty avs src dst
    ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    mem_cont_sim ctx func s t /\
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
     (LENGTH (enc (Array NONE ty) (ListV avs))) s /\ alloca_inv s /\
   ~s.vs_halted /\ s.vs_current_bb = body_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH body_st.cs_current_insts` by
    (full_simp_tac bool_ss [window_array_inv_def, abi_encoder_array_loop_code_def, Abbr `off`] >>
     simp_tac bool_ss [LENGTH] >>
     qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >> asm_rewrite_tac[]) >>
  `window_array_root ctx func body_st ids ei asz msz T ty avs src dst sb cap d s /\
   window_array_cursor T body_st dp dsite dslot off sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s` by
    (conj_tac >- (irule window_array_root_owner_mono >> metis_tac[]) >>
     irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
   mload islot s = n2w k /\ fn_has_code body_st body_end func` by
    fs[window_array_cursor_def, abi_encoder_array_loop_code_def, mload_def, mem_word_at_def] >>
  `islot+32 <= s.vs_alloca_next` by metis_tac[window_array_cursor_frontier] >>
  `off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE k avs))` by simp[Abbr `off`] >>
  drule_all window_array_dynamic_body_run_mem >> strip_tac >>
  irule window_array_dynamic_round_complete_mem >>
  qpat_assum `window_array_transition _ _ body_st _ _ s _` (irule_at Any) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` (irule_at Any) >>
  asm_rewrite_tac[] >> qexists_tac `idx` >> asm_rewrite_tac[]
QED
