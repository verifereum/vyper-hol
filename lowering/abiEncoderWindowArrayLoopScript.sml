(* Actual-window array control and finite, same-witness loop composition. *)
Theory abiEncoderWindowArrayLoop
Ancestors
  abiEncoderWindowArrayBody abiEncoderArrayLoopCode abiEncoderArrayHeader
  abiDecoderArrayBackedge abiEncoderExtendControl abiEncoderExtendSim
  abiEncoderWindowArrayInvariant abiEncoderSharedArrayRound venomState arithmetic

Theorem window_array_loop_finite:
  !n j s.
    j+n = N /\ P j s /\
    (!k u. k < N /\ P k u ==>
      ?v. window_array_transition ctx func owner ids outs u v /\ P (SUC k) v) /\
    (!u. P N u ==>
      ?v. window_array_transition ctx func owner ids outs u v /\ Q v) ==>
    ?t. window_array_transition ctx func owner ids outs s t /\ Q t
Proof
  Induct
  >- (rpt gen_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < N` by decide_tac >>
  `?v. window_array_transition ctx func owner ids outs s v /\ P (SUC j) v` by
    metis_tac[] >>
  `SUC j+n = N` by decide_tac >>
  `?t. window_array_transition ctx func owner ids outs v t /\ Q t` by
    metis_tac[] >>
  metis_tac[window_array_transition_trans]
QED

Theorem window_array_loop_run:
  j <= N /\ P j s /\
  (!k u. k < N /\ P k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ P (SUC k) v) /\
  (!u. P N u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ Q v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\ Q t
Proof
  strip_tac >> irule window_array_loop_finite >>
  qexistsl_tac [`N`, `P`, `j`, `N-j`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem window_array_header_run:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w i /\
  i <= n /\ n < dimword (:256) /\ alloca_inv s /\ alloca_room ctx func s /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) ==>
  window_array_transition ctx func owner ids outs s
    (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >>
  `abi_encoder_extend_sim ctx func s
    (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))` by
    (irule abi_encoder_array_header_extend_sim >> metis_tac[]) >>
  simp_tac bool_ss [window_array_transition_def] >> asm_rewrite_tac[] >>
  simp[abi_encode_array_header_state_def, jump_to_def, update_var_def,
    abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def,
    abiEncoderWindowContractTheory.window_alloca_growth_def,
    venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, exprLoweringPropsTheory.alloca_room_def,
    exprLoweringPropsTheory.pending_alloca_size_def, window_sizes32_def,
    lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, exprLoweringPropsTheory.alloca_room_def,
    exprLoweringPropsTheory.pending_alloca_size_def] >> metis_tac[]
QED

Theorem window_array_header_eval[local]:
  (!x. op = Var x ==> not_fresh_at owner x) /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) ==>
  eval_operand op (jump_to label (abi_encode_array_header_state iv cmp done i n s)) =
  eval_operand op s
Proof
  strip_tac >> Cases_on `op` >>
  simp[eval_operand_def, jump_to_def, abi_encode_array_header_state_def,
    update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED


Theorem window_array_header_inv:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op hdr sb cap d j s /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) /\
  window_array_transition ctx func owner ids outs s
    (jump_to label (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) ==>
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j
    (jump_to label (abi_encode_array_header_state iv cmp done j (LENGTH avs) s))
Proof
  strip_tac >>
  `!op. (!x. op = Var x ==> not_fresh_at owner x) ==>
    eval_operand op (jump_to label
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) = eval_operand op s` by
    (rpt strip_tac >> irule window_array_header_eval >> metis_tac[]) >>
  `alloca_inv (jump_to label (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) /\
   alloca_room ctx func
     (jump_to label (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) /\
   ~(jump_to label (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)).vs_halted` by
    fs[window_array_transition_def] >>
  irule window_array_inv_observations >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [jump_to_def, abi_encode_array_header_state_def, update_var_def,
    SimpLHS] >>
  qexistsl_tac [`hdr`, `s`] >> asm_rewrite_tac[] >>
  qpat_x_assum `!op. _ ==> eval_operand op (jump_to _ _) = _` mp_tac >>
  simp[jump_to_def, abi_encode_array_header_state_def, update_var_def]
QED


Theorem window_store_allocas[local]:
  (mstore a w s).vs_allocas = s.vs_allocas
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem window_store_next[local]:
  (mstore a w s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem window_store_halted[local]:
  (mstore a w s).vs_halted = s.vs_halted
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem window_store_labels[local]:
  (mstore a w s).vs_labels = s.vs_labels
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem window_store_vars[local]:
  (mstore a w s).vs_vars = s.vs_vars
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem window_array_backedge_run:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword (:256) /\
  site IN ids /\ FLOOKUP s.vs_allocas site = SOME (w2n p,32) /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!x. not_fresh_at owner x ==> x <> nv) ==>
  window_array_transition ctx func owner ids outs s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >>
  `abi_encoder_extend_sim ctx func s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))` by
    (irule abi_encoder_array_backedge_extend_sim >> metis_tac[]) >>
  `abi_encoder_registered_effect ids outs s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))) /\
   alloca_inv (jump_to hdr
     (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))` by
    metis_tac[abi_encoder_array_backedge_registered] >>
  qmatch_goalsub_abbrev_tac `window_array_transition _ _ _ _ _ _ t` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels /\
   t.vs_vars = s.vs_vars |+ (nv,n2w (SUC i))` by
    simp[Abbr `t`, jump_to_def, update_var_def, window_store_allocas,
      window_store_next, window_store_halted, window_store_labels, window_store_vars] >>
  simp_tac bool_ss [window_array_transition_def] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (irule window_array_growth_observations >> asm_rewrite_tac[])
  >- metis_tac[window_array_room_observations]
  >- (rpt strip_tac >> fs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  metis_tac[window_array_sizes_observations]
QED

Theorem window_array_backedge_eval[local]:
  (!x. op = Var x ==> not_fresh_at owner x) /\
  (!x. not_fresh_at owner x ==> x <> nv) ==>
  eval_operand op (jump_to hdr (mstore slot w (update_var nv w s))) = eval_operand op s
Proof
  strip_tac >> Cases_on `op` >>
  simp[eval_operand_def, jump_to_def, lookup_var_def, window_store_vars,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem window_array_backedge_cursor[local]:
  window_array_cursor enabled owner op site slot value sb cap d n s /\
  (!x. not_fresh_at owner x ==> x <> nv) /\
  (enabled ==> venomMemDefs$regions_disjoint (slot,32) (islot,32)) ==>
  window_array_cursor enabled owner op site slot value sb cap d n
    (jump_to hdr (mstore islot w (update_var nv w s)))
Proof
  reverse (Cases_on `enabled`) >- simp[window_array_cursor_def] >>
  simp_tac bool_ss [window_array_cursor_def] >> strip_tac >>
  `eval_operand op (jump_to hdr (mstore islot w (update_var nv w s))) =
    eval_operand op s` by (irule window_array_backedge_eval >> metis_tac[]) >>
  `slot+32 <= islot \/ islot+32 <= slot` by
    fs[venomMemDefsTheory.regions_disjoint_def] >>
  asm_rewrite_tac[] >>
  simp[jump_to_def, window_store_allocas, update_var_def,
    valueEncodingPropsTheory.mstore_mem_word_at_disjoint]
QED

Theorem window_array_backedge_index[local]:
  window_array_cursor T owner ip isite islot j sb cap d n s /\
  (!x. not_fresh_at owner x ==> x <> nv) ==>
  window_array_cursor T owner ip isite islot (SUC j) sb cap d n
    (jump_to hdr (mstore islot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  simp_tac bool_ss [window_array_cursor_def] >> strip_tac >>
  `eval_operand ip (jump_to hdr (mstore islot (n2w (SUC j))
    (update_var nv (n2w (SUC j)) s))) = eval_operand ip s` by
    (irule window_array_backedge_eval >> metis_tac[]) >>
  asm_rewrite_tac[] >> simp[jump_to_def, window_store_allocas, update_var_def,
    valueEncodingPropsTheory.mstore_mem_word_at_same]
QED

Theorem window_array_backedge_inv:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs (SUC j) d s.vs_memory /\
  window_array_cursor T owner ip isite islot j sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_cursor active owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty +
     SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  (!x. count_op = Var x ==> not_fresh_at owner x) /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. not_fresh_at owner x ==> x <> nv) /\
  (active ==> dsite <> isite) /\
  isite IN ids /\
  window_array_transition ctx func owner {isite} [] s
    (jump_to hdr (mstore islot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))) ==>
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op hdr sb cap d (SUC j)
    (jump_to hdr (mstore islot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >>
  `active ==> venomMemDefs$regions_disjoint (dslot,32) (islot,32)` by
    (strip_tac >>
     full_simp_tac bool_ss [window_array_cursor_def, window_array_root_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def] >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` >>
  `window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t` by
    (irule window_array_root_transition >> goal_assum (drule_at Any) >>
     simp[]) >>
  `abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory` by
    (irule window_array_prefix_registered_frame >>
     conj_tac
     >- (qexistsl_tac [`{isite}`, `[]`, `s`] >> simp[] >>
         fs[window_array_root_def] >>
         metis_tac[window_array_transition_effect, window_array_transition_resources]) >>
     qexistsl_tac [`active`, `asz`, `cap`, `ei`, `msz`, `sb`, `s.vs_memory`] >>
     fs[window_array_root_def]) >>
  simp_tac bool_ss [window_array_inv_def] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (unabbrev_all_tac >> irule window_array_backedge_index >> metis_tac[])
  >- (unabbrev_all_tac >> irule window_array_backedge_cursor >> metis_tac[])
  >- (unabbrev_all_tac >> metis_tac[window_array_backedge_eval])
  >- fs[window_array_transition_def] >>
  simp[Abbr `t`, jump_to_def]
QED

Theorem window_array_header_step:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op hdr sb cap d j s /\
  j <= LENGTH avs /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) ==>
  window_array_transition ctx func owner ids outs s
    (jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op
    (if j < LENGTH avs then body_lbl else exit_lbl) sb cap d j
    (jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s))
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
   window_array_cursor T owner ip isite islot j sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s` by
    metis_tac[window_array_inv_resources, window_array_inv_control, window_array_inv_cursors] >>
  `eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
   count_op <> Var iv` by
    (full_simp_tac bool_ss [window_array_inv_def] >> metis_tac[]) >>
  `LENGTH avs < dimword (:256)` by
    (drule window_array_inv_root >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp[abiEncoderWindowTheory.abi_encoder_window_array_iff,
       contractABITheory.valid_length_def]) >>
  `eval_operand ip s = SOME (n2w islot) /\ mload islot s = n2w j /\
   w2n (n2w islot : bytes32) = islot` by
    (full_simp_tac bool_ss [window_array_cursor_def] >>
     asm_simp_tac (srw_ss()) [GSYM valueEncodingPropsTheory.mem_word_at_eq_mload,
       wordsTheory.w2n_n2w]) >>
  `window_array_transition ctx func owner ids outs s
    (jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s))` by
    (irule window_array_header_run >> metis_tac[]) >>
  asm_rewrite_tac[] >> irule window_array_header_inv >> metis_tac[]
QED

(* The round callback is body execution followed by the concrete backedge.
   The terminal header is executed too, even for an empty input. *)
Theorem window_array_control_loop:
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
        ip isite islot dp dsite dslot count_op hdr sb cap d (SUC k) v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t
Proof
  strip_tac >> irule window_array_loop_run >>
  qexistsl_tac [`LENGTH avs`,
    `\k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op hdr sb cap d k u`, `j`] >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> full_simp_tac bool_ss [] >>
      qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
      `k <= LENGTH avs` by decide_tac >>
      `window_array_transition ctx func owner ids outs u
         (jump_to body_lbl (abi_encode_array_header_state iv cmp done k (LENGTH avs) u)) /\
       window_array_inv ctx func owner ids ei asz msz active ty avs src dst
         ip isite islot dp dsite dslot count_op body_lbl sb cap d k
         (jump_to body_lbl (abi_encode_array_header_state iv cmp done k (LENGTH avs) u))` by
        (drule_all window_array_header_step >> simp[] >> decide_tac) >>
      first_x_assum drule_all >> strip_tac >> qexists_tac `v` >>
      asm_rewrite_tac[] >> metis_tac[window_array_transition_trans]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
  `LENGTH avs <= LENGTH avs` by decide_tac >>
  qexists_tac `jump_to exit_lbl
    (abi_encode_array_header_state iv cmp done (LENGTH avs) (LENGTH avs) u)` >>
  drule_all window_array_header_step >> simp[]
QED

Theorem window_array_header_high_vars:
  not_fresh_at bound iv /\ not_fresh_at bound cmp /\ not_fresh_at bound done ==>
  !x. ~not_fresh_at bound x ==>
    lookup_var x (jump_to label (abi_encode_array_header_state iv cmp done i n s)) =
    lookup_var x s
Proof
  rpt strip_tac >>
  `x <> iv /\ x <> cmp /\ x <> done` by metis_tac[] >>
  simp[jump_to_def, abi_encode_array_header_state_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem window_array_backedge_high_vars:
  not_fresh_at bound nv ==>
  !x. ~not_fresh_at bound x ==>
    lookup_var x (jump_to hdr (mstore islot w (update_var nv w s))) = lookup_var x s
Proof
  rpt strip_tac >> `x <> nv` by metis_tac[] >>
  simp[jump_to_def, lookup_var_def, window_store_vars,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem window_array_loop_run_observed:
  j <= N /\ P j s /\
  (!k u. k < N /\ P k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ P (SUC k) v /\
      (!x. ~not_fresh_at bound x ==> lookup_var x v = lookup_var x u)) /\
  (!u. P N u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\ Q v /\
      (!x. ~not_fresh_at bound x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\ Q t /\
    (!x. ~not_fresh_at bound x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`P` |->
    `\k u. P k u /\ (!x. ~not_fresh_at bound x ==> lookup_var x u = lookup_var x s)`]
    window_array_loop_run) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
      qexists_tac `v` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `v` >> simp[] >> metis_tac[]
QED

Theorem window_array_control_loop_observed:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done) /\
  not_fresh_at bound iv /\ not_fresh_at bound cmp /\ not_fresh_at bound done /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op hdr sb cap d j s /\
  j <= LENGTH avs /\
  (!k u. k < LENGTH avs /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op body_lbl sb cap d k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op hdr sb cap d (SUC k) v /\
      (!x. ~not_fresh_at bound x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t /\
    (!x. ~not_fresh_at bound x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`N` |-> `LENGTH (avs:abi_value list)`, `P` |->
    `\k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op hdr sb cap d k u`]
    window_array_loop_run_observed) >>
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
      rpt strip_tac >> first_x_assum drule >> disch_then SUBST1_TAC >>
      irule window_array_header_high_vars >> qexists_tac `bound` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
  `LENGTH avs <= LENGTH avs` by decide_tac >>
  qexists_tac `jump_to exit_lbl
    (abi_encode_array_header_state iv cmp done (LENGTH avs) (LENGTH avs) u)` >>
  conj_tac
  >- (drule_all window_array_header_step >> simp[]) >>
  conj_tac
  >- (drule_all window_array_header_step >> simp[]) >>
  rpt strip_tac >> irule window_array_header_high_vars >>
  qexists_tac `bound` >> simp[]
QED
