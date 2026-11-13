(* Cursor-bounded, same-witness memory-safe array control loops. *)
Theory abiEncoderWindowLoopMem
Ancestors
  abiEncoderWindowControlMem windowTransitionMem abiEncoderWindowArrayLoop
  abiEncoderWindowArrayInvariant abiEncoderWindow abiEncoderWindowContract
  venomMemDefs valueEncodingProps contractABI words arithmetic

Theorem window_array_cursor_frontier:
  window_array_cursor T owner op site slot value sb cap d n s /\ alloca_inv s ==>
  slot + 32 <= s.vs_alloca_next
Proof
  simp_tac bool_ss [window_array_cursor_def, alloca_inv_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem window_array_header_step_mem:
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
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s)) /\
  mem_cont_sim ctx func s
    (jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j (LENGTH avs) s))
Proof
  strip_tac >> drule_all window_array_header_step >> strip_tac >>
  asm_rewrite_tac[] >>
  `alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
   window_array_cursor T owner ip isite islot j sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) s` by
    metis_tac[window_array_inv_resources, window_array_inv_control, window_array_inv_cursors] >>
  `islot + 32 <= s.vs_alloca_next` by
    (irule window_array_cursor_frontier >> metis_tac[]) >>
  `eval_operand count_op s = SOME (n2w (LENGTH avs)) /\ count_op <> Var iv` by
    (full_simp_tac bool_ss [window_array_inv_def] >> metis_tac[]) >>
  `LENGTH avs < dimword (:256)` by
    (drule window_array_inv_root >> simp_tac bool_ss [window_array_root_def] >>
     strip_tac >> qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp[abi_encoder_window_array_iff, valid_length_def]) >>
  `eval_operand ip s = SOME (n2w islot) /\ mload islot s = n2w j /\
   w2n (n2w islot : bytes32) = islot` by
    (full_simp_tac bool_ss [window_array_cursor_def] >>
     asm_simp_tac (srw_ss()) [GSYM mem_word_at_eq_mload, w2n_n2w]) >>
  irule array_header_mem_cont >> metis_tac[]
QED

Theorem window_array_control_loop_mem:
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
      mem_cont_sim ctx func u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op hdr sb cap d (SUC k) v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t
Proof
  strip_tac >> irule window_array_loop_run_mem >>
  qexistsl_tac [`LENGTH avs`,
    `\k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op hdr sb cap d k u`, `j`] >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> full_simp_tac bool_ss [] >>
      qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
      `k <= LENGTH avs` by decide_tac >>
      drule_all window_array_header_step_mem >> simp[] >>
      disch_then (qspec_then `outs` strip_assume_tac) >>
      first_x_assum drule_all >> strip_tac >> qexists_tac `v` >>
      asm_rewrite_tac[] >> metis_tac[window_array_transition_trans_mem]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
  `LENGTH avs <= LENGTH avs` by decide_tac >>
  qexists_tac `jump_to exit_lbl
    (abi_encode_array_header_state iv cmp done (LENGTH avs) (LENGTH avs) u)` >>
  drule_all window_array_header_step_mem >> simp[]
QED
