Theory exprSimAbiEncodeFramedArrayControl
Ancestors
  exprSimAbiEncodeFramedArrayBody exprSimAbiEncodeExecFrame
  abiEncoderWindowArrayLoop abiEncoderWindowArrayRound abiEncoderArrayCode
  abiEncoderWindowArrayInvariant abiEncoderWindowPhase abiEncoderWindowContract
  venomState venomExecSemantics compileEnv list arithmetic
  exprLoweringProps abiEncoderArrayHeader

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
  simp[abi_encode_exec_frame_def, pending_alloca_size_def,
    jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]
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
