(* Relational accumulation at the actual array-loop endpoints. *)
Theory abiEncoderWindowLoopRelationMem
Ancestors
  abiEncoderWindowHeaderMem abiEncoderWindowControlMem windowTransitionMem
  abiEncoderWindowMemFrame memContinuation

Theorem window_array_control_loop_relation_mem:
  (!u. R u u) /\
  (!u v w. R u v /\ R v w ==> R u w) /\
  (!k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op hdr sb cap d k u /\
    k <= LENGTH avs ==>
    R u (jump_to (if k < LENGTH avs then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done k (LENGTH avs) u))) /\
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
        ip isite islot dp dsite dslot count_op hdr sb cap d (SUC k) v /\
      (framed ==> window_mem_frame ctx func u v) /\ R u v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t /\
    (framed ==> window_mem_frame ctx func s t) /\ R s t
Proof
  strip_tac >>
  ho_match_mp_tac (window_array_loop_run_mem |> Q.INST
    [`N` |-> `LENGTH (avs:abi_value list)`,
     `P` |-> `\k u. window_array_inv ctx func owner ids ei asz msz active ty avs src dst
       ip isite islot dp dsite dslot count_op hdr sb cap d k u /\
       (framed ==> window_mem_frame ctx func s u) /\ R s u`]) >>
  simp_tac bool_ss [] >> asm_rewrite_tac[window_mem_frame_refl] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> full_simp_tac bool_ss [] >>
      qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
      `k <= LENGTH avs` by decide_tac >>
      drule_all window_array_header_step_mem >> simp[] >>
      disch_then (qspec_then `outs` strip_assume_tac) >>
      qpat_x_assum `!k u. _ ==> ?v. _ /\ _ /\ _ /\ (framed ==> _) /\ _` drule_all >>
      strip_tac >> qexists_tac `v` >> asm_rewrite_tac[] >>
      rpt conj_tac
      >- metis_tac[window_array_transition_trans_mem]
      >- metis_tac[mem_cont_sim_trans]
      >- metis_tac[window_mem_frame_trans] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j s` kall_tac >>
  `LENGTH avs <= LENGTH avs` by decide_tac >>
  qexists_tac `jump_to exit_lbl
    (abi_encode_array_header_state iv cmp done (LENGTH avs) (LENGTH avs) u)` >>
  drule_all window_array_header_step_mem >> simp[] >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_mem_frame_trans] >>
  qpat_x_assum `!k u. _ /\ _ ==> R u _`
    drule_all >> simp[] >> metis_tac[]
QED
