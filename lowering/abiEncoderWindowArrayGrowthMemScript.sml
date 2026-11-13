(* Length growth accumulated beside memory safety at the same loop witness. *)
Theory abiEncoderWindowArrayGrowthMem
Ancestors
  abiEncoderWindowLoopRelationMem abiEncoderArrayHeader venomState arithmetic

Theorem window_array_control_loop_growth_mem:
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
      (framed ==> window_mem_frame ctx func u v) /\
      LENGTH u.vs_memory <= LENGTH v.vs_memory) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op exit_lbl sb cap d (LENGTH avs) t /\
    (framed ==> window_mem_frame ctx func s t) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  irule (window_array_control_loop_relation_mem |> Q.INST
    [`R` |-> `\s t. LENGTH s.vs_memory <= LENGTH t.vs_memory`]
    |> SIMP_RULE bool_ss []) >>
  conj_tac >- (rpt strip_tac >> decide_tac) >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- (qexists_tac `exit_bb` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`body_bb`, `body_lbl`, `cmp`, `done`, `hdr`, `id`, `iv`, `j`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> simp[abi_encode_array_header_state_def, jump_to_def, update_var_def]
QED
