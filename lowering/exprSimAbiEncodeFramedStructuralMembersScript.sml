Theory exprSimAbiEncodeFramedStructuralMembers
Ancestors
  exprSimAbiEncodeFramedMembers abiEncoderWindowStructuralMembers
  exprSimAbiEncodeExecFrame abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderWindow abiEncoderProps abiEncoderInput
  compileEnv emitHelper fragExec venomState venomMemDefs
  list rich_list arithmetic words finite_map pred_set

Theorem abi_encode_framed_structural_member_static_run:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
    LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (gvs[] >> decide_tac) >>
  drule_all window_structural_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d)` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_static_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_structural_member_prefix_static_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_structural_member_static_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_structural_members_inv_def] >> metis_tac[]
QED

Theorem abi_encode_framed_structural_member_dynamic_run:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k +
        LENGTH (enc (EL k ats) (EL k avs))) /\
      FLOOKUP t.vs_allocas site = SOME (slot,32) /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_structural_members_inv_dynamic_cursor >>
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  `window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  drule_all window_structural_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\ (!x. dst = Var x ==> not_fresh_at st x)` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_dynamic_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_structural_member_prefix_dynamic_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_structural_member_dynamic_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_structural_members_inv_def] >> metis_tac[]
QED
