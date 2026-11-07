Theory exprSimAbiEncodeFramedStructuralMembers
Ancestors
  exprSimAbiEncodeFramedMembers exprSimAbiEncodeFramedArrayBody
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers
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

Theorem abi_encode_framed_structural_member_source_prepare:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?t. window_phase ctx func st ready {} [] s t /\
    window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
      sb cap d ready en t /\
    eval_operand child_src t = SOME (n2w (sb+so)) /\
    (!x. child_src = Var x ==> not_fresh_at ready x) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all abi_encode_framed_emit_add_phase >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[window_structural_members_inv_pure_phase]) >>
  fs[word_add_n2w]
QED

Theorem abi_encode_framed_structural_member_static_step_run_sizes:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids st mid)) /\
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid)) (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_structural_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_structural_members_inv_restrict_end] >>
  drule_all abi_encode_framed_structural_member_static_run >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
   LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (drule_all window_structural_members_inv_output_bounds >> strip_tac >>
     `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
     qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (strip_tac >>
     `site NOTIN window_alloca_sites func (frag_ids st mid)` by metis_tac[] >>
     `d <= d+SUM (MAP abi_member_head_size (TAKE k ats)) /\
      (d+SUM (MAP abi_member_head_size (TAKE k ats))) +
        LENGTH (enc (EL k ats) (EL k avs)) <= d+LENGTH (enc at (ListV avs))` by decide_tac >>
     `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
       (drule_all window_structural_member_static_cursor_frame >> simp[]) >>
     `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
     `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
       (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
        simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
     `mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by
       (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` mp_tac >>
        simp_tac bool_ss [window_structural_members_inv_def] >> metis_tac[]) >>
     drule_all window_member_tail_step >> simp[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `!R. _` kall_tac >>
  irule window_structural_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  simp[] >> metis_tac[SUBSET_UNION, SUBSET_TRANS]
QED

Theorem abi_encode_framed_structural_member_dynamic_step_run_sizes:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (window_alloca_sites func (frag_ids st mid) UNION {site}) SUBSET
    (window_alloca_sites func (frag_ids st en) UNION {site}) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_structural_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_structural_members_inv_restrict_end] >>
  drule_all abi_encode_framed_structural_member_dynamic_run >> strip_tac >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
    (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
     simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
  `mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (drule_all window_member_tail_step >> disch_then (qspec_then `infos` mp_tac) >>
     asm_rewrite_tac[] >> disch_then SUBST1_TAC >> asm_rewrite_tac[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `!R. _` kall_tac >>
  irule window_structural_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Theorem window_structural_member_drop_cons[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem window_structural_member_envelope_frame[local]:
  EVERY (\(b,n). d <= b /\ b+n <= d+len) outs ==>
  !a. EVERY (\(b,n). a < b \/ b+n <= a) [(d,len)] ==>
      EVERY (\(b,n). a < b \/ b+n <= a) outs
Proof
  simp_tac (srw_ss()) [EVERY_MEM] >> strip_tac >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  Cases_on `r` >> first_x_assum drule >> simp[] >> decide_tac
QED

Theorem abi_encode_framed_structural_members_cons_run_sizes:
  window_structural_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = (h0,h1,h2,h3)::rest /\
  abi_encode_framed_contract h0 /\
  compile_abi_encode_complex_elems dst src ((h0,h1,h2,h3)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid u. window_structural_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ DROP (SUC k) infos = rest /\
    compile_abi_encode_complex_elems dst src rest
      (abi_encoder_member_span (TAKE (SUC k) infos))
      (SUM (MAP abi_member_head_size (TAKE (SUC k) ats))) dp mid = (out,en) /\
    window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s u /\
    st.cs_next_var <= mid.cs_next_var /\
    window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    abi_encode_exec_frame func s u
Proof
  strip_tac >>
  `fn_has_code st en func` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all window_members_cons_context >> strip_tac >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode_child,
      cj 3 abiEncoderAppendTheory.cs_appends_abi_encode_mutual, cs_appends_def] >>
  `cs_extends st ready` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `fn_has_code ready en func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_framed_structural_member_source_prepare >> strip_tac >>
  `k < LENGTH infos /\ EL k infos = (h0,h1,h2,h3) /\ DROP (SUC k) infos = rest` by
    metis_tac[window_structural_member_drop_cons] >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _` kall_tac >>
  `abi_encoder_admissible h0` by
    (`abi_encoder_admissible (AbiComplex infos)` by
       (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     simp_tac bool_ss [abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
       abiEncoderAdmissibleTheory.abi_encoder_members_admissible_every] >>
     simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(h0,h1,h2,h3)` mp_tac) >> simp[] >> metis_tac[MEM_EL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> site < ready.cs_next_id` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, window_member_cursor_def] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready mid) SUBSET window_alloca_sites func (frag_ids ready en) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid)) (window_alloca_sites func (frag_ids mid en)) /\
   (EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids ready mid) /\
     DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en)))` by
    metis_tac[window_member_site_split] >>
  qpat_x_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` kall_tac >>
  qpat_x_assum `cs_extends ready mid` kall_tac >>
  qpat_x_assum `cs_extends mid en` kall_tac >>
  qpat_x_assum `cs_extends st ready` kall_tac >>
  `?u ids outs. window_structural_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ window_phase ctx func ready mid ids outs t u /\
    ids SUBSET (window_alloca_sites func (frag_ids ready en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
    (!R. (!i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    abi_encode_exec_frame func t u` by
    suspend "child" >>
  suspend "compose"
QED

Resume abi_encode_framed_structural_members_cons_run_sizes[child]:
  reverse (Cases_on `h3`)
  >- (`EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids ready mid)` by metis_tac[] >>
      drule_all abi_encode_framed_structural_member_static_step_run_sizes >> strip_tac >>
      qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid)`,
        `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`] >>
      asm_rewrite_tac[] >>
      (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
      drule_all window_structural_members_inv_output_bounds >> strip_tac >>
      drule_all window_structural_members_inv_total_bounds >> strip_tac >>
      `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
      simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
      qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(h0,h1,h2,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `(window_alloca_sites func (frag_ids ready mid) UNION {site}) SUBSET
     (window_alloca_sites func (frag_ids ready en) UNION {site}) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
     (window_alloca_sites func (frag_ids mid en))` by
    metis_tac[SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET] >>
  drule_all abi_encode_framed_structural_member_dynamic_step_run_sizes >> strip_tac >>
  qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid) UNION {site}`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
  asm_rewrite_tac[] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Resume abi_encode_framed_structural_members_cons_run_sizes[compose]:
  `!i. FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i` by
    (qpat_assum `window_phase _ _ st ready {} [] s t` mp_tac >>
     simp_tac bool_ss [window_phase_def,
       abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     simp_tac (srw_ss()) [NoAsms, NOT_IN_EMPTY] >> metis_tac[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  `h1 = abi_member_head_size (EL k ats) /\ k < LENGTH ats` by
    (drule_all window_structural_members_inv_source >> strip_tac >>
     qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, window_member_prefix_def] >> metis_tac[]) >>
  `abi_encoder_member_span (TAKE (SUC k) infos) = abi_encoder_member_span (TAKE k infos) + h2 /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + h1` by
    (rpt (qpat_x_assum `!R. _` kall_tac) >>
     simp[TAKE_SUC, TAKE1_DROP, abi_encoder_member_span_def, MAP_APPEND, SUM_APPEND]) >>
  `window_alloca_sites func (frag_ids ready en) SUBSET window_alloca_sites func (frag_ids st en) /\
   window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def, SUBSET_DEF] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`mid`, `u`] >> asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!R. _` kall_tac) >>
  (conj_tac >- metis_tac[]) >>
  reverse conj_tac >- decide_tac >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`, `t`] >>
  simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (drule window_structural_member_envelope_frame >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF])) >>
  qpat_x_assum `ids SUBSET _` mp_tac >>
  qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Finalise abi_encode_framed_structural_members_cons_run_sizes
