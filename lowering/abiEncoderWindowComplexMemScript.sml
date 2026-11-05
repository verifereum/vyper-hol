(* Same-witness memory safety for complex encoder cursor phases. *)
Theory abiEncoderWindowComplexMem
Ancestors
  abiEncoderWindowComplex abiEncoderWindowMembersMem abiEncoderWindowStructuralMembers
  abiEncoderWindowMembers abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderWindow abiEncoderInput abiEncoderRegisteredEffect windowPhaseMem memContinuation
  allocaSiteResource exprLoweringProps venomMemDefs venomState finite_map pred_set
  compileEnv emitHelper valueEncoding valueEncodingProps contractABI list rich_list arithmetic words

Theorem window_complex_allocate_cursor_mem:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  emit_op ALLOCA [Lit 32w] st = (dp,mid) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) ==>
  ?t slot. window_phase ctx func st mid {st.cs_next_id} [] s t /\
    abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
      (ListV avs) sb cap d t /\
    window_member_cursor infos dp st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) mid t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  drule_all window_emit_alloca32_phase_mem >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id = SUC st.cs_next_id /\
    ?x. dp = Var x /\ not_fresh_at mid x` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[not_fresh_at_def]) >>
  `b < dimword (:256) /\ regions_disjoint (sb,cap) (b,32) /\
   regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,32)` by
    metis_tac[window_complex_cursor_protected] >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids mid en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
     (ListV avs) sb cap d t` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     (conj_tac >- fs[abi_encoder_window_pre_def]) >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `s`, `st`] >> simp[]) >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp[window_member_cursor_def] >> metis_tac[]
QED

Theorem window_complex_initialize_store_mem:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  window_member_cursor infos dp site slot sb cap d
    (LENGTH (enc at (ListV avs))) st s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  emit_void MSTORE [dp; Lit (n2w (window_member_head_size infos))] st = ((),ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func ==>
  ?u. window_phase ctx func st ready {site} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos dp site slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    mem_cont_sim ctx func s u
Proof
  strip_tac >>
  `eval_operand dp s = SOME (n2w slot) /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
   slot < dimword (:256) /\ regions_disjoint (sb,cap) (slot,32)` by
    fs[window_member_cursor_def] >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `slot+32 <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `eval_operand (Lit (n2w (window_member_head_size infos))) s =
     SOME (n2w (window_member_head_size infos))` by simp[eval_operand_def] >>
  drule_all window_cursor_store_phase_mem >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `DISJOINT {site} (window_alloca_sites func (frag_ids ready en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap u.vs_memory` by
    (irule window_alloca_growth_source >> qexistsl_tac [`{site}`, `[]`, `s`] >> simp[] >>
     `abi_encoder_registered_effect {site} [] s u /\ window_alloca_growth s u` by
       metis_tac[window_phase_effect, window_phase_resources] >>
     asm_rewrite_tac[] >> fs[abi_encoder_window_pre_def]) >>
  `eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     qexistsl_tac [`{site}`, `[]`, `s`, `st`] >> simp[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_member_cursor_phase >>
      qexistsl_tac [`ctx`, `func`, `{site}`, `[]`, `s`, `st`] >> simp[]) >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED
