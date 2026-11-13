(* Framed source-free ABI encoder execution. *)
Theory abiEncodeEmptySourceMemory
Ancestors
  valueEncodingDefs
  abiEncodeEmptySourceCopyMem abiEncodeEmptySourceInitializeMem
  abiEncodeEmptySourceMembersMem abiEncodeEmptySourceChildMem
  abiEncoderWindowComplexMem abiEncoderWindowComplex abiEncoderWindowStructuralMembers
  abiEncoderWindowMembers abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderWindow abiEncoderInput abiEncoderMembersDefs abiEncoderSourceAggregate
  abiEncoderWindowMemFrame abiEncoderWindowPhaseFrameMem memContinuation
  abiEncoderOpenInput abiEncoderProps abiEncoderAdmissible exprLoweringProps compileEnv fragExec emitHelperProps
  valueEncoding contractABI venomState list rich_list words arithmetic pred_set

(* Syntax-only expansion of the zero-capacity precondition, with only the
   source-frontier inequality omitted. *)
val empty_pre = ``
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts``;
val empty_recursive = ``
  !dst src st out en ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\ ^empty_pre ==>
    ?t. window_strong_result ctx func st en out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t``;

Theorem empty_source_complex_run_frame[local]:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> ^empty_recursive) ==>
  !dst src st out en ctx func s at av sb d.
    compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,en) /\
    ^(Term.subst [``ei:abi_enc_info`` |-> ``AbiComplex infos``] empty_pre) ==>
    ?t. window_strong_result ctx func st en out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> metis_tac[]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >> Cases_on `infos`
  >- suspend "empty" >>
  rename1 `h::rest` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) (h::rest)`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume empty_source_complex_run_frame[empty]:
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def, comp_return_def,
    pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `st = en` SUBST_ALL_TAC >>
  `enc at (ListV avs) = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> strip_tac >>
     gvs[abi_encoder_tuple_type_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >>
  simp_tac bool_ss [mem_cont_sim_refl, window_mem_frame_refl, AND_CLAUSES] >>
  irule window_complex_phase_result >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms, LENGTH, mem_bytes_at_def, eval_operand_def] >>
  (conj_tac >- (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def,
     abiEncoderPropsTheory.frag_ids_def] >> rpt strip_tac >> decide_tac)) >>
  (conj_tac >- (qpat_x_assum `Lit 0w = out` (SUBST1_TAC o SYM) >>
     simp[eval_operand_def])) >>
  irule window_phase_refl >> asm_rewrite_tac[]
QED

Resume empty_source_complex_run_frame[static]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,last)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def, LET_THM] >>
  simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_x_assum `last = en` SUBST_ALL_TAC >>
  drule_all empty_source_static_entry >>
  disch_then (qspecl_then [`st`, `0`, `0`, `d`] strip_assume_tac) >>
  drule_all empty_source_initialized_members_run_frame >> strip_tac >>
  suspend "static_finish"
QED

Resume empty_source_complex_run_frame[static_finish]:
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def] >> rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` mp_tac >>
     disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  qpat_x_assum `!R. _` (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_dynamic_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    metis_tac[abiEncoderOpenInputTheory.abi_encoder_structural_list_layout] >>
  `SUM (MAP2 abi_member_tail_size ats avs) = 0` by
    (irule abiEncoderComplexDynamicTheory.abi_encoder_static_tuple_tails >>
     metis_tac[]) >>
  `LENGTH (enc at (ListV avs)) = window_member_head_size infos` by
    (drule abi_encoder_tuple_type_encoding >>
     disch_then (qspec_then `avs` mp_tac) >> asm_rewrite_tac[] >>
     disch_then SUBST1_TAC >>
     drule abiEncoderOpenInputTheory.abi_encoder_open_tuple_length >>
     asm_rewrite_tac[] >> simp_tac bool_ss [abiDecodeRangesTheory.head_lengths_acc] >> decide_tac) >>
  `~any_dynamic ats` by metis_tac[] >>
  qpat_x_assum `Lit _ = out` (SUBST_ALL_TAC o SYM) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_complex_phase_result >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms, eval_operand_def] >>
  qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, UNION_EMPTY]
QED

Resume empty_source_complex_run_frame[dynamic]:
  asm_rewrite_tac[] >> qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocated)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))] allocated` >>
  rename1 `emit_void MSTORE _ allocated = (unit,ready)` >> Cases_on `unit` >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 buf.buf_operand ready` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,load)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_x_assum `(\(_,cs'). _) _ = _` mp_tac >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms] >> strip_tac >>
  `ci_mono ready load` by
    (qpat_assum `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (qpat_x_assum `!ei az ms dyn. _` kall_tac) >>
     metis_tac[cj 3 ci_mono_compile_abi_encode, pairTheory.SND]) >>
  `ci_mono load en` by
    (qspecl_then [`MLOAD`, `[buf.buf_operand]`, `load`] mp_tac ci_mono_emit_op >>
     asm_rewrite_tac[pairTheory.SND]) >>
  `ci_mono ready en` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all empty_source_initialize_members >> strip_tac >>
  `fn_has_code ready load func /\ fn_has_code load en func` by
    (rpt (qpat_x_assum `!ei az ms dyn. _` kall_tac) >>
     metis_tac[fn_has_code_split, ci_mono_def]) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids ready load /\
     FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id IN frag_ids ready en` by
       (qpat_assum `ci_mono load en` mp_tac >>
        qpat_x_assum `_ IN frag_ids ready load` mp_tac >>
        simp_tac (srw_ss()) [NoAsms, abiEncoderPropsTheory.frag_ids_def, ci_mono_def] >>
        rpt strip_tac >> decide_tac) >>
     qpat_x_assum `!inst b sz. _ /\ _ /\ inst.inst_id IN frag_ids ready en /\ _ ==> _` drule_all >>
     simp_tac bool_ss []) >>
  qpat_x_assum `!inst b sz. _ /\ _ /\ inst.inst_id IN frag_ids ready en /\ _ ==> _` kall_tac >>
  drule_all empty_source_initialized_members_run_frame >> strip_tac >>
  suspend "dynamic_finish"
QED

Resume empty_source_complex_run_frame[dynamic_finish]:
  qpat_x_assum `!ei az ms dyn. _` kall_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def] >> rpt strip_tac >>
     qpat_x_assum `!inst b sz. _ /\ _ /\ inst.inst_id IN frag_ids st en /\ _ ==> _` mp_tac >>
     disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_x_assum `!R. (!i b sz. _ /\ FLOOKUP s.vs_allocas i = _ ==> _) ==> _`
       (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >>
     qpat_x_assum `!R. _`
       (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     asm_rewrite_tac[]) >>
  drule_all empty_source_initialization_code >> strip_tac >>
  `ci_mono st ready` by
    (qpat_assum `ci_mono st allocated` mp_tac >>
     qpat_assum `ci_mono allocated ready` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [ci_mono_def] >>
     metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  qpat_x_assum `window_phase ctx func ready load _ _ u t` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs)))` by
    (qpat_x_assum `EXISTS _ infos ==> mem_word_at slot t.vs_memory = _` mp_tac >>
     asm_rewrite_tac[]) >>
  drule_all window_complex_dynamic_finish_mem >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[] >> metis_tac[]
QED

Finalise empty_source_complex_run_frame

Theorem empty_source_admissible_mutual_frame[local]:
  (!ei. abi_encoder_admissible ei ==> ^empty_recursive) /\
  (!infos. abi_encoder_members_admissible infos ==>
    EVERY (\(ei,_,_,_). ^empty_recursive) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[abi_encoder_window_word_iff])
  >- suspend "copy"
  >- (rpt strip_tac >> gvs[abi_encoder_window_bytes_iff])
  >- (rpt strip_tac >>
      qpat_x_assum `abi_encoder_window_input (AbiDynArray _ _ _ _) _ _ _ _ _` mp_tac >>
      simp[abi_encoder_window_array_iff])
  >- suspend "complex"
  >- simp[EVERY_DEF] >>
  simp_tac bool_ss [abi_encoder_admissible_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  metis_tac[]
QED

Resume empty_source_admissible_mutual_frame[copy]:
  rpt strip_tac >>
  `sz = 0` by gvs[abi_encoder_window_copy_iff] >> gvs[] >>
  drule_all empty_source_copy_run_mem >> simp_tac bool_ss []
QED

Resume empty_source_admissible_mutual_frame[complex]:
  gen_tac >> strip_tac >> strip_tac >>
  `abi_encoder_members_admissible infos` by fs[abi_encoder_admissible_def] >>
  first_x_assum drule >> strip_tac >>
  `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> ^empty_recursive` by
    (fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  drule empty_source_complex_run_frame >> simp_tac bool_ss []
QED

Finalise empty_source_admissible_mutual_frame

Theorem compile_abi_encode_to_buf_empty_source_strong_mem_frame:
  !ei. ^empty_recursive
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (cj 1 empty_source_admissible_mutual_frame) >>
  simp_tac bool_ss []
QED
