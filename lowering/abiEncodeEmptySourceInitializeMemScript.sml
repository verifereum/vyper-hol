(* Source-free complex entry and cursor initialization. *)
Theory abiEncodeEmptySourceInitializeMem
Ancestors
  abiEncodeEmptySourceInput abiEncoderWindowStructuralMembers
  abiEncoderWindowMembers abiEncoderWindowContract abiEncoderWindowComplexMem
  abiEncoderWindow abiEncoderInput abiEncoderMembersDefs
  abiEncoderWindowPhaseFrameMem abiEncoderWindowMemFrame
  windowPhaseMem memContinuation valueEncoding valueEncodingProps contractABI
  abiCanonicalWindows abiDecodeRanges list rich_list arithmetic words
  abiEncoderWindowPhase abiEncoderRegisteredEffect abiEncoderProps
  freshWrites compileEnv fragExec venomMemDefs venomState finite_map pred_set
  emitHelperProps emitHelper allocaFootprint exprLoweringProps
  allocaSiteResource venomExecSemantics

Theorem empty_source_static_entry:
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
  abi_encoder_tuple_type at ats /\ ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs 0 d s.vs_memory /\
  window_member_cursor infos (Lit 0w) site slot sb 0 d
    (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs 0))
Proof
  strip_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_structural_members >> strip_tac >>
  simp[window_member_prefix_zero, window_member_cursor_def]
QED

Theorem empty_source_remaining_pre:
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  window_phase ctx func st mid ids outs s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func /\
  DISJOINT ids (window_alloca_sites func (frag_ids mid en)) /\
  eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) ==>
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 t.vs_memory /\
  eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv t /\ alloca_room ctx func t /\
  d + LENGTH (enc at av) <= t.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids mid en /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
  t.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  `abi_encoder_window_input ei at av sb 0 t.vs_memory` by
    metis_tac[empty_source_window_rebase] >>
  asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[not_fresh_at_mono]) >>
  (conj_tac >- decide_tac) >> rpt gen_tac >> strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids mid en` mp_tac >>
     simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `inst.inst_id NOTIN ids` by
    (fs[DISJOINT_DEF, EXTENSION, window_alloca_sites_def] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by
    (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     pure_rewrite_tac [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >> metis_tac[]
QED

Theorem empty_source_allocate_cursor[local]:
  emit_op ALLOCA [Lit 32w] st = (dp,mid) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (d,n) (b,sz)) /\
  d+n <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot. window_phase ctx func st mid {st.cs_next_id} [] s t /\
    window_member_cursor (infos : (abi_enc_info # num # num # bool) list)
      dp st.cs_next_id slot sb 0 d n mid t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32) /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[] >>
  drule_all window_emit_alloca32_phase_mem_frame >> strip_tac >>
  rename1 `FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32)` >>
  `mid.cs_next_id = SUC st.cs_next_id /\ ?x. dp = Var x /\ not_fresh_at mid x` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >>
     strip_tac >> conj_tac >- decide_tac >> metis_tac[]) >>
  `alloca_room ctx func t /\ window_alloca_growth s t` by
    metis_tac[window_phase_resources] >>
  `slot < dimword (:256)` by
    (`t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     decide_tac) >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
     venomMemDefs$regions_disjoint (d,n) (b,sz)` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (d,n) (slot,32)` by
    (irule window_alloca_growth_protected >>
     qexistsl_tac [`st.cs_next_id`, `{st.cs_next_id}`, `s`, `t`] >>
     asm_rewrite_tac [IN_SING]) >>
  qexistsl_tac [`t`, `slot`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_member_cursor_def] >> strip_tac >>
  asm_rewrite_tac [prim_recTheory.LESS_SUC_REFL] >>
  simp[NoAsms, venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem empty_source_initialize_store[local]:
  window_member_cursor infos dp site slot sb 0 d n st s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  emit_void MSTORE [dp; Lit (n2w (window_member_head_size infos))] st = ((),ready) /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. window_phase ctx func st ready {site} [] s u /\
    window_member_cursor infos dp site slot sb 0 d n ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    mem_cont_sim ctx func s u /\ window_mem_frame ctx func s u
Proof
  strip_tac >>
  `eval_operand dp s = SOME (n2w slot) /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ slot < dimword (:256)` by
    fs[window_member_cursor_def] >>
  `slot+32 <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `eval_operand (Lit (n2w (window_member_head_size infos))) s =
     SOME (n2w (window_member_head_size infos))` by simp[eval_operand_def] >>
  drule_all window_cursor_store_phase_mem_frame >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND, cs_extends_def] >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_member_cursor_phase >>
      qexistsl_tac [`ctx`, `func`, `{site}`, `[]`, `s`, `st`] >> asm_rewrite_tac[]) >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem empty_source_initialization_code:
  fn_has_code st en func /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w h)] mid = ((),ready) /\
  ci_mono ready en ==>
  emit_op ALLOCA [Lit 32w] st = (buf.buf_operand,mid) /\
  ci_mono st mid /\ ci_mono mid ready /\
  fn_has_code st mid func /\ fn_has_code mid ready func /\
  fn_has_code mid en func /\ fn_has_code ready en func /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  st.cs_next_id IN window_alloca_sites func (frag_ids st en)
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit 32w] st = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  `ci_mono st mid /\ ci_mono mid ready` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends st mid /\ cs_extends mid ready /\ cs_extends ready en` by
    fs[ci_mono_def] >>
  `fn_has_code st mid func /\ fn_has_code mid ready func /\
   fn_has_code mid en func /\ fn_has_code ready en func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `fn_has_code st mid func` mp_tac >>
     simp_tac bool_ss [fragExecTheory.fn_has_code_def] >> strip_tac >>
     gvs[IS_PREFIX_APPEND] >> irule fragExecTheory.lookup_block_fn_insts >>
     goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  asm_rewrite_tac[] >>
  `mid.cs_next_id = SUC st.cs_next_id` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `st.cs_next_id < en.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
  goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]
QED

Theorem empty_source_initialize_phase:
  abi_encoder_admissible (AbiComplex infos) /\
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb 0 d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
    mem_cont_sim ctx func s u /\ window_mem_frame ctx func s u
Proof
  strip_tac >> drule_all empty_source_initialization_code >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint
      (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (qpat_x_assum `_ IN window_alloca_sites _ _` mp_tac >>
     simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def] >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     metis_tac[]) >>
  drule_all empty_source_allocate_cursor >>
  disch_then (qspecl_then [`sb`, `infos`] strip_assume_tac) >>
  `alloca_inv t /\ alloca_room ctx func t` by
    metis_tac[window_phase_resources] >>
  `~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_control] >>
  drule_all empty_source_initialize_store >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_phase_chain >>
      qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >>
      simp[] >> metis_tac[ci_mono_def]) >>
  metis_tac[mem_cont_sim_trans, window_mem_frame_trans]
QED

Theorem empty_source_initialize_members:
  abi_encoder_admissible (AbiComplex infos) /\
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_tuple_type at ats /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    mem_cont_sim ctx func s u /\ window_mem_frame ctx func s u /\
    (abi_encoder_admissible (AbiComplex infos) /\
     abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 u.vs_memory /\
     eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d) /\
     (!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x) /\
     fn_has_code ready en func /\ fn_inst_ids_distinct func /\
     alloca_inv u /\ alloca_room ctx func u /\
     d + LENGTH (enc at (ListV avs)) <= u.vs_alloca_next /\
     venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
     (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id IN frag_ids ready en /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
       sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
       venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
     ~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
     u.vs_inst_idx = LENGTH ready.cs_current_insts) /\
    abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
    window_member_head_size infos = head_lengths ats 0 /\
    window_member_prefix infos ats avs 0 d u.vs_memory /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb 0 d
      (LENGTH (enc at (ListV avs))) ready u /\
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at slot u.vs_memory = n2w (window_member_tail infos ats avs 0)) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >> drule_all empty_source_initialize_phase >> strip_tac >>
  drule_all empty_source_initialization_code >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `st.cs_next_id < ready.cs_next_id` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids ready en))` by
    (simp[NoAsms, DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
       abiEncoderPropsTheory.frag_ids_def] >> simp[]) >>
  `eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  drule_all empty_source_remaining_pre >> strip_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_structural_members >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >>
  (conj_tac >- (irule window_member_prefix_zero >> asm_rewrite_tac[])) >>
  (conj_tac >- asm_rewrite_tac[window_member_tail_def, abi_tuple_tails_def,
      TAKE_0, MAP, FLAT, LENGTH, ADD_CLAUSES]) >>
  gen_tac >> disch_tac >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     strip_tac >> rpt gen_tac >> simp[NoAsms] >> strip_tac >>
     qpat_x_assum `i = _` SUBST_ALL_TAC >>
     qpat_x_assum `FLOOKUP _ _ = SOME (b,sz)` mp_tac >>
     asm_rewrite_tac[] >> simp[NoAsms]) >>
  drule window_phase_effect >> strip_tac >>
  drule window_registered_sizes_transport >>
  disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]
QED
