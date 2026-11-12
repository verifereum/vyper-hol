(* Iteration of source-free ABI complex members. *)
Theory abiEncodeEmptySourceMembersMem
Ancestors
  abiEncodeEmptySourceMemberLayout abiEncodeEmptySourceMemberTransportMem
  abiEncodeEmptySourceChildMem abiEncodeEmptySourceInput abiEncoderInput abiEncoderBufferFrame
  abiEncoderWindowPhaseFrameMem abiEncoderWindowMemFrame memContinuation
  abiEncoderWindowMembersMem abiEncoderWindowStructuralMembers abiEncoderSourceAggregate
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderWindowMembers
  compileEnv fragExec freshWrites venomState
  words list rich_list arithmetic pred_set

Theorem empty_source_member_source_prepare[local]:
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
   fn_has_code st en func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ alloca_room ctx func s /\
   d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)) /\
  emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?t. window_phase ctx func st ready {} [] s t /\
   ((abi_encoder_admissible (AbiComplex infos) /\
     abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 t.vs_memory /\
     eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) /\
     (!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x) /\
     fn_has_code ready en func /\ fn_inst_ids_distinct func /\
     alloca_inv t /\ alloca_room ctx func t /\
     d + LENGTH (enc at (ListV avs)) <= t.vs_alloca_next /\
     venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
     (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id IN frag_ids ready en /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
       sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
       venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
     ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
     t.vs_inst_idx = LENGTH ready.cs_current_insts) /\
    abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
    window_member_head_size infos = head_lengths ats 0 /\
    window_member_prefix infos ats avs k d t.vs_memory /\
    window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) ready t /\
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k))) /\
   eval_operand child_src t = SOME (n2w (sb+so)) /\
   (!x. child_src = Var x ==> not_fresh_at ready x) /\
   (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
        !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
   mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[NoAsms, eval_operand_def] >>
  drule_all window_emit_add_phase_mem_frame >> strip_tac >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >> drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >>
     pure_rewrite_tac[NOT_IN_EMPTY, FALSITY, AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP] >>
     metis_tac[]) >>
  drule_all empty_source_members_pure_phase >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[word_add_n2w]
QED

Theorem empty_source_static_member_advance[local]:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ k < LENGTH infos /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  ~is_dynamic (EL k ats) /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  window_phase ctx func st mid ids
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
      LENGTH (enc (EL k ats) (EL k avs)))] s t /\
  mem_bytes_at (d+SUM (MAP abi_member_head_size (TAKE k ats)))
    (LENGTH (enc (EL k ats) (EL k avs))) t.vs_memory = enc (EL k ats) (EL k avs) /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN ids /\
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)) ==>
  window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k)))
Proof
  strip_tac >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule empty_source_member_static_prefix_frame >> asm_rewrite_tac[] >>
     metis_tac[]) >>
  conj_tac >- (irule window_structural_member_prefix_static_step >> asm_rewrite_tac[]) >>
  strip_tac >>
  `site NOTIN ids /\
   mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by metis_tac[] >>
  `FLOOKUP s.vs_allocas site = SOME (slot,32) /\
   venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32)` by
    metis_tac[abiEncoderWindowMembersTheory.window_member_cursor_def] >>
  `venomMemDefs$regions_disjoint (slot,32)
    (d+SUM (MAP abi_member_head_size (TAKE k ats)),
     LENGTH (enc (EL k ats) (EL k avs)))` by
    (drule_all empty_source_member_output_bounds >> strip_tac >>
     drule_all empty_source_member_total_bounds >> strip_tac >>
     qpat_x_assum `~is_dynamic _ ==> _` drule >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (slot,32)` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all empty_source_member_static_cursor_frame >> strip_tac >>
  drule_all abiEncoderWindowMembersTheory.window_member_tail_step >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem empty_source_dynamic_member_advance[local]:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ k < LENGTH infos /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  is_dynamic (EL k ats) /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  window_phase ctx func st mid ids
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
     (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
  mem_bytes_at (d+window_member_tail infos ats avs k)
    (LENGTH (enc (EL k ats) (EL k avs))) t.vs_memory = enc (EL k ats) (EL k avs) /\
  mem_word_at (d+SUM (MAP abi_member_head_size (TAKE k ats))) t.vs_memory =
    n2w (window_member_tail infos ats avs k) /\
  mem_word_at slot t.vs_memory =
    n2w (window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs))) ==>
  window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
  mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))
Proof
  strip_tac >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule empty_source_member_dynamic_prefix_frame >> asm_rewrite_tac[] >> metis_tac[]) >>
  conj_tac >- (irule window_structural_member_prefix_dynamic_step >> asm_rewrite_tac[]) >>
  drule_all abiEncoderWindowMembersTheory.window_member_tail_step >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem empty_source_dynamic_member_layout[local]:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 /\ is_dynamic (EL k ats) /\
  alloca_room ctx func s /\ d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  slot < dimword (:256) /\
  venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32) ==>
  d+SUM (MAP abi_member_head_size (TAKE k ats)) < dimword (:256) /\
  d+SUM (MAP abi_member_head_size (TAKE k ats))+32 <= s.vs_alloca_next /\
  (d+SUM (MAP abi_member_head_size (TAKE k ats))+32 <= slot \/
   slot+32 <= d+SUM (MAP abi_member_head_size (TAKE k ats))) /\
  venomMemDefs$regions_disjoint
    (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))
    (d+SUM (MAP abi_member_head_size (TAKE k ats)),32) /\
  venomMemDefs$regions_disjoint
    (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs))) (slot,32)
Proof
  strip_tac >> drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats))+32 <= window_member_head_size infos /\
   window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  `d+LENGTH (enc at (ListV avs)) < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt, LESS_EQ_LESS_TRANS] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (slot,32)` mp_tac >>
  pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [window_member_tail_def]) >>
  pure_rewrite_tac[window_member_tail_def] >> decide_tac
QED

Theorem empty_source_static_member_run[local]:
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
   fn_has_code st en func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ alloca_room ctx func s /\
   d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    site NOTIN window_alloca_sites func (frag_ids st en) /\
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)) /\
  k < LENGTH infos /\ EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\
  (!dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
        LENGTH (enc (EL k ats) (EL k avs)))] s t /\
    window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))) /\
    (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all empty_source_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  qpat_x_assum `ats' = ats` SUBST_ALL_TAC >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by decide_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[] >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
     LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (qpat_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
  `d+SUM (MAP abi_member_head_size (TAKE k ats)) +
     LENGTH (enc (EL k ats) (EL k avs)) <= s.vs_alloca_next` by decide_tac >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint
      (d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs))) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >> strip_tac >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `eval_operand (Lit (n2w (d+SUM (MAP abi_member_head_size (TAKE k ats))))) s =
     SOME (n2w (d+SUM (MAP abi_member_head_size (TAKE k ats))))` by simp[NoAsms, eval_operand_def] >>
  `venomMemDefs$regions_disjoint (sb,0)
    (d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))` by
    simp[NoAsms, venomMemDefsTheory.regions_disjoint_def] >>
  `!x. child_src = Var x \/ Lit (n2w (d+SUM (MAP abi_member_head_size (TAKE k ats)))) = Var x ==>
    not_fresh_at st x` by (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  `abi_encoder_window_input ei (EL k ats) (EL k avs) sb 0 s.vs_memory` by metis_tac[] >>
  `eval_operand child_src s = SOME (n2w sb)` by
    (qpat_x_assum `eval_operand child_src s = _` mp_tac >> metis_tac[ADD_CLAUSES]) >>
  drule_all empty_source_static_child_run_frame >> strip_tac >>
  suspend "advance"
QED

Resume empty_source_static_member_run[advance]:
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def] >> metis_tac[]) >>
  drule_all empty_source_static_member_advance >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Finalise empty_source_static_member_run

Theorem empty_source_dynamic_member_run[local]:
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
   fn_has_code st en func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ alloca_room ctx func s /\
   d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    site NOTIN window_alloca_sites func (frag_ids st en) /\
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)) /\
  k < LENGTH infos /\ EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\
  (!dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
       (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
    window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k)) /\
    (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all empty_source_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  qpat_x_assum `ats' = ats` SUBST_ALL_TAC >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by decide_tac >>
  `is_dynamic (EL k ats)` by metis_tac[] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp_tac (srw_ss()) [EXISTS_MEM] >>
     qexists_tac `(ei,az,ms,T)` >> simp_tac (srw_ss()) [] >>
     metis_tac[MEM_EL]) >>
  `site NOTIN window_alloca_sites func (frag_ids st en) /\
   mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by metis_tac[] >>
  `?cursor. dp = Var cursor /\ not_fresh_at st cursor /\
    eval_operand (Var cursor) s = SOME (n2w slot) /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\ slot < dimword (:256) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32)` by
    metis_tac[window_member_cursor_def] >>
  qpat_x_assum `dp = Var cursor` SUBST_ALL_TAC >>
  drule_all empty_source_dynamic_member_layout >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  `window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  `d+window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    s.vs_alloca_next` by decide_tac >>
  suspend "child"
QED

Resume empty_source_dynamic_member_run[child]:
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs))) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >> strip_tac >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `eval_operand (Lit (n2w (d+window_member_tail infos ats avs k))) s =
    SOME (n2w (d+window_member_tail infos ats avs k))` by simp[NoAsms, eval_operand_def] >>
  `venomMemDefs$regions_disjoint (sb,0)
    (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))` by
    simp[NoAsms, venomMemDefsTheory.regions_disjoint_def] >>
  `!x. child_src = Var x \/ Lit (n2w (d+window_member_tail infos ats avs k)) = Var x ==>
    not_fresh_at st x` by (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  `abi_encoder_window_input ei (EL k ats) (EL k avs) sb 0 s.vs_memory` by metis_tac[] >>
  `eval_operand child_src s = SOME (n2w sb)` by
    (qpat_x_assum `eval_operand child_src s = _` mp_tac >> metis_tac[ADD_CLAUSES]) >>
  drule_all empty_source_dynamic_child_run_frame >> strip_tac >>
  suspend "advance"
QED

Resume empty_source_dynamic_member_run[advance]:
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _` kall_tac >>
  `!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (rpt gen_tac >>
     disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
     pure_rewrite_tac[IN_UNION, IN_SING] >>
     disch_then DISJ_CASES_TAC
     >- (qpat_x_assum `i IN window_alloca_sites _ _` mp_tac >>
         simp_tac (srw_ss()) [window_alloca_sites_def] >> metis_tac[]) >>
     qpat_x_assum `i = site` SUBST_ALL_TAC >>
     metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  drule_all empty_source_dynamic_member_advance >> strip_tac >>
  qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise empty_source_dynamic_member_run

(* Syntax-only abbreviations for the expanded invariant and child interface.
   These introduce no HOL constants. *)
val empty_member_inv = ``
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
   fn_has_code st en func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ alloca_room ctx func s /\
   d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k))``;
val empty_child_contract = ``
  !dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t``;

Theorem empty_source_member_step_envelope[local]:
  ^empty_member_inv /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,dyn) /\ abi_encoder_admissible ei /\
  ^empty_child_contract /\
  compile_abi_encode_child dst child_src ei dyn
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid))
    (window_alloca_sites func (frag_ids mid en)) /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    site NOTIN window_alloca_sites func (frag_ids st mid) /\
    DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
      (window_alloca_sites func (frag_ids mid en))) ==>
  ?t ids outs. ^(Term.subst [``s:venom_state`` |-> ``t:venom_state``,
      ``st:compile_state`` |-> ``mid:compile_state``, ``k:num`` |-> ``SUC k``] empty_member_inv) /\
    window_phase ctx func st mid ids outs s t /\
    ids SUBSET (window_alloca_sites func (frag_ids st en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  drule_all empty_source_members_restrict_end >> strip_tac >>
  reverse (Cases_on `dyn`)
  >- (`EXISTS (\(_,_,_,dyn). dyn) infos ==>
         site NOTIN window_alloca_sites func (frag_ids st mid) /\
         mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by metis_tac[] >>
      drule_all empty_source_static_member_run >> strip_tac >>
      suspend "static") >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[NoAsms, EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >>
     simp_tac (srw_ss()) [] >> metis_tac[MEM_EL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids st mid) /\
     mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by metis_tac[] >>
  drule_all empty_source_dynamic_member_run >> strip_tac >>
  suspend "dynamic"
QED

Resume empty_source_member_step_envelope[static]:
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _` kall_tac >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >> drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  drule_all empty_source_members_phase_advance >> strip_tac >>
  qexistsl_tac [`t`, `window_alloca_sites func (frag_ids st mid)`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
  drule_all empty_source_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  qpat_x_assum `ats' = ats` SUBST_ALL_TAC >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by decide_tac >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[] >>
  simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
  qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac
QED

Resume empty_source_member_step_envelope[dynamic]:
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _` kall_tac >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >> drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  `DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
     (window_alloca_sites func (frag_ids mid en))` by metis_tac[] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
     mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (disch_tac >> first_assum ACCEPT_TAC) >>
  drule_all empty_source_members_phase_advance >> strip_tac >>
  qexistsl_tac [`t`, `window_alloca_sites func (frag_ids st mid) UNION {site}`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET, SUBSET_REFL]) >>
  drule_all empty_source_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  qpat_x_assum `ats' = ats` SUBST_ALL_TAC >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by decide_tac >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[] >>
  simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Finalise empty_source_member_step_envelope

Theorem empty_source_members_cons_run[local]:
  ^empty_member_inv /\ DROP k infos = (ei,az,ms,dyn)::rest /\
  ^empty_child_contract /\
  compile_abi_encode_complex_elems dst src ((ei,az,ms,dyn)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid u. ^(Term.subst [``s:venom_state`` |-> ``u:venom_state``,
      ``st:compile_state`` |-> ``mid:compile_state``, ``k:num`` |-> ``SUC k``] empty_member_inv) /\
    DROP (SUC k) infos = rest /\
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
    mem_cont_sim ctx func s u /\ window_mem_frame ctx func s u
Proof
  strip_tac >>
  drule_all window_members_cons_context >> strip_tac >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode_child,
      cj 3 abiEncoderAppendTheory.cs_appends_abi_encode_mutual, cs_appends_def] >>
  `cs_extends st ready` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `fn_has_code ready en func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all empty_source_member_source_prepare >> strip_tac >>
  `k < LENGTH infos` by
    (`LENGTH (DROP k infos) = SUC (LENGTH rest)` by
       (pure_asm_rewrite_tac[] >> rewrite_tac[LENGTH]) >>
     qpat_x_assum `LENGTH (DROP k infos) = _` mp_tac >>
     pure_rewrite_tac[LENGTH_DROP] >> decide_tac) >>
  `EL k infos = (ei,az,ms,dyn) /\ DROP (SUC k) infos = rest` by
    (qspecl_then [`infos`, `k`] mp_tac DROP_EL_CONS >>
     asm_rewrite_tac[] >> simp_tac bool_ss [CONS_11, ADD1] >> metis_tac[]) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _` kall_tac >>
  `abi_encoder_admissible ei` by
    (qpat_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     simp_tac bool_ss [abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
       abiEncoderAdmissibleTheory.abi_encoder_members_admissible_every] >>
     simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(ei,az,ms,dyn)` mp_tac) >>
     simp_tac (srw_ss()) [NoAsms] >> metis_tac[MEM_EL]) >>
  suspend "step"
QED

Resume empty_source_members_cons_run[step]:
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> site < ready.cs_next_id` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ ready t` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready mid) SUBSET window_alloca_sites func (frag_ids ready en) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid)) (window_alloca_sites func (frag_ids mid en)) /\
   (EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids ready mid) /\
     DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en)))` by
    metis_tac[window_member_site_split] >>
  drule_all empty_source_member_step_envelope >> strip_tac >>
  suspend "package"
QED

Resume empty_source_members_cons_run[package]:
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _` kall_tac >>
  drule_all empty_source_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  qpat_x_assum `ats' = ats` SUBST_ALL_TAC >>
  `abi_encoder_member_span (TAKE (SUC k) infos) = abi_encoder_member_span (TAKE k infos) + ms /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + az` by
    (rpt (qpat_x_assum `!R. _` kall_tac) >>
     gvs[abiEncoderInputTheory.abi_encoder_member_span_def] >>
     simp[TAKE_SUC, TAKE1_DROP, MAP_APPEND, SUM_APPEND]) >>
  `window_alloca_sites func (frag_ids ready en) SUBSET window_alloca_sites func (frag_ids st en) /\
   window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def,
       SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  `mem_cont_sim ctx func s t'` by metis_tac[mem_cont_sim_trans] >>
  `window_mem_frame ctx func s t'` by metis_tac[window_mem_frame_trans] >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t'.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >>
     (impl_tac >- (first_x_assum (qspec_then `R` mp_tac) >> asm_rewrite_tac[])) >>
     rewrite_tac[]) >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  qexistsl_tac [`mid`, `t'`] >> asm_rewrite_tac[] >>
  (conj_tac >- (qpat_x_assum `compile_abi_encode_complex_elems _ _ rest _ _ _ _ = _` mp_tac >>
    asm_rewrite_tac[])) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`, `t`] >>
  simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (simp_tac (srw_ss()) [EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM e outs` >> PairCases_on `e` >>
     qpat_x_assum `EVERY _ outs` mp_tac >> simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(e0,e1)` mp_tac) >>
     simp_tac (srw_ss()) [NoAsms] >> asm_rewrite_tac[] >> decide_tac)) >>
  qpat_x_assum `ids SUBSET _` mp_tac >>
  qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Finalise empty_source_members_cons_run

Theorem empty_source_members_remaining_run[local]:
  ^empty_member_inv /\ DROP k (infos:(abi_enc_info # num # num # bool) list) = rest /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> ^empty_child_contract) /\
  compile_abi_encode_complex_elems dst src rest
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      ^(Term.subst [``s:venom_state`` |-> ``t:venom_state``,
        ``st:compile_state`` |-> ``en:compile_state``, ``k:num`` |-> ``LENGTH (infos:(abi_enc_info # num # num # bool) list)``] empty_member_inv) /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  map_every qid_spec_tac [`out`, `s`, `en`, `st`, `d`, `sb`, `slot`, `site`, `dp`,
    `dst`, `src`, `k`, `avs`, `ats`, `at`, `infos`, `func`, `ctx`, `rest`] >>
  Induct_on `rest`
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
      simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def,
        comp_return_def, pairTheory.PAIR_EQ] >> strip_tac >>
      `k = LENGTH infos` by
        (qpat_assum `window_member_prefix _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [window_member_prefix_def] >>
         strip_tac >> fs[DROP_EQ_NIL] >> decide_tac) >>
      qpat_x_assum `!ei az ms dyn. _` kall_tac >>
      qpat_x_assum `st = en` SUBST_ALL_TAC >>
      qpat_x_assum `k = LENGTH infos` SUBST_ALL_TAC >>
      qexists_tac `s` >> asm_rewrite_tac[] >>
      (conj_tac >- (irule window_phase_refl >> asm_rewrite_tac[])) >>
      simp[mem_cont_sim_refl, window_mem_frame_refl]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `^(Term.subst [``ei:abi_enc_info`` |-> ``h0:abi_enc_info``] empty_child_contract)` by
    (qpat_assum `!ei az ms dyn. _` (qspecl_then [`h0`, `h1`, `h2`, `h3`] mp_tac) >>
     rewrite_tac[MEM]) >>
  drule_all empty_source_members_cons_run >> strip_tac >>
  suspend "tail"
QED

Resume empty_source_members_remaining_run[tail]:
  `!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> ^empty_child_contract` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) (_::rest) ==> _` (qspecl_then [`ei`, `az`, `ms`, `dyn`] mp_tac) >>
     (impl_tac >- (rewrite_tac[MEM] >> disj2_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `!ctx func infos at ats avs k src dst dp site slot sb d st en s out. _`
    drule_all >> strip_tac >>
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  `window_mem_frame ctx func s t` by metis_tac[window_mem_frame_trans] >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >>
     (impl_tac >- (first_x_assum (qspec_then `R` mp_tac) >> asm_rewrite_tac[])) >>
     rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_phase_chain >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `mid`,
    `window_alloca_sites func (frag_ids mid en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `window_alloca_sites func (frag_ids mid en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Finalise empty_source_members_remaining_run

Theorem empty_source_initialized_members_run_frame:
  ^(Term.subst [``k:num`` |-> ``0:num``] empty_member_inv) /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> ^empty_child_contract) /\
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs) /\
      (EXISTS (\(_,_,_,dyn). dyn) infos ==>
        mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs)))) /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`k` |-> `0`, `rest` |-> `infos`] empty_source_members_remaining_run) >>
  pure_rewrite_tac [DROP_0, TAKE_0, MAP, SUM, abiEncoderInputTheory.abi_encoder_member_span_def] >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "complete"
QED

Resume empty_source_initialized_members_run_frame[complete]:
  `LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs` by
    (qpat_assum `window_member_prefix _ _ _ _ _ t.vs_memory` mp_tac >>
     simp_tac bool_ss [window_member_prefix_def] >> metis_tac[]) >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (irule abi_encoder_tuple_type_encoding >> asm_rewrite_tac[]) >>
  `mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs)` by
    metis_tac[window_structural_member_prefix_complete] >>
  `window_member_tail infos ats avs (LENGTH infos) = LENGTH (enc at (ListV avs))` by
    (`TAKE (LENGTH infos) ats = ats /\ TAKE (LENGTH infos) avs = avs` by
       metis_tac[TAKE_LENGTH_ID] >>
     drule window_structural_member_tuple_length >>
     pure_asm_rewrite_tac[window_member_tail_def] >> metis_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  disch_tac >>
  qpat_x_assum `_ ==> mem_word_at slot t.vs_memory = _` drule >>
  asm_rewrite_tac[]
QED

Finalise empty_source_initialized_members_run_frame
