(* Iteration of source-free ABI complex members. *)
Theory abiEncodeEmptySourceMembersMem
Ancestors
  abiEncodeEmptySourceMemberLayout abiEncodeEmptySourceMemberTransportMem
  abiEncodeEmptySourceChildMem abiEncoderBufferFrame
  abiEncoderWindowPhaseFrameMem abiEncoderWindowMemFrame
  abiEncoderWindowMembersMem abiEncoderWindowStructuralMembers
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
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
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
