(* Transport of expanded source-free structural member invariants. *)
Theory abiEncodeEmptySourceMemberTransportMem
Ancestors
  abiEncodeEmptySourceInitializeMem abiEncodeEmptySourceInput
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers
  abiEncoderWindowContract abiEncoderWindowPhase abiEncoderRegisteredEffect
  abiEncoderProps freshWrites venomState venomMemDefs list rich_list
  arithmetic pred_set finite_map

Theorem empty_source_members_restrict_end:
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
  fn_has_code st mid func /\ mid.cs_next_id <= en.cs_next_id ==>
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
   fn_has_code st mid func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ alloca_room ctx func s /\
   d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k))
Proof
  strip_tac >> asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids st mid` mp_tac >>
     simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem empty_source_members_phase_advance:
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
  window_phase ctx func st mid ids outs s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func /\ DISJOINT ids (window_alloca_sites func (frag_ids mid en)) /\
  window_member_prefix infos ats avs j d t.vs_memory /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs j)) ==>
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 t.vs_memory /\
   eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
   fn_has_code mid en func /\ fn_inst_ids_distinct func /\
   alloca_inv t /\ alloca_room ctx func t /\
   d + LENGTH (enc at (ListV avs)) <= t.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids mid en /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs j d t.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) mid t /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs j))
Proof
  strip_tac >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  drule_all empty_source_remaining_pre >> strip_tac >>
  asm_rewrite_tac[] >>
  metis_tac[window_member_cursor_phase]
QED

Theorem empty_source_members_pure_phase:
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
  window_phase ctx func st mid {} [] s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func ==>
  (abi_encoder_admissible (AbiComplex infos) /\
   abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 t.vs_memory /\
   eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
   fn_has_code mid en func /\ fn_inst_ids_distinct func /\
   alloca_inv t /\ alloca_room ctx func t /\
   d + LENGTH (enc at (ListV avs)) <= t.vs_alloca_next /\
   venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at (ListV avs))) /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids mid en /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
     venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
   ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts) /\
  abi_encoder_tuple_type at ats /\ LIST_REL abi_encoder_structural_valid ats avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d t.vs_memory /\
  window_member_cursor infos dp site slot sb 0 d (LENGTH (enc at (ListV avs))) mid t /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k))
Proof
  strip_tac >>
  `!q n. mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory` by
    (rpt gen_tac >> irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{}`, `[]`] >> simp[] >> metis_tac[window_phase_effect]) >>
  `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
    (simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >> asm_rewrite_tac[]) >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (asm_rewrite_tac[window_member_prefix_def] >>
     fs[window_member_prefix_def] >> metis_tac[]) >>
  irule empty_source_members_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`{}`, `k`, `[]`, `s`, `st`] >> asm_rewrite_tac[] >> simp[]
QED
