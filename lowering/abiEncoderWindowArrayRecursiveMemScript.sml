(* Array body execution with same-witness safe child callbacks. *)
Theory abiEncoderWindowArrayRecursiveMem
Ancestors
  abiEncoderWindowArrayBodyMem abiEncoderWindowArrayBody abiEncoderWindowChild
  abiEncoderWindowArrayInvariant abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderWindowSequence abiEncoderWindowArrayLayout abiEncoderWindow
  abiEncoderRegisteredEffect abiEncoderWindowStructuralMembers abiEncoderArrayBodyCode
  abiEncoderArrayCode abiEncoderArrayDynamicMemory abiDecoderReentry abiEncoderAdmissible abiEncoderProps abiEncoder
  memContinuation windowTransitionMem freshWrites exprLoweringProps emitHelperProps compileEnv loweringStateRelDefs fragExec allocaFootprint instMemFrontier venomMemDefs finite_map
  valueEncoding valueEncodingDefs valueEncodingProps contractABI venomState words list pred_set arithmetic

Theorem window_array_element_run_mem:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
        mem_cont_sim ctx func s t) /\
  compile_abi_encode_to_buf child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+off,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_root_live_pre >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_child_transition >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_static_element_run_mem:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+32+j*asz)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
        mem_cont_sim ctx func s t) /\
  compile_abi_encode_static_info child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+32+j*asz) s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `abi_encoder_admissible (AbiDynArray ei asz msz F) /\
   abi_encoder_window_input (AbiDynArray ei asz msz F)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
    fs[abi_encoder_window_array_iff] >>
  `compile_abi_encode_to_buf child_dst child_src ei ready = (out,en)` by
    metis_tac[window_array_static_info_eq] >>
  `32+j*asz+LENGTH (enc ty (EL j avs)) <=
    LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule_all window_array_prefix_step_geometry >> strip_tac >>
     `j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <=
        LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
     drule window_array_layout >> strip_tac >> asm_rewrite_tac[] >>
     qpat_x_assum `j * _ + LENGTH _ <= _` mp_tac >> decide_tac) >>
  `eval_operand child_dst s = SOME (n2w (d+(32+j*asz)))` by asm_rewrite_tac[ADD_ASSOC] >>
  drule_all window_array_element_run_mem >> strip_tac >>
  qexists_tac `t` >> full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_prefix_static_advance >>
  `abi_encoder_array_prefix ty avs j d t.vs_memory` by
    (irule window_array_static_prefix_frame >> metis_tac[]) >>
  `mem_bytes_at (d+32+j*abi_member_head_size ty)
      (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  metis_tac[]
QED

Theorem window_array_static_body_run_mem:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ fn_has_code st en func /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
        mem_cont_sim ctx func s t) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    eval_operand out t = SOME (n2w j) /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `abi_encoder_static_leaf ei` by fs[window_array_root_def, Once abi_encoder_admissible_def] >>
  drule_all abi_encode_array_static_body_context >> strip_tac >> gvs[] >>
  `?p. window_phase ctx func st prepared {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at prepared x) /\
    mem_cont_sim ctx func s p` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all window_array_addresses_phase_mem >> metis_tac[]) >>
  `window_array_transition ctx func st {} [] s p` by metis_tac[window_array_pure_phase_transition] >>
  `window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d p` by
    (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF]) >>
  `abi_encoder_array_prefix ty avs j d p.vs_memory` by
    (irule window_array_prefix_registered_frame >> reverse conj_tac >- metis_tac[window_array_root_def] >>
     qexistsl_tac [`{}`, `[]`, `s`] >> asm_rewrite_tac[EVERY_DEF, NOT_IN_EMPTY] >>
     metis_tac[window_array_root_def, window_array_transition_effect, window_array_transition_resources]) >>
  `window_alloca_sites func (frag_ids prepared en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >> simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `window_alloca_sites func (frag_ids prepared en) SUBSET ids` by metis_tac[SUBSET_TRANS] >>
  `st.cs_next_var <= prepared.cs_next_var /\ ~p.vs_halted /\
   p.vs_current_bb = prepared.cs_current_bb /\ p.vs_inst_idx = LENGTH prepared.cs_current_insts /\
   (!x. SND (FST coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at prepared x)` by
    (full_simp_tac bool_ss [window_phase_def] >> metis_tac[LESS_EQ_ADD]) >>
  drule_all window_array_static_element_run_mem >> strip_tac >>
  `eval_operand (FST (FST coords)) t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels, window_phase_strong_result]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\ mem_cont_sim ctx func s t` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{}`, `[]`, `prepared`, `window_alloca_sites func (frag_ids prepared en)`,
       `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`, `p`] >>
     simp_tac bool_ss [EMPTY_SUBSET, EVERY_DEF] >> metis_tac[window_phase_strong_result, SUBSET_REFL]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> reverse conj_tac >- metis_tac[window_phase_control] >>
  irule window_array_phase_transition >> conj_tac >- metis_tac[window_array_transition_sizes] >>
  qexists_tac `en` >> full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM]
QED

Theorem window_array_pure_cursor_facts[local]:
  window_array_cursor T owner dp site slot off sb cap d n s /\
  window_phase ctx func owner en {} [] s t ==>
  eval_operand dp t = SOME (n2w slot) /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  mem_word_at slot t.vs_memory = n2w off /\ mload slot t = n2w off /\
  slot < dimword (:256) /\ slot+32 <= t.vs_alloca_next
Proof
  strip_tac >>
  `window_array_transition ctx func owner {} [] s t` by
    metis_tac[window_array_pure_phase_transition] >>
  `eval_operand dp t = SOME (n2w slot)` by
    (irule window_array_transition_eval >> fs[window_array_cursor_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_array_cursor_def, window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `mem_word_at slot t.vs_memory = n2w off` by
    (irule EQ_TRANS >> qexists_tac `mem_word_at slot s.vs_memory` >>
     reverse conj_tac >- fs[window_array_cursor_def] >>
     irule window_array_transition_cursor_frame >>
     metis_tac[window_array_cursor_def, NOT_IN_EMPTY, EVERY_DEF]) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- fs[mload_def, mem_word_at_def, mem_bytes_at_def, LET_THM]
  >- fs[window_array_cursor_def] >>
  irule alloca_region_below_frontier >>
  `alloca_inv t` by metis_tac[window_phase_resources] >>
  fs[alloca_inv_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem window_array_dynamic_prepare_mem[local]:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  islot+32 <= s.vs_alloca_next /\ mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d n s /\
  abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
  abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
  fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
  st.cs_next_var <= addressed.cs_next_var /\ addressed.cs_next_var <= prepared.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?q. window_phase ctx func st prepared {} [] s q /\
    window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d q /\
    eval_operand (FST (FST coords)) q = SOME (n2w j) /\
    eval_operand (SND (FST coords)) q = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (SND (SND coords)) q = SOME (n2w (d+32+j*asz)) /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    eval_operand dp q = SOME (n2w slot) /\ FLOOKUP q.vs_allocas site = SOME (slot,32) /\
    mem_word_at slot q.vs_memory = n2w off /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      SND (SND coords) = Var x \/ FST ops = Var x \/ SND ops = Var x \/
      dp = Var x ==> not_fresh_at prepared x) /\ mem_cont_sim ctx func s q
Proof
  strip_tac >>
  `?p. window_phase ctx func st addressed {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at addressed x) /\
    mem_cont_sim ctx func s p` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all window_array_addresses_phase_mem >> metis_tac[]) >>
  drule_all window_array_pure_cursor_facts >> strip_tac >>
  `alloca_inv p /\ alloca_room ctx func p /\ ~p.vs_halted /\
   p.vs_current_bb = addressed.cs_current_bb /\
   p.vs_inst_idx = LENGTH addressed.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `!x. FST (SND coords) = Var x ==> not_fresh_at addressed x` by metis_tac[] >>
  drule_all window_array_tail_phase_mem >> strip_tac >>
  `window_phase ctx func st prepared {} [] s t /\ mem_cont_sim ctx func s t` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{}`, `[]`, `addressed`, `{}`, `[]`, `p`] >> simp[EVERY_DEF]) >>
  `window_array_transition ctx func st {} [] s t` by metis_tac[window_array_pure_phase_transition] >>
  `eval_operand dp t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
   mem_word_at slot t.vs_memory = n2w off` by metis_tac[window_array_pure_cursor_facts] >>
  qexists_tac `t` >> asm_rewrite_tac[ADD_ASSOC] >> rpt conj_tac
  >- (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  metis_tac[window_array_cursor_def, not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem window_array_dynamic_child_finish_mem[local]:
  window_array_transition ctx func owner child_ids [(b,n)] q r /\
  window_strong_result ctx func prepared child_end child_len ty av b q r /\
  mem_cont_sim ctx func q r /\ n = LENGTH (enc ty av) /\
  eval_operand idx q = SOME (n2w j) /\ eval_operand head q = SOME (n2w h) /\
  eval_operand offset q = SOME (n2w off) /\ eval_operand dp q = SOME (n2w slot) /\
  (!x. idx = Var x \/ head = Var x \/ offset = Var x \/ dp = Var x ==>
    not_fresh_at prepared x) /\
  abi_encode_child_suffix head dp offset child_len child_end = (ignored,en) /\
  fn_has_code child_end en func /\
  (!x. child_len = Var x ==> not_fresh_at child_end x) /\
  FLOOKUP q.vs_allocas site = SOME (slot,32) /\ site NOTIN child_ids /\
  h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= q.vs_alloca_next /\
  (h+32 <= slot \/ slot+32 <= h) /\
  venomMemDefs$regions_disjoint (b,n) (h,32) /\
  venomMemDefs$regions_disjoint (b,n) (slot,32) /\
  owner.cs_next_var <= prepared.cs_next_var /\
  prepared.cs_next_var <= child_end.cs_next_var ==>
  ?t. window_array_transition ctx func owner (child_ids UNION {site})
      [(h,32);(b,n)] q t /\
    mem_bytes_at b n t.vs_memory = enc ty av /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    eval_operand idx t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ mem_cont_sim ctx func q t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `window_phase ctx func prepared child_end
     (window_alloca_sites func (frag_ids prepared child_end)) [(b,n)] q r` by
    metis_tac[window_phase_strong_result] >>
  `eval_operand idx r = SOME (n2w j) /\ eval_operand head r = SOME (n2w h) /\
   eval_operand offset r = SOME (n2w off) /\ eval_operand dp r = SOME (n2w slot)` by
    (rpt conj_tac >> irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  `mem_bytes_at b n r.vs_memory = enc ty av /\ eval_operand child_len r = SOME (n2w n)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated] >>
  `!x. dp = Var x \/ child_len = Var x ==> not_fresh_at child_end x` by metis_tac[not_fresh_at_mono] >>
  `alloca_inv r /\ alloca_room ctx func r /\ ~r.vs_halted /\
   r.vs_current_bb = child_end.cs_current_bb /\ r.vs_inst_idx = LENGTH child_end.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `h+32 <= r.vs_alloca_next` by
    metis_tac[window_array_transition_resources, window_alloca_growth_frontier, LESS_EQ_TRANS] >>
  drule_all window_array_suffix_run_mem >> strip_tac >>
  `window_phase ctx func owner child_end child_ids [(b,n)] q r /\
   window_phase ctx func child_end en {site} [(h,32)] r t` by metis_tac[window_array_transition_phase] >>
  `window_phase ctx func owner en (child_ids UNION {site}) [(h,32);(b,n)] q t /\
   mem_cont_sim ctx func q t` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`child_ids`, `[(b,n)]`, `child_end`, `{site}`, `[(h,32)]`, `r`] >>
     simp[SUBSET_UNION] >> decide_tac) >>
  `mem_bytes_at b n t.vs_memory = mem_bytes_at b n r.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{site}`, `[(h,32)]`] >> simp[] >>
     metis_tac[window_array_transition_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `eval_operand idx t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels, not_fresh_at_mono]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> irule window_array_phase_transition >>
  conj_tac >- (gen_tac >> strip_tac >> metis_tac[window_array_transition_sizes]) >>
  qexists_tac `en` >> metis_tac[]
QED

Theorem window_array_dynamic_geometry[local]:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  j < LENGTH avs /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) ==>
  asz = abi_member_head_size ty /\ is_dynamic ty /\
  32+off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  d+32+j*asz < dimword (:256) /\ slot < dimword (:256) /\
  d+32+j*asz+32 <= s.vs_alloca_next /\
  (d+32+j*asz+32 <= slot \/ slot+32 <= d+32+j*asz) /\
  venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (d+32+j*asz,32) /\
  venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (slot,32)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by metis_tac[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ is_dynamic ty` by fs[abi_encoder_window_array_iff] >>
  `32+off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   j*abi_member_head_size ty+32 <= off` by
    (drule_all window_array_prefix_step_geometry >> disch_then (mp_tac o CONJUNCT1) >>
     asm_rewrite_tac[] >> strip_tac >> decide_tac) >>
  `d+LENGTH (enc (Array NONE ty) (ListV avs)) < dimword (:256) /\
   d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next` by
    (full_simp_tac bool_ss [window_array_root_def, alloca_room_def] >> decide_tac) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_array_cursor _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_array_cursor_def, regions_disjoint_def] >>
  rpt strip_tac >> full_simp_tac arith_ss [] >> decide_tac
QED

Theorem window_array_dynamic_element_run_mem[local]:
  window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d q /\
  j < LENGTH avs /\ owner.cs_next_var <= prepared.cs_next_var /\
  window_alloca_sites func (frag_ids prepared child_end) SUBSET ids /\
  site NOTIN window_alloca_sites func (frag_ids prepared child_end) /\
  fn_has_code prepared child_end func /\ fn_has_code child_end en func /\
  prepared.cs_next_var <= child_end.cs_next_var /\
  eval_operand child_src q = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst q = SOME (n2w (d+(32+off))) /\
  eval_operand idx q = SOME (n2w j) /\ eval_operand head q = SOME (n2w h) /\
  eval_operand offset q = SOME (n2w off) /\ eval_operand dp q = SOME (n2w slot) /\
  (!x. child_src = Var x \/ child_dst = Var x \/ idx = Var x \/ head = Var x \/
    offset = Var x \/ dp = Var x ==> not_fresh_at prepared x) /\
  FLOOKUP q.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= q.vs_alloca_next /\
  (h+32 <= slot \/ slot+32 <= h) /\
  venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (h,32) /\
  venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (slot,32) /\
  32+off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~q.vs_halted /\ q.vs_current_bb = prepared.cs_current_bb /\
  q.vs_inst_idx = LENGTH prepared.cs_current_insts /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  compile_abi_encode_to_buf child_dst child_src ei prepared = (child_len,child_end) /\
  (!x. child_len = Var x ==> not_fresh_at child_end x) /\
  abi_encode_child_suffix head dp offset child_len child_end = (ignored,en) ==>
  ?t. window_array_transition ctx func prepared
      (window_alloca_sites func (frag_ids prepared child_end) UNION {site})
      [(h,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] q t /\
    mem_bytes_at (d+(32+off)) (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs) /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand idx t = SOME (n2w j) /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ mem_cont_sim ctx func q t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at prepared x` by metis_tac[] >>
  drule_all window_array_element_run_mem >> strip_tac >>
  `window_array_transition ctx func prepared
    (window_alloca_sites func (frag_ids prepared child_end))
    [(d+(32+off),LENGTH (enc ty (EL j avs)))] q t` by
    metis_tac[window_array_child_transition, LESS_EQ_REFL] >>
  `!x. idx = Var x \/ head = Var x \/ offset = Var x \/ dp = Var x ==>
    not_fresh_at prepared x` by metis_tac[] >>
  irule window_array_dynamic_child_finish_mem >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_encode_child_suffix _ _ _ _ _ = _` (irule_at Any) >>
  asm_rewrite_tac[LESS_EQ_REFL]
QED

Theorem window_array_dynamic_body_run_mem:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  islot+32 <= s.vs_alloca_next /\ mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ site IN ids /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\ fn_has_code st en func /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand out t = SOME (n2w j) /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ mem_cont_sim ctx func s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all window_array_dynamic_geometry >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  `st.cs_next_var <= addressed.cs_next_var /\ addressed.cs_next_var <= prepared.cs_next_var /\
   st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  drule_all window_array_dynamic_prepare_mem >> strip_tac >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >> simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET ids /\
   site NOTIN window_alloca_sites func (frag_ids prepared child_end)` by metis_tac[SUBSET_TRANS, SUBSET_DEF] >>
  `~q.vs_halted /\ q.vs_current_bb = prepared.cs_current_bb /\
   q.vs_inst_idx = LENGTH prepared.cs_current_insts` by metis_tac[window_phase_control] >>
  `d+32+j*asz+32 <= q.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_frontier, LESS_EQ_TRANS] >>
  `!x. child_len = Var x ==> not_fresh_at child_end x` by
    (qpat_x_assum `abi_decoder_operand_live _ child_len` mp_tac >> Cases_on `child_len` >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. SND (FST coords) = Var x \/ SND ops = Var x \/ FST (FST coords) = Var x \/
    SND (SND coords) = Var x \/ FST ops = Var x \/ dp = Var x ==> not_fresh_at prepared x` by metis_tac[] >>
  `eval_operand (SND ops) q = SOME (n2w (d+(32+off)))` by asm_rewrite_tac[ADD_ASSOC] >>
  drule_all window_array_dynamic_element_run_mem >> strip_tac >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t /\ mem_cont_sim ctx func s t` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{}`, `[]`, `prepared`, `window_alloca_sites func (frag_ids prepared child_end) UNION {site}`,
       `[(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))]`, `q`] >>
     asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF] >>
     metis_tac[window_array_transition_phase, UNION_SUBSET, SUBSET_UNION, SUBSET_TRANS]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_array_phase_transition >> conj_tac
     >- metis_tac[window_array_pure_phase_transition, window_array_transition_sizes] >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  qpat_x_assum `asz = _` SUBST_ALL_TAC >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  qexists_tac `t` >> full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_dynamic_prefix_finish >>
  qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` (irule_at Any) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  metis_tac[UNION_SUBSET, SUBSET_DEF, IN_SING]
QED
