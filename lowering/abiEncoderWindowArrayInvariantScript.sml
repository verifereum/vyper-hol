(* Control-free transitions for array backedges. *)
Theory abiEncoderWindowArrayInvariant
Ancestors
  abiEncoderWindowArrayLayout abiEncoderWindowPhase abiEncoderWindowChild
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderExtendSim
  exprLoweringProps venomState finite_map pred_set list abiEncoderArrayPrefix

Definition window_sizes32_def:
  window_sizes32 ids (s:venom_state) <=>
    !i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32
End

Definition window_array_transition_def:
  window_array_transition ctx func owner ids outs s t <=>
    abi_encoder_extend_sim ctx func s t /\
    abi_encoder_registered_effect ids outs s t /\
    window_alloca_growth s t /\ alloca_inv t /\ alloca_room ctx func t /\
    (!x w. not_fresh_at owner x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    ~t.vs_halted /\ t.vs_labels = s.vs_labels /\
    (!R. window_sizes32 R s ==> window_sizes32 R t)
End

Theorem window_array_transition_refl:
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted ==>
  window_array_transition ctx func owner ids outs s s
Proof
  simp[window_array_transition_def, abi_encoder_extend_sim_refl,
    abi_encoder_registered_effect_refl, window_alloca_growth_refl]
QED

Theorem window_array_transition_trans:
  window_array_transition ctx func owner ids outs s t /\
  window_array_transition ctx func owner ids outs t u ==>
  window_array_transition ctx func owner ids outs s u
Proof
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  `abi_encoder_registered_effect ids outs s u /\ window_alloca_growth s u` by
    (irule window_alloca_growth_sequence >> metis_tac[SUBSET_REFL]) >>
  asm_rewrite_tac[] >> metis_tac[abi_encoder_extend_sim_trans]
QED

Theorem window_array_transition_resources:
  window_array_transition ctx func owner ids outs s t ==>
  alloca_inv t /\ alloca_room ctx func t /\ window_alloca_growth s t
Proof
  simp[window_array_transition_def]
QED

Theorem window_array_transition_effect:
  window_array_transition ctx func owner ids outs s t ==>
  abi_encoder_registered_effect ids outs s t
Proof
  simp[window_array_transition_def]
QED

Theorem window_array_transition_sizes:
  window_array_transition ctx func owner ids outs s t /\ window_sizes32 R s ==>
  window_sizes32 R t
Proof
  simp[window_array_transition_def] >> metis_tac[]
QED

Theorem window_array_transition_vars:
  window_array_transition ctx func owner ids outs s t /\
  not_fresh_at owner x /\ lookup_var x s = SOME w ==>
  lookup_var x t = SOME w
Proof
  simp[window_array_transition_def] >> metis_tac[]
QED

Theorem window_array_transition_phase:
  window_array_transition ctx func owner ids outs s t /\
  t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts ==>
  window_phase ctx func owner en ids outs s t
Proof
  simp[window_array_transition_def, window_phase_def]
QED

Theorem window_array_transition_source:
  window_array_transition ctx func owner ids outs s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) outs /\
  (!id b sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_source >>
  metis_tac[window_array_transition_effect]
QED

Theorem window_array_transition_cursor_frame:
  window_array_transition ctx func owner ids outs s t /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site NOTIN ids /\
  EVERY (\r. venomMemDefs$regions_disjoint (slot,32) r) outs ==>
  mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at slot 32 t.vs_memory = mem_bytes_at slot 32 s.vs_memory` by
    (irule abi_encoder_window_effect_parent >>
     metis_tac[window_array_transition_effect, window_array_transition_resources]) >>
  fs[valueEncodingTheory.mem_word_at_def, GSYM valueEncodingTheory.mem_bytes_at_def]
QED

Definition window_array_root_def:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s <=>
    abi_encoder_admissible (AbiDynArray ei asz msz active) /\
    abi_encoder_window_input (AbiDynArray ei asz msz active)
      (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at owner x) /\
    fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_room ctx func s /\
    sb+cap <= s.vs_alloca_next /\
    d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc (Array NONE ty) (ListV avs))) /\
    window_sizes32 ids s /\
    (!id b sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz))
End

Definition window_array_cursor_def:
  window_array_cursor enabled owner op site slot value sb cap d n s <=>
    (enabled ==>
      (!x. op = Var x ==> not_fresh_at owner x) /\
      eval_operand op s = SOME (n2w slot) /\
      FLOOKUP s.vs_allocas site = SOME (slot,32) /\
      slot < dimword (:256) /\
      venomMemDefs$regions_disjoint (sb,cap) (slot,32) /\
      venomMemDefs$regions_disjoint (d,n) (slot,32) /\
      mem_word_at slot s.vs_memory = n2w value)
End

Definition window_array_inv_def:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op label sb cap d j s <=>
    window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
    abi_encoder_array_prefix ty avs j d s.vs_memory /\
    window_array_cursor T owner ip isite islot j sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
    window_array_cursor active owner dp dsite dslot
      (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
    (!x. count_op = Var x ==> not_fresh_at owner x) /\
    eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
    ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = 0
End

Theorem window_array_inv_root:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s ==>
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s
Proof
  simp[window_array_inv_def]
QED

Theorem window_array_inv_prefix:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s ==>
  abi_encoder_array_prefix ty avs j d s.vs_memory
Proof
  simp[window_array_inv_def]
QED

Theorem window_array_inv_control:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s ==>
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = 0
Proof
  simp[window_array_inv_def]
QED

Theorem window_array_inv_init:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  mem_word_at d s.vs_memory = n2w (LENGTH avs) /\
  window_array_cursor T owner ip isite islot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_cursor active owner dp dsite dslot (LENGTH avs * abi_member_head_size ty)
    sb cap d (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  (!x. count_op = Var x ==> not_fresh_at owner x) /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = 0 ==>
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d 0 s
Proof
  simp[window_array_inv_def, abi_encoder_array_prefix_empty]
QED

Theorem window_array_root_live_pre:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?child_cap. child_cap <= msz /\ 32+j*msz+child_cap <= cap /\
    abi_encoder_window_pre ctx func ready en child_dst child_src ei ty
      (EL j avs) (sb+32+j*msz) child_cap (d+off) s
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  drule_all window_array_live_child >> strip_tac >>
  qexists_tac `child_cap` >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> strip_tac >>
  simp_tac bool_ss [abi_encoder_window_pre_def] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qpat_x_assum `abi_encoder_admissible (AbiDynArray _ _ _ _)` mp_tac >>
      simp_tac bool_ss [Once abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >>
      simp_tac bool_ss [])
  >- decide_tac
  >- decide_tac
  >- (full_simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `inst.inst_id IN ids` by
    (qpat_x_assum `_ SUBSET ids` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF, window_alloca_sites_def] >> metis_tac[]) >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by
    metis_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (b,sz)` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem window_array_root_prepare:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  window_phase ctx func owner ready {} [] s t ==>
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t
Proof
  strip_tac >>
  `abi_encoder_registered_effect {} [] s t` by metis_tac[window_phase_effect] >>
  `!i. FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i` by
    fs[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
  `alloca_inv t /\ alloca_room ctx func t /\ window_alloca_growth s t` by
    metis_tac[window_phase_resources] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap t.vs_memory` by
    (irule abi_encoder_window_effect_source >>
     qexistsl_tac [`{}`, `[]`, `s`] >> fs[window_array_root_def]) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (conj_tac >> irule window_phase_eval >>
     qexistsl_tac [`ctx`, `ready`, `func`, `{}`, `[]`, `s`, `owner`] >>
     fs[window_array_root_def, window_phase_def] >> metis_tac[]) >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> strip_tac >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem window_array_inv_live_pre:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s /\
  window_phase ctx func owner ready {} [] s t /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src t = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst t = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) ==>
  ?child_cap. child_cap <= msz /\ 32+j*msz+child_cap <= cap /\
    abi_encoder_window_pre ctx func ready en child_dst child_src ei ty
      (EL j avs) (sb+32+j*msz) child_cap (d+off) t
Proof
  strip_tac >> irule window_array_root_live_pre >>
  metis_tac[window_array_inv_root, window_array_root_prepare, window_phase_control]
QED

Theorem window_array_inv_resources:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s ==>
  alloca_inv s /\ alloca_room ctx func s /\ window_sizes32 ids s /\
  sb+cap <= s.vs_alloca_next /\
  d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next
Proof
  simp_tac bool_ss [window_array_inv_def, window_array_root_def] >> strip_tac >>
  asm_rewrite_tac[]
QED

Theorem window_array_inv_cursors:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s ==>
  window_array_cursor T owner ip isite islot j sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_cursor active owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty +
     SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s
Proof
  simp_tac bool_ss [window_array_inv_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem window_array_root_observations:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ alloca_inv t /\ alloca_room ctx func t /\
  eval_operand src t = eval_operand src s /\ eval_operand dst t = eval_operand dst s ==>
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t
Proof
  simp_tac bool_ss [window_array_root_def, window_sizes32_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem window_array_cursor_observations:
  window_array_cursor enabled owner op site slot value sb cap d n s /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  (enabled ==> eval_operand op t = eval_operand op s) ==>
  window_array_cursor enabled owner op site slot value sb cap d n t
Proof
  Cases_on `enabled` >> simp_tac bool_ss [window_array_cursor_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem window_array_inv_observations:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label sb cap d j s /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ alloca_inv t /\ alloca_room ctx func t /\
  (!op. (!x. op = Var x ==> not_fresh_at owner x) ==>
     eval_operand op t = eval_operand op s) /\
  ~t.vs_halted /\ t.vs_current_bb = label' /\ t.vs_inst_idx = 0 ==>
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op label' sb cap d j t
Proof
  simp_tac bool_ss [window_array_inv_def] >> strip_tac >>
  `window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t` by
    (irule window_array_root_observations >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >>
     qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (irule window_array_cursor_observations >> goal_assum (drule_at Any) >>
      asm_rewrite_tac[] >> fs[window_array_cursor_def] >> metis_tac[])
  >- (irule window_array_cursor_observations >> goal_assum (drule_at Any) >>
      asm_rewrite_tac[] >> fs[window_array_cursor_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem window_array_growth_observations:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  window_alloca_growth s t
Proof
  simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem window_array_room_observations:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_room ctx func t <=> alloca_room ctx func s)
Proof
  simp[alloca_room_def, pending_alloca_size_def]
QED

Theorem window_array_sizes_observations:
  t.vs_allocas = s.vs_allocas ==> (window_sizes32 R t <=> window_sizes32 R s)
Proof
  simp[window_sizes32_def]
QED
