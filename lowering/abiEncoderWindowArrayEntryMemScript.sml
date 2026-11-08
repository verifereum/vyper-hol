(* Safe source-length copy and initialized array prefix. *)
Theory abiEncoderWindowArrayEntryMem
Ancestors
  abiEncoderWindowArrayEntry abiEncoderWindowArrayCursorMem
  abiEncoderWindow abiEncoderWindowArrayLayout windowSequenceMem
  abiEncoderWindowSequence instMemFrontier venomInst allocaFootprint
  abiEncoderArrayLoopCode abiEncoderArrayHeader abiDecoderPrimitiveLoopEntry
  memControlFlow memSafeRun venomExecSemantics rich_list
  windowPhaseMem windowTransitionMem abiEncoderWindowPhase
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayBody abiEncoderWindowArrayRound
  abiEncoderWindowStructuralMembers abiEncoderRegisteredEffect
  abiEncoderWindowContract abiEncoderPrimitiveEffect freshWrites
  emitHelperProps exprLoweringProps compileEnv emitHelper fragExec
  venomState venomMemDefs valueEncoding valueEncodingProps finite_map pred_set words list arithmetic

Theorem window_array_length_copy_phase_mem:
  emit_op MLOAD [src] st = (count_op,mid) /\
  emit_void MSTORE [dst;count_op] mid = ((),en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next ==>
  ?t. window_phase ctx func st en {} [(d,32)] s t /\
    window_array_transition ctx func st {} [(d,32)] s t /\
    eval_operand count_op t = SOME (n2w n) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\
    mem_word_at d t.vs_memory = n2w n /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_cursor_load_phase_mem >> strip_tac >>
  `eval_operand count_op t = SOME (n2w n)` by fs[mload_def, mem_word_at_def] >>
  `eval_operand dst t = SOME (n2w d)` by metis_tac[window_phase_operand] >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `d+32 <= t.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_frontier] >>
  drule_all window_output_store_phase_mem >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {} [(d,32)] s
    ((mstore d (n2w n) t) with vs_inst_idx := LENGTH en.cs_current_insts) /\
   mem_cont_sim ctx func s
    ((mstore d (n2w n) t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{}`, `[]`, `mid`, `{}`, `[(d,32)]`, `t`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {} [(d,32)] s u` >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (`abi_encoder_registered_effect {} [(d,32)] s u` by metis_tac[window_phase_effect] >>
     qpat_assum `abi_encoder_registered_effect {} [(d,32)] s u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >> rpt strip_tac >>
     `!i b sz. i IN ({}:num set) /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by simp[] >>
     drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

(* Endpoint-independent framing for the initialized scratch cursor. *)
Theorem window_array_prefix_init_frame[local]:
  window_phase ctx func st en {site} [] s t /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
    regions_disjoint (sb,32) (b,sz) /\ regions_disjoint (d,32) (b,sz)) /\
  FLOOKUP t.vs_allocas site = SOME (b,32) ==>
  mem_word_at sb t.vs_memory = mem_word_at sb s.vs_memory /\
  regions_disjoint (b,32) (d,32)
Proof
  strip_tac >>
  `window_alloca_growth s t /\ abi_encoder_registered_effect {site} [] s t` by
    metis_tac[window_phase_resources, window_phase_effect] >>
  conj_tac
  >- (`mem_bytes_at sb 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory` by
        (irule window_alloca_growth_frame >> asm_rewrite_tac[] >>
         qexistsl_tac [`{site}`, `[]`] >> simp[] >> metis_tac[]) >>
      fs[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `!i b sz. i IN {site} /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
     regions_disjoint (d,32) (b,sz)` by
    (rpt strip_tac >> irule window_alloca_growth_protected >>
     qexistsl_tac [`i`, `{site}`, `s`, `t`] >> simp[] >> metis_tac[]) >>
  `regions_disjoint (d,32) (b,32)` by metis_tac[IN_SING] >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem window_array_prefix_phase_mem:
  abi_decode_index_init st = (pp,c1) /\
  emit_op MLOAD [src] c1 = (count_op,c2) /\
  emit_void MSTORE [dst;count_op] c2 = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ regions_disjoint (sb,32) (b,sz) /\ regions_disjoint (d,32) (b,sz)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    eval_operand pp t = SOME (n2w b) /\
    (!x. pp = Var x \/ count_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\
    eval_operand count_op t = SOME (n2w n) /\ mem_word_at d t.vs_memory = n2w n /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by metis_tac[] >>
  drule_all window_array_index_init_run_mem >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\ t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (qpat_assum `alloca_room ctx func s` (mp_then Any mp_tac alloca_room_next_lt) >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `mem_word_at sb t.vs_memory = mem_word_at sb s.vs_memory /\
   regions_disjoint (b,32) (d,32)` by
    (irule window_array_prefix_init_frame >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `!x. dst = Var x ==> not_fresh_at c1 x` by metis_tac[not_fresh_at_mono] >>
  `sb+32 <= t.vs_alloca_next /\ d+32 <= t.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_frontier] >>
  `mem_word_at sb t.vs_memory = n2w n` by simp[] >>
  drule_all window_array_length_copy_phase_mem >> strip_tac >>
  `mem_word_at b t'.vs_memory = 0w` by
    (`mem_word_at b t'.vs_memory = mem_word_at b t.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        qexistsl_tac [`ctx`, `func`, `{}`, `[(d,32)]`, `c1`, `st.cs_next_id`] >>
        simp[] >> metis_tac[]) >> metis_tac[]) >>
  `window_phase ctx func st en {st.cs_next_id} [(d,32)] s t' /\ mem_cont_sim ctx func s t'` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[(d,32)]`, `t`] >> simp[]) >>
  `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t'` by
    metis_tac[window_array_phase_transition, window_array_transition_sizes] >>
  `FLOOKUP t'.vs_allocas st.cs_next_id = SOME (b,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `b+32 <= t'.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_frontier] >>
  qexistsl_tac [`t'`, `b`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem window_array_root_index_init_run_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_decode_index_init st = (ip,en) /\ st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en ip st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  drule_all window_array_index_init_run_mem >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem window_array_root_prefix_bounds[local]:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  site IN ids ==>
  32 <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  mem_word_at sb s.vs_memory = n2w (LENGTH avs) /\
  EVERY (\r. regions_disjoint (sb,cap) r) [(d,32)] /\
  (!b sz. FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
    sz = 32 /\ regions_disjoint (sb,32) (b,sz) /\ regions_disjoint (d,32) (b,sz))
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `32 <= cap /\ mem_word_at sb s.vs_memory = n2w (LENGTH avs)` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff] >> metis_tac[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule window_array_layout >> decide_tac) >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> strip_tac >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- decide_tac
  >- decide_tac
  >- (simp[] >>
      qpat_x_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
      qpat_x_assum `32 <= LENGTH _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
      simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `sz = 32 /\ regions_disjoint (sb,cap) (b,sz) /\
   regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
  qpat_x_assum `regions_disjoint (sb,cap) (b,sz)` mp_tac >>
  qpat_x_assum `regions_disjoint (d,_) (b,sz)` mp_tac >>
  qpat_x_assum `32 <= cap` mp_tac >> qpat_x_assum `32 <= LENGTH _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac
QED

Theorem window_array_root_prefix_run_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),en) /\
  st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    abi_encoder_array_prefix ty avs 0 d t.vs_memory /\
    window_array_cursor T en pp st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_root_prefix_bounds >> strip_tac >>
  qpat_assum `abi_encode_array_prefix _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abiEncoderArrayPhasesTheory.abi_encode_array_prefix_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `abi_decode_index_init st = (pp,c1)` >>
  rename1 `emit_op MLOAD [src] c1 = (count_op,c2)` >>
  rename1 `emit_void MSTORE [dst;count_op] c2 = ((),en)` >>
  `cs_extends st c1` by
    (drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >>
     simp_tac bool_ss [] >> strip_tac >> fs[inst_extends_def, cs_extends_def] >> decide_tac) >>
  `cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `alloca_room ctx func s /\ alloca_inv s /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x)` by
    metis_tac[window_array_root_def] >>
  drule_all window_array_prefix_phase_mem >> strip_tac >>
  `EVERY (\r. regions_disjoint (sb,cap) r) [(d,32)]` by simp[] >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_prefix_zero] >>
  conj_tac >- (simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
    qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
    simp_tac bool_ss [window_array_root_def] >> strip_tac >>
    qpat_x_assum `!id b sz. id IN ids /\ _ ==> _ /\ _` drule >>
    disch_then drule >> simp[]) >>
  metis_tac[]
QED

Theorem window_array_mul_phase_mem:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_mul_pure >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_op_mem_ok >> disch_then irule >> simp[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

(* Finish a cursor phase without exposing the concrete store in its consumers. *)
Theorem window_array_stored_cursor_mem[local]:
  window_phase ctx func st mid {site} [] s u /\
  mem_cont_sim ctx func s u /\
  emit_void MSTORE [ptr_op;value_op] mid = ((),en) /\
  fn_has_code mid en func /\
  eval_operand ptr_op u = SOME (n2w b) /\ eval_operand value_op u = SOME w /\
  (!x. ptr_op = Var x ==> not_fresh_at mid x) /\
  FLOOKUP u.vs_allocas site = SOME (b,32) /\
  b+32 <= u.vs_alloca_next /\ b < dimword (:256) /\
  st.cs_next_var <= mid.cs_next_var ==>
  ?t. window_phase ctx func st en {site} [] s t /\
    window_array_transition ctx func st {site} [] s t /\
    eval_operand ptr_op t = SOME (n2w b) /\
    (!x. ptr_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas site = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ mem_word_at b t.vs_memory = w /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = mid.cs_current_bb /\
   u.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all window_cursor_store_phase_mem >> strip_tac >>
  `mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {site} [] s
     ((mstore b w u) with vs_inst_idx := LENGTH en.cs_current_insts) /\
   mem_cont_sim ctx func s
     ((mstore b w u) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{site}`, `[]`, `mid`, `{site}`, `[]`, `u`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {site} [] s v` >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next` by
    simp[Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {site} v` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {site} [] s v` by metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R v` by
    (qpat_assum `abi_encoder_registered_effect {site} [] s v` mp_tac >>
     qpat_assum `window_sizes32 {site} v` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [window_sizes32_def] >> rpt strip_tac >>
     drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexists_tac `v` >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `v`, mstore_mem_word_at_same]
QED

Theorem window_array_root_dynamic_cursor_phase_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  emit_op ALLOCA [Lit 32w] st = (dp,c1) /\
  emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
  emit_void MSTORE [dp;offset] c2 = ((),en) /\ st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en dp st.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  `asz = abi_member_head_size ty` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff] >> metis_tac[]) >>
  drule_all window_emit_alloca32_phase_mem >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\ t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand count_op t = SOME (n2w (LENGTH avs))` by metis_tac[window_phase_operand] >>
  `eval_operand (Lit (n2w asz)) t = SOME (n2w asz)` by simp[eval_operand_def] >>
  drule_all window_array_mul_phase_mem >> strip_tac >>
  rename1 `window_phase ctx func c1 c2 {} [] t u` >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st c2 {st.cs_next_id} [] s u /\ mem_cont_sim ctx func s u` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[]`, `t`] >> simp[]) >>
  `eval_operand dp u = SOME (n2w b) /\
   FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32) /\ b+32 <= u.vs_alloca_next` by
    metis_tac[window_phase_operand, window_phase_effect, abi_encoder_registered_effect_allocated,
      window_phase_resources, window_alloca_growth_frontier] >>
  `!x. dp = Var x ==> not_fresh_at c2 x` by metis_tac[not_fresh_at_mono] >>
  `st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  `eval_operand offset u = SOME (n2w (LENGTH avs * abi_member_head_size ty))` by
    fs[word_mul_n2w] >>
  drule_all window_array_stored_cursor_mem >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t'`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t'` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem window_array_root_tail_init_run_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_tail_init count_op asz st = (dp,en) /\ st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en dp st.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule window_array_tail_init_trace >> strip_tac >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all window_array_root_dynamic_cursor_phase_mem >> simp_tac bool_ss []
QED

Theorem window_array_root_dynamic_init_steps_mem[local]:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_decode_index_init st = (ip,mid) /\
  abi_encode_array_tail_init count_op asz mid = (dp,en) /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u v bi bd.
    window_phase ctx func st mid {st.cs_next_id} [] s u /\
    window_phase ctx func mid en {mid.cs_next_id} [] u v /\
    window_array_transition ctx func st {st.cs_next_id} [] s u /\
    window_array_transition ctx func mid {mid.cs_next_id} [] u v /\
    window_array_root ctx func en ids ei asz msz active ty avs src dst sb cap d v /\
    window_array_cursor T en ip st.cs_next_id bi 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) v /\
    window_array_cursor T en dp mid.cs_next_id bd
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) v /\
    eval_operand count_op v = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s v
Proof
  strip_tac >>
  drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abiEncoderArrayTailInitTheory.abi_encode_array_tail_init_shape >> strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at en x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  drule_all window_array_root_index_init_run_mem >> strip_tac >>
  rename1 `window_phase ctx func st mid _ [] s u` >>
  `window_array_root ctx func mid ids ei asz msz active ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `!x. count_op = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts` by fs[window_phase_def] >>
  drule_all window_array_root_tail_init_run_mem >> strip_tac >>
  rename1 `window_phase ctx func mid en _ [] u v` >>
  `window_array_cursor T mid ip st.cs_next_id b 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `window_array_cursor T mid ip st.cs_next_id b 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) v` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand count_op v = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `mem_cont_sim ctx func s v` by metis_tac[memContinuationTheory.mem_cont_sim_trans] >>
  qexistsl_tac [`u`, `v`, `b`, `b'`] >> asm_rewrite_tac[] >>
  rpt conj_tac >>
  FIRST [irule window_array_root_owner_mono,
         irule window_array_cursor_owner_mono, all_tac] >> metis_tac[]
QED

Theorem window_array_dynamic_init_trace_mem[local]:
  abi_encode_array_dynamic_init count_op asz st = ((ip,dp),en) ==>
  ?mid. abi_decode_index_init st = (ip,mid) /\
    abi_encode_array_tail_init count_op asz mid = (dp,en)
Proof
  rewrite_tac[abiEncoderArrayTailInitTheory.abi_encode_array_dynamic_init_split] >>
  simp_tac bool_ss [comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem window_array_root_dynamic_init_run_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_dynamic_init count_op asz st = ((ip,dp),en) /\
  st.cs_next_id IN ids /\ st.cs_next_id+2 IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (st.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (st.cs_next_var+1))]) (fn_insts func) /\
  fn_has_code st en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t bi bd.
    window_phase ctx func st en {st.cs_next_id;st.cs_next_id+2} [] s t /\
    window_array_transition ctx func st {st.cs_next_id;st.cs_next_id+2} [] s t /\
    window_array_root ctx func en ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en ip st.cs_next_id bi 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    window_array_cursor T en dp (st.cs_next_id+2) bd
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule window_array_dynamic_init_trace_mem >> strip_tac >>
  drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abiEncoderArrayTailInitTheory.abi_encode_array_tail_init_shape >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid en` by fs[inst_extends_def, cs_extends_def] >>
  `fn_has_code st mid func /\ fn_has_code mid en func` by metis_tac[fn_has_code_split] >>
  `mid.cs_next_id IN ids` by metis_tac[] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func)` by metis_tac[] >>
  drule_all window_array_root_dynamic_init_steps_mem >> strip_tac >>
  `window_phase ctx func st en {st.cs_next_id;st.cs_next_id+2} [] s v` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{mid.cs_next_id}`, `[]`, `u`] >>
     asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R v` by
    metis_tac[window_array_transition_sizes] >>
  `window_array_transition ctx func st {st.cs_next_id;st.cs_next_id+2} [] s v` by
    metis_tac[window_array_phase_transition] >>
  qexistsl_tac [`v`, `bi`, `bd`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_entry_jump_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  s.vs_current_bb = owner.cs_current_bb /\
  s.vs_inst_idx = LENGTH owner.cs_current_insts /\ ~s.vs_halted ==>
  mem_cont_sim ctx func s (jump_to (FST labels) s)
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  irule mem_cont_sim_edge >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac
  >- (qexists_tac `<|bb_label := owner.cs_current_bb; bb_instructions :=
        owner.cs_current_insts ++ [mk_inst owner.cs_next_id JMP [Label (FST labels)] []]|>` >>
      simp[] >> conj_tac
      >- (gen_tac >> irule abi_decoder_loop_entry_control >>
          simp[] >> qexists_tac `owner.cs_next_id` >> simp[]) >>
      gen_tac >> simp[Once mem_safe_block_def, get_instruction_def, EL_APPEND_EQN,
        mem_safe_step_def, below_frontier_no_ranges, mk_inst_def, is_terminator_def,
        step_inst_def, step_inst_base_opcode_eqs]) >>
  simp[jump_to_def, abi_encode_array_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem window_array_entry_from_init_mem:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs 0 d s.vs_memory /\
  window_array_cursor T st pp psite pslot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_phase ctx func st owner sites [] s t /\
  window_array_transition ctx func st sites [] s t /\ mem_cont_sim ctx func s t /\
  sites SUBSET ids /\ psite NOTIN sites /\
  (!x. not_fresh_at st x ==> not_fresh_at owner x) /\
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t /\
  window_array_cursor T owner ip isite islot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
  window_array_cursor active owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
  (!x. count_op = Var x ==> not_fresh_at owner x) /\
  eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels ==>
  window_array_transition ctx func st sites [] s (jump_to (FST labels) t) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d 0
    (jump_to (FST labels) t) /\
  window_array_cursor T owner pp psite pslot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) (jump_to (FST labels) t) /\
  mem_cont_sim ctx func s (jump_to (FST labels) t)
Proof
  strip_tac >> drule_all window_array_entry_from_init >> strip_tac >>
  asm_rewrite_tac[] >>
  `t.vs_current_bb = owner.cs_current_bb /\
   t.vs_inst_idx = LENGTH owner.cs_current_insts /\ ~t.vs_halted` by
    metis_tac[window_phase_control] >>
  drule_all window_array_entry_jump_mem >>
  metis_tac[memContinuationTheory.mem_cont_sim_trans]
QED

Theorem window_array_entry_transition_chain_mem[local]:
  window_array_transition ctx func st first outs s u /\ first SUBSET ids /\
  window_array_transition ctx func mid second [] u v /\ second SUBSET ids /\
  (!x. not_fresh_at st x ==> not_fresh_at mid x) /\
  mem_cont_sim ctx func s u /\ mem_cont_sim ctx func u v ==>
  window_array_transition ctx func st ids outs s v /\ mem_cont_sim ctx func s v
Proof
  strip_tac >>
  `window_array_transition ctx func st ids outs s u` by
    (irule window_array_transition_enlarge >> qexistsl_tac [`first`, `outs`] >> simp[]) >>
  `window_array_transition ctx func st ids outs u v` by
    (irule window_array_transition_owner_weaken >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> irule window_array_transition_enlarge >>
     qexistsl_tac [`second`, `[]`] >> simp[]) >>
  metis_tac[window_array_transition_trans, memContinuationTheory.mem_cont_sim_trans]
QED

Theorem window_array_static_entry_run_mem:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  abi_decode_index_init mid = (ip,owner) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz F ty avs src dst
      ip mid.cs_next_id bi (Lit 0w) 0 0 count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule abiEncoderArrayContextTheory.abi_encode_array_prefix_shape >> strip_tac >>
  drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule_all window_array_root_prefix_run_mem >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz F ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all window_array_root_index_init_run_mem >> strip_tac >>
  rename1 `window_phase ctx func mid owner _ _ u v` >>
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d v` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand count_op v = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `!x. count_op = Var x ==> not_fresh_at owner x` by metis_tac[] >>
  `window_array_cursor F owner (Lit 0w) 0 0
     (LENGTH avs * abi_member_head_size ty) sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) v` by simp[window_array_cursor_def] >>
  `{mid.cs_next_id} SUBSET ids /\ st.cs_next_id NOTIN {mid.cs_next_id}` by
    (asm_simp_tac (srw_ss()) [SUBSET_DEF] >> decide_tac) >>
  drule_all window_array_entry_from_init_mem >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `b'`] >> asm_rewrite_tac[] >>
  drule_all window_array_entry_transition_chain_mem >> strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[]
QED

Theorem window_array_dynamic_entry_run_mem:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\ mid.cs_next_id+2 IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi bd.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip mid.cs_next_id bi dp (mid.cs_next_id+2) bd count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule abiEncoderArrayContextTheory.abi_encode_array_prefix_shape >> strip_tac >>
  drule_all window_array_root_prefix_run_mem >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz T ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all window_array_root_dynamic_init_run_mem >> strip_tac >>
  rename1 `window_phase ctx func mid owner _ _ u v` >>
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (drule window_array_dynamic_init_trace_mem >> strip_tac >>
     drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
     drule abiEncoderArrayTailInitTheory.abi_encode_array_tail_init_shape >> strip_tac >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `{mid.cs_next_id;mid.cs_next_id+2} SUBSET ids /\
   st.cs_next_id NOTIN {mid.cs_next_id;mid.cs_next_id+2}` by
    (asm_simp_tac (srw_ss()) [SUBSET_DEF] >> decide_tac) >>
  drule_all window_array_entry_from_init_mem >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `bi`, `bd`] >> asm_rewrite_tac[] >>
  drule_all window_array_entry_transition_chain_mem >> strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[]
QED
