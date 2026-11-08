(* Actual-site cursor initialization for array entry, including reused sites. *)
Theory abiEncoderWindowArrayEntry
Ancestors
  abiEncoderWindowArrayFinish abiEncoderWindowArrayBody abiEncoderWindowArrayInvariant
  abiEncoderWindowArrayRound abiEncoderExtendControl abiEncoderArrayContext
  abiEncoderWindow abiEncoderWindowArrayLayout abiEncoderArrayPrefix
  abiEncoderWindowStructuralMembers abiEncoderWindowPhase abiEncoderWindowSequence
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderPrimitiveEffect
  abiDecoderIndexInit abiEncoderArrayCode abiEncoderArrayPhases abiEncoderArrayTailInit
  emitHelperProps freshWrites exprLoweringProps compileEnv emitHelper
  fragExec venomState venomMemDefs valueEncoding valueEncodingProps venomInst
  finite_map pred_set words list arithmetic

Theorem window_array_cursor_init_phase:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor;value_op] mid = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand cursor t = SOME (n2w b) /\
    (!x. cursor = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = w
Proof
  strip_tac >> drule_all window_emit_alloca32_phase >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by
    (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand value_op t = SOME w` by metis_tac[window_phase_operand] >>
  `window_phase ctx func mid en {st.cs_next_id} [] t
    ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >> metis_tac[]) >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {st.cs_next_id} [] s
    ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >>
     simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {st.cs_next_id} [] s u` >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {st.cs_next_id} u` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s u` by
    metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] s u` mp_tac >>
     qpat_assum `window_sizes32 {st.cs_next_id} u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [window_sizes32_def] >>
     rpt strip_tac >> drule_all window_registered_sizes_transport >>
     metis_tac[]) >>
  qexistsl_tac [`u`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem window_array_index_init_run:
  abi_decode_index_init st = (ip,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand ip t = SOME (n2w b) /\
    (!x. ip = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w
Proof
  strip_tac >>
  `?mid. emit_op ALLOCA [Lit 32w] st = (ip,mid) /\
    emit_void MSTORE [ip;Lit 0w] mid = ((),en)` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_index_init_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     strip_tac >> gvs[] >>
     Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends st mid /\ cs_extends mid en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\
   (!x. Lit 0w = Var x ==> not_fresh_at st x)` by simp[eval_operand_def] >>
  drule_all window_array_cursor_init_phase >> simp[]
QED

(* The length copy reads only the root word, independently of declared stride. *)
Theorem window_array_length_copy_phase:
  emit_op MLOAD [src] st = (count_op,mid) /\
  emit_void MSTORE [dst;count_op] mid = ((),en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [(d,32)] s t /\
    window_array_transition ctx func st {} [(d,32)] s t /\
    eval_operand count_op t = SOME (n2w n) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\
    mem_word_at d t.vs_memory = n2w n
Proof
  strip_tac >> drule_all window_cursor_load_phase >> strip_tac >>
  `eval_operand count_op t = SOME (n2w n)` by
    fs[mload_def, mem_word_at_def] >>
  `eval_operand dst t = SOME (n2w d)` by metis_tac[window_phase_operand] >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all window_output_store_phase >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {} [(d,32)] s
    ((mstore d (n2w n) t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `mid`, `{}`, `[(d,32)]`, `t`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {} [(d,32)] s u` >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (`abi_encoder_registered_effect {} [(d,32)] s u` by
       metis_tac[window_phase_effect] >>
     qpat_assum `abi_encoder_registered_effect {} [(d,32)] s u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [window_sizes32_def] >> rpt strip_tac >>
     `!i b sz. i IN ({}:num set) /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by simp[] >>
     drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem window_array_dynamic_cursor_phase:
  emit_op ALLOCA [Lit 32w] st = (dp,c1) /\
  emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
  emit_void MSTORE [dp;offset] c2 = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand count_op s = SOME (n2w n) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand dp t = SOME (n2w b) /\
    (!x. dp = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = n2w (n*asz)
Proof
  strip_tac >> drule_all window_emit_alloca32_phase >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\
   t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand count_op t = SOME (n2w n)` by metis_tac[window_phase_operand] >>
  `eval_operand (Lit (n2w asz)) t = SOME (n2w asz)` by simp[eval_operand_def] >>
  drule_all window_array_mul_phase >> strip_tac >>
  rename1 `window_phase ctx func c1 c2 {} [] t u` >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = c2.cs_current_bb /\
   u.vs_inst_idx = LENGTH c2.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `eval_operand dp u = SOME (n2w b)` by metis_tac[window_phase_operand] >>
  `FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `b+32 <= u.vs_alloca_next` by
    metis_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  `window_phase ctx func c2 en {st.cs_next_id} [] u
    ((mstore b (n2w (n*asz)) u) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >>
     qexistsl_tac [`dp`, `offset`] >> fs[word_mul_n2w, MULT_COMM]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st c2 {st.cs_next_id} [] s u` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[]`, `t`] >> simp[]) >>
  `window_phase ctx func st en {st.cs_next_id} [] s
    ((mstore b (n2w (n*asz)) u) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c2`, `{st.cs_next_id}`, `[]`, `u`] >>
     simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {st.cs_next_id} [] s v` >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next` by
    simp[Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {st.cs_next_id} v` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s v` by
    metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R v` by
    (qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] s v` mp_tac >>
     qpat_assum `window_sizes32 {st.cs_next_id} v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >>
     rpt strip_tac >> drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexistsl_tac [`v`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac
  >- (qpat_x_assum `eval_operand dp u = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `dp` >>
      simp[eval_operand_def, lookup_var_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `v`, mstore_mem_word_at_same]
QED

Theorem window_array_prefix_phase:
  abi_decode_index_init st = (pp,c1) /\
  emit_op MLOAD [src] c1 = (count_op,c2) /\
  emit_void MSTORE [dst;count_op] c2 = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,32) (b,sz) /\
    venomMemDefs$regions_disjoint (d,32) (b,sz)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  mem_word_at sb s.vs_memory = n2w n /\
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
    eval_operand count_op t = SOME (n2w n) /\
    mem_word_at d t.vs_memory = n2w n
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by metis_tac[] >>
  drule_all window_array_index_init_run >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\
   t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (qpat_assum `alloca_room ctx func s` (mp_tac o MATCH_MP alloca_room_next_lt) >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `mem_bytes_at sb 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory` by
    (`window_alloca_growth s t` by metis_tac[window_phase_resources] >>
     irule window_alloca_growth_frame >> asm_rewrite_tac[] >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`] >>
     simp_tac (srw_ss()) [IN_SING, EVERY_DEF] >>
     metis_tac[window_phase_effect]) >>
  `mem_word_at sb t.vs_memory = n2w n` by
    (qpat_x_assum `mem_word_at sb s.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at sb 32 _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  `!x. dst = Var x ==> not_fresh_at c1 x` by metis_tac[not_fresh_at_mono] >>
  drule_all window_array_length_copy_phase >> strip_tac >>
  `window_alloca_growth s t /\
   (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r)` by
    metis_tac[window_phase_resources, window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,32) (b,sz)` by
    (rpt strip_tac >> irule window_alloca_growth_protected >>
     qexistsl_tac [`i`, `{st.cs_next_id}`, `s`, `t`] >>
     full_simp_tac bool_ss [IN_SING] >> asm_rewrite_tac[] >>
     rpt strip_tac >> qpat_x_assum `!b sz. _ ==> _ /\ _` drule >> simp_tac bool_ss []) >>
  `venomMemDefs$regions_disjoint (b,32) (d,32)` by
    (`venomMemDefs$regions_disjoint (d,32) (b,32)` by
       (qpat_assum `!i b sz. i IN _ /\ _ ==> _` mp_tac >>
        simp_tac (srw_ss()) [IN_SING] >> metis_tac[]) >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,32) (b,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `mem_word_at b t'.vs_memory = 0w` by
    (`mem_word_at b t'.vs_memory = mem_word_at b t.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        qexistsl_tac [`ctx`, `func`, `{}`, `[(d,32)]`, `c1`, `st.cs_next_id`] >>
        simp_tac (srw_ss()) [EVERY_DEF] >> metis_tac[]) >> metis_tac[]) >>
  `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {st.cs_next_id} [(d,32)] s t'` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[(d,32)]`, `t`] >>
     simp_tac (srw_ss()) [SUBSET_REFL, EMPTY_SUBSET] >> metis_tac[]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R t'` by
    metis_tac[window_array_transition_sizes] >>
  `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t'` by
    metis_tac[window_array_phase_transition] >>
  `FLOOKUP t'.vs_allocas st.cs_next_id = SOME (b,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `b+32 <= t'.vs_alloca_next` by
    (`window_alloca_growth t t'` by metis_tac[window_phase_resources] >>
     drule_all window_alloca_growth_frontier >> simp[]) >>
  qexistsl_tac [`t'`, `b`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_array_prefix_trace[local]:
  abi_encode_array_prefix src dst st = ((pp,count_op),en) ==>
  ?c1 c2. abi_decode_index_init st = (pp,c1) /\
    emit_op MLOAD [src] c1 = (count_op,c2) /\
    emit_void MSTORE [dst;count_op] c2 = ((),en)
Proof
  simp_tac bool_ss [abi_encode_array_prefix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem window_array_prefix_run:
  abi_encode_array_prefix src dst st = ((pp,count_op),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,32) (b,sz) /\
    venomMemDefs$regions_disjoint (d,32) (b,sz)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  mem_word_at sb s.vs_memory = n2w n /\
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
    eval_operand count_op t = SOME (n2w n) /\
    mem_word_at d t.vs_memory = n2w n
Proof
  strip_tac >> drule window_array_prefix_trace >> strip_tac >>
  `cs_extends st c1` by
    (drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
     fs[inst_extends_def, cs_extends_def] >> decide_tac) >>
  `cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all window_array_prefix_phase >> simp_tac bool_ss []
QED

Theorem window_array_root_prefix_run:
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
    (!x. count_op = Var x ==> not_fresh_at en x)
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
    fs[window_array_root_def] >>
  `32 <= cap /\ mem_word_at sb s.vs_memory = n2w (LENGTH avs)` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff] >> metis_tac[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule window_array_layout >> decide_tac) >>
  `?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    eval_operand pp t = SOME (n2w b) /\
    (!x. pp = Var x \/ count_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    mem_word_at d t.vs_memory = n2w (LENGTH avs)` by
    (irule window_array_prefix_run >> asm_rewrite_tac[] >>
     qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> strip_tac >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     qexistsl_tac [`dst`, `sb`, `src`] >> asm_rewrite_tac[] >>
     reverse conj_tac >- decide_tac >> rpt strip_tac >>
     `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
       venomMemDefs$regions_disjoint
         (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (b,sz)` mp_tac >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
     qpat_x_assum `32 <= cap` mp_tac >>
     qpat_x_assum `32 <= LENGTH _` mp_tac >>
     qpat_x_assum `sz = 32` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) [(d,32)]` by
    (simp_tac (srw_ss()) [EVERY_DEF] >>
     `venomMemDefs$regions_disjoint (sb,cap)
        (d,LENGTH (enc (Array NONE ty) (ListV avs)))` by fs[window_array_root_def] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
     qpat_x_assum `32 <= LENGTH _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[abi_encoder_array_prefix_empty] >>
  conj_tac >- (simp_tac bool_ss [window_array_cursor_def] >>
    asm_rewrite_tac[] >>
    qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
    simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem window_array_root_index_init_run:
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
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  drule_all window_array_index_init_run >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem window_array_root_dynamic_cursor_phase:
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
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
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
  drule_all window_array_dynamic_cursor_phase >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem window_array_tail_init_trace:
  abi_encode_array_tail_init count_op asz st = (dp,en) ==>
  ?c1 offset c2.
    emit_op ALLOCA [Lit 32w] st = (dp,c1) /\
    emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
    emit_void MSTORE [dp;offset] c2 = ((),en)
Proof
  strip_tac >> drule abi_encode_array_tail_init_trace >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp_tac bool_ss [contextTheory.compile_alloc_buffer_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def, LET_THM] >>
  Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
  strip_tac >> gvs[]
QED

Theorem window_array_root_tail_init_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_tail_init count_op asz st = (dp,en) /\
  st.cs_next_id IN ids /\
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
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >> drule window_array_tail_init_trace >> strip_tac >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all window_array_root_dynamic_cursor_phase >> simp_tac bool_ss []
QED

Theorem window_array_root_dynamic_init_steps:
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
    (!x. count_op = Var x ==> not_fresh_at en x)
Proof
  strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at en x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  drule_all window_array_root_index_init_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ [] s u` >>
  `window_array_root ctx func mid ids ei asz msz active ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `!x. count_op = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts` by fs[window_phase_def] >>
  drule_all window_array_root_tail_init_run >> strip_tac >>
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
  qexistsl_tac [`u`, `v`, `b`, `b'`] >> asm_rewrite_tac[] >>
  rpt conj_tac >>
  FIRST [irule window_array_root_owner_mono,
         irule window_array_cursor_owner_mono, all_tac] >> metis_tac[]
QED

Theorem window_array_dynamic_init_trace[local]:
  abi_encode_array_dynamic_init count_op asz st = ((ip,dp),en) ==>
  ?mid. abi_decode_index_init st = (ip,mid) /\
    abi_encode_array_tail_init count_op asz mid = (dp,en)
Proof
  rewrite_tac[abi_encode_array_dynamic_init_split] >>
  simp_tac bool_ss [comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem window_array_root_dynamic_init_run:
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
    (!x. count_op = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule window_array_dynamic_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid en` by fs[inst_extends_def, cs_extends_def] >>
  `fn_has_code st mid func /\ fn_has_code mid en func` by
    metis_tac[fn_has_code_split] >>
  `mid.cs_next_id IN ids` by metis_tac[] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func)` by metis_tac[] >>
  drule_all window_array_root_dynamic_init_steps >> strip_tac >>
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

Theorem window_array_root_prefix_frame:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\
  window_array_transition ctx func phase sites [] s t /\ sites SUBSET ids ==>
  abi_encoder_array_prefix ty avs j d t.vs_memory
Proof
  strip_tac >> irule window_array_prefix_registered_frame >>
  reverse conj_tac
  >- (qexistsl_tac [`active`, `asz`, `cap`, `ei`, `msz`, `sb`, `s.vs_memory`] >>
      fs[window_array_root_def]) >>
  qexistsl_tac [`sites`, `[]`, `s`] >>
  simp_tac (srw_ss()) [EVERY_DEF] >> asm_rewrite_tac[] >>
  `abi_encoder_registered_effect sites [] s t /\ window_alloca_growth s t` by
    metis_tac[window_array_transition_effect, window_array_transition_resources] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> strip_tac >>
  asm_rewrite_tac[] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem window_array_entry_jump:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  alloca_inv s /\ alloca_room ctx func s /\
  s.vs_current_bb = owner.cs_current_bb /\
  s.vs_inst_idx = LENGTH owner.cs_current_insts /\ ~s.vs_halted ==>
  window_array_transition ctx func owner ids outs s (jump_to (FST labels) s)
Proof
  strip_tac >>
  `abi_encoder_extend_sim ctx func s (jump_to (FST labels) s)` by
    (irule abi_encoder_array_loop_entry_extend_sim >> metis_tac[]) >>
  simp_tac bool_ss [window_array_transition_def] >> asm_rewrite_tac[] >>
  simp[venomStateTheory.jump_to_def, abi_encoder_registered_effect_def,
    window_alloca_growth_def, alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, alloca_room_def, pending_alloca_size_def,
    lookup_var_def, window_sizes32_def] >>
  fs[alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, alloca_room_def, pending_alloca_size_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem window_array_entry_header_run:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs 0 d s.vs_memory /\
  window_array_cursor T owner ip isite islot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_array_cursor active owner dp dsite dslot
    (LENGTH avs * abi_member_head_size ty) sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  (!x. count_op = Var x ==> not_fresh_at owner x) /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  s.vs_current_bb = owner.cs_current_bb /\
  s.vs_inst_idx = LENGTH owner.cs_current_insts /\ ~s.vs_halted ==>
  window_array_transition ctx func owner {} [] s (jump_to (FST labels) s) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d 0
    (jump_to (FST labels) s)
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[window_array_root_def] >>
  `window_array_transition ctx func owner {} [] s (jump_to (FST labels) s)` by
    (irule window_array_entry_jump >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `alloca_inv (jump_to (FST labels) s) /\
   alloca_room ctx func (jump_to (FST labels) s)` by
    metis_tac[window_array_transition_resources] >>
  `window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d
     (jump_to (FST labels) s)` by
    (irule window_array_root_observations >> asm_rewrite_tac[] >>
     qexists_tac `s` >> simp[venomStateTheory.jump_to_def, eval_operand_def, lookup_var_def] >>
     asm_rewrite_tac[]) >>
  `!enabled op site slot value.
     window_array_cursor enabled owner op site slot value sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) s ==>
     window_array_cursor enabled owner op site slot value sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) (jump_to (FST labels) s)` by
    (rpt strip_tac >> irule window_array_cursor_observations >>
     goal_assum (drule_at Any) >> simp[venomStateTheory.jump_to_def, eval_operand_def, lookup_var_def]) >>
  irule window_array_inv_init >> asm_rewrite_tac[] >>
  simp[venomStateTheory.jump_to_def, eval_operand_def, lookup_var_def] >>
  qpat_x_assum `abi_encoder_array_prefix _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_array_prefix_def] >> metis_tac[]
QED

(* Complete the initialization phase without exposing the prefix/parent memory
   implementation in either static or dynamic initializer consumers. *)
Theorem window_array_entry_from_init:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs 0 d s.vs_memory /\
  window_array_cursor T st pp psite pslot 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  window_phase ctx func st owner sites [] s t /\
  window_array_transition ctx func st sites [] s t /\
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
    (LENGTH (enc (Array NONE ty) (ListV avs))) (jump_to (FST labels) t)
Proof
  strip_tac >>
  `abi_encoder_array_prefix ty avs 0 d t.vs_memory` by
    (irule window_array_root_prefix_frame >> metis_tac[]) >>
  `t.vs_current_bb = owner.cs_current_bb /\
    t.vs_inst_idx = LENGTH owner.cs_current_insts /\ ~t.vs_halted` by
    fs[window_phase_def] >>
  drule_all window_array_entry_header_run >> strip_tac >>
  `window_array_transition ctx func st sites [] t (jump_to (FST labels) t)` by
    (irule window_array_transition_owner_weaken >>
     qexists_tac `owner` >> asm_rewrite_tac[] >>
     irule window_array_transition_enlarge >>
     goal_assum (drule_at Any) >> simp[]) >>
  `window_array_transition ctx func st sites [] s (jump_to (FST labels) t)` by
    (irule window_array_transition_trans >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `window_array_cursor T st pp psite pslot 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) (jump_to (FST labels) t)` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule window_array_cursor_owner_mono >> metis_tac[]
QED

Theorem window_array_dynamic_entry_run:
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
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >> drule abi_encode_array_prefix_shape >> strip_tac >>
  drule_all window_array_root_prefix_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz T ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all window_array_root_dynamic_init_run >> strip_tac >>
  rename1 `window_phase ctx func mid owner _ _ u v` >>
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (drule window_array_dynamic_init_trace >> strip_tac >>
     drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
     drule abi_encode_array_tail_init_shape >> strip_tac >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `window_array_cursor T mid pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `{mid.cs_next_id;mid.cs_next_id+2} SUBSET ids /\
   st.cs_next_id NOTIN {mid.cs_next_id;mid.cs_next_id+2}` by
    (asm_simp_tac (srw_ss()) [SUBSET_DEF] >> decide_tac) >>
  drule_all window_array_entry_from_init >> strip_tac >>
  `window_array_transition ctx func st ids [(d,32)] s u` by
    (qpat_assum `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s u` mp_tac >>
     qpat_assum `st.cs_next_id IN ids` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `window_array_transition ctx func st ids [(d,32)] u (jump_to (FST labels) v)` by
    (irule window_array_transition_owner_weaken >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `bi`, `bd`] >>
  asm_rewrite_tac[] >> irule window_array_transition_trans >> metis_tac[]
QED

Theorem window_array_static_entry_run:
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
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >> drule abi_encode_array_prefix_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule_all window_array_root_prefix_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz F ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all window_array_root_index_init_run >> strip_tac >>
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
  drule_all window_array_entry_from_init >> strip_tac >>
  `window_array_transition ctx func st ids [(d,32)] s u` by
    (qpat_assum `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s u` mp_tac >>
     qpat_assum `st.cs_next_id IN ids` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `window_array_transition ctx func st ids [(d,32)] u (jump_to (FST labels) v)` by
    (irule window_array_transition_owner_weaken >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> simp[]) >>
  `window_array_transition ctx func st ids [(d,32)] s (jump_to (FST labels) v)` by
    (irule window_array_transition_trans >> metis_tac[]) >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `b'`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_entry_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  (active ==> mid.cs_next_id+2 IN ids) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func)) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi bd.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip mid.cs_next_id bi dp (if active then mid.cs_next_id+2 else 0) bd
      count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  Cases_on `active` >> simp_tac bool_ss [] >> strip_tac
  >- (drule_all window_array_dynamic_entry_run >> simp_tac bool_ss []) >>
  drule_all window_array_static_entry_run >> strip_tac >>
  qexistsl_tac [`t`, `pb`, `bi`, `0`] >> asm_rewrite_tac[]
QED
