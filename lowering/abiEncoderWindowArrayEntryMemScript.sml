(* Safe source-length copy and initialized array prefix. *)
Theory abiEncoderWindowArrayEntryMem
Ancestors
  abiEncoderWindowArrayEntry abiEncoderWindowArrayCursorMem
  windowPhaseMem windowTransitionMem abiEncoderWindowPhase
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayBody
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
