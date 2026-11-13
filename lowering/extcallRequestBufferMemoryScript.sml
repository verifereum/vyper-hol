(* The stored argument tuple enters the actual calldata encoder and suffix. *)
Theory extcallRequestBufferMemory
Ancestors
  extcallCalldataSuffixMemory extcallEncoderWindowMemory
  abiEncoderWindowContract abiEncoderWindowPhase abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame windowPhaseMem fragGasPathMem fragGasPathFrameMem
  memContinuation exprLoweringProps emitHelperProps compileEnv emitHelper
  abiEncoderProps abiEncoderWindow venomState venomMemDefs words list finite_map pred_set arithmetic
  exprSimAbiEncodeStateTransport loweringStateRelDefs localPtrsProps
  exprSimAbiEncodeSiteResources venomInst externalReturnEncoderSites

Theorem extcall_window_source_rel[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  window_phase ctx func st en ids outs s t /\ abi_encode_exec_frame func s t /\
  (!name b n. local_region ce es.scopes s name b n ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory) /\
  (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ inst.inst_id IN ids /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `state_rel func ce cx es s /\ local_ptrs_rel func ce es.scopes s /\
   immutable_alloca_sep func ce cx es s /\ immutable_base_zero ce s /\
   fmp_room ctx func s` by fs[stmt_state_rel_def,state_rel_def] >>
  `abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
   alloca_inv t /\ alloca_room ctx func t /\ t.vs_labels = s.vs_labels` by
    fs[window_phase_def] >>
  `(!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r) /\
   (!i q k. FLOOKUP t.vs_allocas i = SOME (q,k) /\
     FLOOKUP s.vs_allocas i = NONE ==> s.vs_alloca_next <= q) /\
   s.vs_alloca_next <= t.vs_alloca_next` by
    (fs[abi_encoder_registered_effect_def,window_alloca_growth_def] >> metis_tac[]) >>
  `!name entry lp sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var lp) sz) ==>
    lookup_var lp t = lookup_var lp s` by
    (rpt strip_tac >>
     `not_fresh_at st lp` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `?w. lookup_var lp s = SOME w` by (fs[local_ptrs_rel_def] >> metis_tac[]) >>
     metis_tac[window_phase_vars]) >>
  `state_rel func ce cx es t` by
    (match_mp_tac (Q.INST [`observer` |-> `func`, `initial` |-> `s`, `actual` |-> `t`,
       `prepared` |-> `s`, `ids` |-> `ids`, `outs` |-> `outs`,
       `cenv` |-> `ce`, `vs` |-> `es`] abi_encode_caller_state_rel) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_alloca_sep func ce cx es t` by
    (drule_all abi_encode_caller_immutable_separation >> simp[]) >>
  `fmp_room ctx func t` by
    (fs[fmp_room_def,abi_encode_exec_frame_def] >> disch_tac >>
     qpat_x_assum `_ ==> _ /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> decide_tac) >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >> rpt strip_tac >>
     `not_fresh_at st x` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var x s = SOME 0w` by
       (fs[immutable_base_zero_def,eval_operand_def] >> metis_tac[]) >>
     metis_tac[window_phase_vars]) >>
  simp[stmt_state_rel_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id IN ids` >- metis_tac[] >>
  `FLOOKUP t.vs_allocas inst.inst_id = FLOOKUP s.vs_allocas inst.inst_id` by
    (fs[abi_encoder_registered_effect_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def] >> metis_tac[]
QED

Theorem extcall_window_region_frame[local]:
  window_phase ctx func st en ids outs s t /\
  p+n <= s.vs_alloca_next /\
  EVERY (\r. venomMemDefs$regions_disjoint (p,n) r) outs /\
  (!i q k. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (q,k) ==>
    p+n <= q \/ q+k <= p) ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >>
  `window_alloca_growth s t /\ abi_encoder_registered_effect ids outs s t` by
    metis_tac[window_phase_resources,window_phase_effect] >>
  irule abi_encoder_window_effect_bytes >> qexistsl_tac [`ids`, `outs`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (fs[window_alloca_growth_def,venomMemDefsTheory.regions_disjoint_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  PairCases_on `x` >>
  `FLOOKUP t.vs_allocas id = SOME (x0,x1)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  gvs[] >>
  qpat_x_assum `!i q k. _` drule_all >> strip_tac >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_window_local_bytes[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  compile_abi_encode_to_buf dst src ei se = (out,sen) /\
  fn_has_code se sen func /\ fn_inst_ids_distinct func /\
  st.cs_next_var <= se.cs_next_var /\
  window_phase ctx func st en (window_alloca_sites func (frag_ids se sen))
    [(b+32,len)] s t /\
  MEM shared (fn_insts func) /\ shared.inst_outputs = [q] /\
  not_local_ptr ce es.scopes q /\
  FLOOKUP s.vs_allocas shared.inst_id = SOME (b,sz) /\ 32+len <= sz ==>
  !name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce es.scopes s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `loweringStateRelDefs$regions_disjoint b sz p n` by
    (irule local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
  `p+n <= s.vs_alloca_next` by
    (fs[local_region_def,local_ptrs_rel_def] >>
     qpat_x_assum `!name entry lp sz. _` drule_all >> strip_tac >> gvs[]) >>
  `EVERY (\r. venomMemDefs$regions_disjoint (p,n) r) [(b+32,len)]` by
    (fs[venomMemDefsTheory.regions_disjoint_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid pb pn. aid IN window_alloca_sites func (frag_ids se sen) /\
      FLOOKUP s.vs_allocas aid = SOME(pb,pn) ==> p+n <= pb \/ pb+pn <= p` by
    suspend "scratch" >>
  drule_all extcall_window_region_frame >> simp[]
QED

Resume extcall_window_local_bytes[scratch]:
  map_every qx_gen_tac [`aid`,`pb`,`pn`] >> strip_tac >>
  fs[window_alloca_sites_def] >>
  `?v. inst.inst_outputs = [v] /\ not_local_ptr ce es.scopes v` by
    (mp_tac (Q.INST [`ready` |-> `se`, `body_end` |-> `sen`,
       `obs` |-> `func`, `earlier` |-> `st`, `i` |-> `inst`,
       `scopes` |-> `es.scopes`] abi_encode_compiled_scratch_site) >>
     simp[] >> metis_tac[]) >>
  `loweringStateRelDefs$regions_disjoint pb pn p n` by
    (irule local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise extcall_window_local_bytes[local]

(* Constructor immutables are separated from actual function allocation sites. *)
Theorem extcall_window_immutable_bytes[local]:
  stmt_state_rel ctx func ce cx es s /\
  window_phase ctx func st en (window_alloca_sites func (frag_ids se sen))
    [(b+32,len)] s t /\
  MEM shared (fn_insts func) /\ shared.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas shared.inst_id = SOME (b,sz) /\ 32+len <= sz ==>
  ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory
Proof
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
  `off + type_memory_size tv <= s.vs_alloca_next /\
   (!inst p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME(p,n) ==>
      loweringStateRelDefs$regions_disjoint off (type_memory_size tv) p n)` by
    (fs[immutable_alloca_sep_def] >> metis_tac[]) >>
  `loweringStateRelDefs$regions_disjoint off (type_memory_size tv) b sz` by
    metis_tac[] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (off,type_memory_size tv) r)
      [(b+32,len)]` by
    (fs[venomMemDefsTheory.regions_disjoint_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid pb pn. aid IN window_alloca_sites func (frag_ids se sen) /\
      FLOOKUP s.vs_allocas aid = SOME(pb,pn) ==>
      off+type_memory_size tv <= pb \/ pb+pn <= off` by
    (rpt gen_tac >> strip_tac >> fs[window_alloca_sites_def] >>
     metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  drule_all extcall_window_region_frame >> simp[]
QED

Theorem extcall_tuple_window_source_state[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce ss /\
  compile_abi_encode_to_buf dst src ei se = (encoded,sen) /\
  fn_has_code se sen func /\ fn_inst_ids_distinct func /\
  ss.cs_next_var <= se.cs_next_var /\
  window_strong_result ctx func se sen encoded at av (b+32) prepared encoded_state /\
  window_phase ctx func sen sp {} [] encoded_state t /\
  window_phase ctx func ss sp (window_alloca_sites func (frag_ids se sen))
    [(b+32,LENGTH (enc at av))] s t /\ abi_encode_exec_frame func s t /\
  MEM shared (fn_insts func) /\ shared.inst_opcode = ALLOCA /\
  shared.inst_outputs = [q] /\ not_local_ptr ce es.scopes q /\
  FLOOKUP s.vs_allocas shared.inst_id = SOME (b,sz) /\
  32+LENGTH (enc at av) <= sz ==>
  stmt_state_rel ctx func ce cx es t /\
  (!name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `!name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (mp_tac (Q.INST [`st` |-> `ss`, `out` |-> `encoded`, `en` |-> `sp`,
       `len` |-> `LENGTH (enc at av)`] extcall_window_local_bytes) >> simp[]) >>
  `(ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory)` by
    (mp_tac (Q.INST [`st` |-> `ss`, `en` |-> `sp`,
       `len` |-> `LENGTH (enc at av)`] extcall_window_immutable_bytes) >> simp[]) >>
  `!i. FLOOKUP t.vs_allocas i = FLOOKUP encoded_state.vs_allocas i` by
    (qpat_assum `window_phase _ _ _ _ {} [] _ _`
       (mp_tac o MATCH_MP window_phase_effect) >>
     simp[abi_encoder_registered_effect_def] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  `!inst n pb pn. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    inst.inst_id IN window_alloca_sites func (frag_ids se sen) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(pb,pn) ==> pn = w2n n` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id IN frag_ids se sen` by fs[window_alloca_sites_def] >>
     drule_all encoder_function_alloca_shape >> strip_tac >>
     `pn = 32` by metis_tac[window_strong_result_sizes] >> gvs[dimword_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (drule_all extcall_window_source_rel >> simp[]) >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem extcall_registered_tuple_calldata_mem:
  emit_op ADD [buf; Lit 32w] ss = (dst,se) /\
  compile_abi_encode_to_buf dst argbuf ei se = (encoded,sen) /\
  emit_op ADD [encoded; Lit 4w] sen = (call_len,slen) /\
  emit_op ADD [buf; Lit 28w] slen = (call_offset,sp) /\
  fn_has_code ss se func /\ fn_has_code se sen func /\
  fn_has_code sen slen func /\ fn_has_code slen sp func /\
  fn_inst_ids_distinct func /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av tb cap s.vs_memory /\
  alloca_inv s /\ alloca_room ctx func s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ss.cs_current_bb /\
  s.vs_inst_idx = LENGTH ss.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  eval_operand argbuf s = SOME (n2w tb) /\
  (!x. buf = Var x \/ argbuf = Var x ==> not_fresh_at ss x) /\
  FLOOKUP s.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
  FLOOKUP s.vs_allocas tuple_id = SOME (tb,cap) /\
  buf_id <> tuple_id /\ buf_id < ss.cs_next_id /\
  LENGTH (enc at av) <= args_size /\
  mem_bytes_at b 32 s.vs_memory = word_to_bytes (n2w method_id : bytes32) T /\
  (!inst p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids se sen /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) ==>
    inst.inst_id <> buf_id /\ inst.inst_id <> tuple_id /\ n = 32) ==>
  ?prepared encoded_state t path_count.
    window_phase ctx func ss se {} [] s prepared /\
    window_strong_result ctx func se sen encoded at av (b+32) prepared encoded_state /\
    window_phase ctx func sen sp {} [] encoded_state t /\
    window_phase ctx func ss sp (window_alloca_sites func (frag_ids se sen))
      [(b+32,LENGTH (enc at av))] s t /\
    abi_encode_exec_frame func s t /\
    gas_path_mem ctx func s path_count (OK t) /\ mem_cont_sim ctx func s t /\
    alloca_history func t /\
    eval_operand buf t = SOME (n2w b) /\
    eval_operand call_offset t = SOME (n2w (b+28)) /\
    eval_operand call_len t = SOME (n2w (LENGTH (enc at av)+4)) /\
    FLOOKUP t.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
    read_memory (b+28) (4+LENGTH (enc at av)) t =
      DROP 28 (word_to_bytes (n2w method_id : bytes32) T) ++ enc at av /\
    (b+28)+(4+LENGTH (enc at av)) <= t.vs_alloca_next /\
    b+28 < dimword (:256) /\ LENGTH (enc at av)+4 < dimword (:256) /\
    (!ce cx es shared q.
      stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce ss /\
      MEM shared (fn_insts func) /\ shared.inst_opcode = ALLOCA /\
      shared.inst_id = buf_id /\ shared.inst_outputs = [q] /\
      not_local_ptr ce es.scopes q ==>
      stmt_state_rel ctx func ce cx es t /\
      (!name p n. local_region ce es.scopes s name p n ==>
        mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME (32w:bytes32)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_counted_mem >>
  disch_then (qx_choosel_then [`prepared`, `add_count`] strip_assume_tac) >>
  `prepared.vs_allocas = s.vs_allocas` by
    (drule window_phase_effect >>
     simp[abi_encoder_registered_effect_def,fmap_eq_flookup] >> metis_tac[]) >>
  `!p n. mem_bytes_at p n prepared.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt gen_tac >> irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{}`, `[]`] >> simp[] >> metis_tac[window_phase_effect]) >>
  `abi_encoder_window_input ei at av tb cap prepared.vs_memory` by
    (irule abi_encoder_window_input_mem_agree >>
     goal_assum (drule_at Any) >> simp[]) >>
  `alloca_inv prepared /\ alloca_room ctx func prepared /\
   ~prepared.vs_halted /\ prepared.vs_current_bb = se.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH se.cs_current_insts` by
    metis_tac[window_phase_resources,window_phase_control] >>
  `ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id` by
    metis_tac[ci_mono_emit_op,ci_mono_def,pairTheory.SND] >>
  `eval_operand argbuf prepared = SOME (n2w tb) /\
   eval_operand buf prepared = SOME (n2w b)` by
    metis_tac[window_phase_eval] >>
  `!x. argbuf = Var x \/ dst = Var x ==> not_fresh_at se x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst prepared = SOME (n2w (b+32))` by simp[word_add_n2w] >>
  `abi_encoder_window_pre ctx func se sen dst argbuf ei at av tb cap (b+32) prepared` by
    (irule (Q.INST [`args_size` |-> `args_size`, `ret_size` |-> `ret_size`,
       `buf_id` |-> `buf_id`, `tuple_id` |-> `tuple_id`]
       extcall_registered_encoder_window_pre) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     asm_rewrite_tac [] >>
     qexistsl_tac [`args_size`, `buf_id`, `ret_size`, `tuple_id`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_history func prepared` by metis_tac[gas_path_mem_allocation_state] >>
  `!x. buf = Var x ==> not_fresh_at se x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `buf_id < se.cs_next_id` by decide_tac >>
  `FLOOKUP prepared.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32)` by
    asm_rewrite_tac [] >>
  `mem_bytes_at b 32 prepared.vs_memory = word_to_bytes (n2w method_id:bytes32) T` by
    metis_tac[] >>
  drule_all extcall_encoded_calldata_suffix_resources_mem >>
  disch_then (qx_choosel_then [`encoded_state`, `t`, `suffix_count`] strip_assume_tac) >>
  `window_phase ctx func ss sp (window_alloca_sites func (frag_ids se sen))
    [(b+32,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `se`, `window_alloca_sites func (frag_ids se sen)`,
       `[(b+32,LENGTH (enc at av))]`, `prepared`] >> simp[]) >>
  `abi_encode_exec_frame func s t` by metis_tac[abi_encode_exec_frame_trans] >>
  `gas_path_mem ctx func s (add_count+suffix_count) (OK t)` by
    metis_tac[gas_path_mem_then] >>
  `!ce cx es shared q.
    stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce ss /\
    MEM shared (fn_insts func) /\ shared.inst_opcode = ALLOCA /\
    shared.inst_id = buf_id /\ shared.inst_outputs = [q] /\
    not_local_ptr ce es.scopes q ==>
    stmt_state_rel ctx func ce cx es t /\
    (!name p n. local_region ce es.scopes s name p n ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory)` by
    (rpt gen_tac >> strip_tac >>
     `32+LENGTH (enc at av) <= MAX args_size ret_size+32` by
       (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
     mp_tac (Q.INST [`src` |-> `argbuf`, `sz` |-> `MAX args_size ret_size+32`]
       extcall_tuple_window_source_state) >> asm_rewrite_tac []) >>
  qexistsl_tac [`prepared`, `encoded_state`, `t`, `add_count+suffix_count`] >>
  asm_rewrite_tac [] >> metis_tac[mem_cont_sim_trans]
QED
