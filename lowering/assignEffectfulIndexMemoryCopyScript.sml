Theory assignEffectfulIndexMemoryCopy
Ancestors
  assignEffectfulIndexBytesCopy placeMemoryTypedPrimitive exprSimBufferStore
  valueCopy valueEncodingProps stmtSimDefs context compileEnv
  exprLoweringProps venomState loweringStateRelDefs venomMemDefs
  fragGasMode exprSimCopy exprSimAggregateChildren

Theorem assign_effectful_memory_copy_path:
  compile_store_memory ce src dst pty pty sa = ((),sb) /\
  ~is_word_type pty /\ ~is_bytestring_type pty /\
  type_memory_bytes ce pty = type_memory_size tv /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_size tv < dimword (:256) /\ type_memory_size tv <= N /\
  FLOOKUP s.vs_allocas aid = SOME (w2n d,N) /\
  origin.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= w2n d \/ w2n d+N <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n d) N) /\
  (!id off n. id < origin.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (off,n) ==>
    regions_disjoint off n (w2n d) N) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    val_in_memory tv v (w2n d) t.vs_memory /\
    stmt_state_rel ctx func ce cx es t /\
    eval_operand dst t = SOME d /\
    FLOOKUP t.vs_allocas aid = SOME (w2n d,N) /\
    (!name b sz. local_region ce es.scopes t name b sz ==>
      b+sz <= w2n d \/ w2n d+N <= b) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    alloca_frame ce es origin s ce es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_copy_memory dst src (type_memory_size tv) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `val_in_memory tv v (w2n d) t.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_relocate >>
     simp[] >> qexistsl_tac [`s.vs_memory`, `type_memory_size tv`, `w2n w`] >> simp[]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule aggregate_store_control_frame >>
     qexistsl_tac [`w2n d`, `N`, `s`, `sa`] >> gvs[] >>
     rpt conj_tac
     >- metis_tac[]
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
               local_region ce es.scopes s name b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_frame ce es origin s ce es t` by
    (simp[alloca_frame_def] >> rpt strip_tac
     >- (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
         `regions_disjoint off sz (w2n d) N` by metis_tac[] >>
         gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  `eval_operand dst t = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def] >>
     gvs[venom_state_component_equality]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED
