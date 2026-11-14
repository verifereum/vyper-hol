Theory assignEffectfulIndexBytesCopy
Ancestors
  exprSimIfExpWidenedBytesCounted exprSimCopy stmtSimDefs
  context compileEnv exprLoweringProps valueCopyBytes
  venomState loweringStateRelDefs valueEncoding

Theorem assign_effectful_bytes_copy_path:
  compile_store_memory ce src dst pty pty sa = ((),sb) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  is_bytestring_type pty /\ evaluate_type (get_tenv cx) pty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
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
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[compile_store_memory_def, is_bytestring_word_type] >>
  drule_all bytestring_store_allocated_counted_frame >> strip_tac >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
               local_region ce es.scopes s name b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_frame ce es origin s ce es t` by
    (simp[alloca_frame_def] >> rpt strip_tac
     >- (qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ _ = _` irule >>
         metis_tac[regions_disjoint_def]) >>
     metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand dst t = SOME d` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED
