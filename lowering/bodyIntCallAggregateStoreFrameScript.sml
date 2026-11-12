(* Complete data-state frames at the counted compatible-store endpoint. *)
Theory bodyIntCallAggregateStoreFrame
Ancestors
  bodyIntCallAggregateStoreLanding exprSimAggregateChildren
  bodyIntCallWidenCopy bodyIntCallLiteralLanding localMemoryStorePath
  placeMemoryPrimitiveForward entrySinkExtraction valueCopyBytes valueEncoding
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts venomState venomExecSemantics
  venomInst words list rich_list fragGasMode instIdxIndep finite_map

Theorem protected_compatible_store_frame_landing:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  (!b n. P b n ==> regions_disjoint b n (w2n dw)
     (MIN (type_memory_size stv) (type_memory_size dtv))) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (local_ptrs_reserved ce sa ==>
      !name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all protected_compatible_store_run >> strip_tac >>
  drule_all compatible_store_no_gas >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[eval_op_inst_idx, lookup_var_def, venom_state_component_equality] >>
  strip_tac >> irule local_region_reserved_operands >>
  qexists_tac `\op. ?x. op = Var x /\ not_fresh_at sa x` >>
  fs[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem protected_compatible_store_state_landing:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  (!b n. P b n ==> regions_disjoint b n (w2n dw) (type_memory_size dtv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint b sz (w2n dw) (type_memory_size dtv)) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    stmt_state_rel ctx func ce cx es u /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (!name b sz. local_region ce es.scopes u name b sz <=> local_region ce es.scopes s name b sz) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST
    [`P` |-> `\b n. regions_disjoint b n (w2n dw) (type_memory_size dtv)`,
     `scopes` |-> `es.scopes`] (SPEC_ALL protected_compatible_store_frame_landing)) >>
  (impl_tac >- (simp[] >> simp[regions_disjoint_def, arithmeticTheory.MIN_ALT] >> rpt strip_tac >>
    Cases_on `type_memory_size stv <= type_memory_size dtv` >> gvs[])) >>
  strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule aggregate_store_control_frame >>
     qexistsl_tac [`w2n dw`, `type_memory_size dtv`, `s`, `sa`] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED
