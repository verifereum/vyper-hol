(* Non-normalizing immutable aggregate stores at one framed endpoint.
   Direct copies frame their padded write extent, not the value footprint. *)
Theory tupleAssignImmutableDeployAggregatePlain
Ancestors
  immutableAssignStore immutableAssignStoreLength

Theorem tuple_immutable_direct_aggregate_store:
  compile_assign_value cenv dst LocCode src F NONE dty sty L sa = ((),sb) /\
  dty = sty /\ ~is_bytestring_type dty /\
  n = (if L <= 32 then 1 else (L+31) DIV 32) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k /\
  stmt_state_rel ctx func cenv cx es s ==>
  ?r q. r = s /\ stmt_state_rel ctx func cenv cx es r /\
    gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory dtv v b q.vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at b (type_memory_size dtv) q.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
    (!p len. regions_disjoint p len b (32*n) ==>
      mem_bytes_at p len q.vs_memory = mem_bytes_at p len s.vs_memory) /\
    LENGTH r.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule (Q.INST [`imm` |-> `cenv.ce_imm_alloca`,
    `copy_size` |-> `mem_size`] immutable_assign_direct_store) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `k <= 32*n`)) >>
  disch_then (drule_at (Pat `eval_operand dst s = _`)) >>
  disch_then (qspecl_then [`ctx`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `compile_imm_store_words cenv.ce_imm_alloca src dst n 0 sa = ((),sb)` by
    (asm_rewrite_tac[] >> irule immutableDeployOperandTransferTheory.immutable_store_suffix_words >>
     gvs[stmtLoweringTheory.compile_assign_value_def,
         compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]) >>
  drule_all immutable_assign_store_words_memory_length >> strip_tac >>
  qexistsl_tac [`s`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gvs[venomStateTheory.venom_state_component_equality,
      loweringStateRelDefsTheory.regions_disjoint_def,
      exprLoweringPropsTheory.same_blocks_def,
      venomStateTheory.lookup_var_def] >> gvs[]
QED

Theorem tuple_immutable_bytestring_aggregate_store:
  compile_assign_value cenv dst LocCode src F NONE dty sty L sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory /\
  a + val_footprint stv v < dimword (:256) /\
  b + type_memory_size dtv < dimword (:256) /\
  (a + val_footprint stv v <= b \/ b + type_memory_size dtv <= a) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s ==>
  ?r q. r = s /\ stmt_state_rel ctx func cenv cx es r /\
    gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory dtv v b q.vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at b (type_memory_size dtv) q.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
    (!p len. regions_disjoint p len b (type_memory_size dtv) ==>
      mem_bytes_at p len q.vs_memory = mem_bytes_at p len s.vs_memory) /\
    LENGTH r.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule immutable_assign_bytestring_store >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`ctx`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`s`, `q`] >>
  gvs[venomStateTheory.venom_state_component_equality,
      loweringStateRelDefsTheory.regions_disjoint_def] >> gvs[]
QED
