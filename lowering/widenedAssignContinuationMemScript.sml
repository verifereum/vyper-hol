(* Counted updates of existing memory locals after a widened physical copy. *)
Theory widenedAssignContinuationMem
Ancestors
  widenedAssignmentPreparationMem widenedLocalContinuationMem
  widenedLocalEndpointMem widenedDeclareContinuationMem stmtSimAssignSource
  gasSummary fragGasMode vyperState finite_map exprLoweringProps exprSimSource venomState compileEnv
Libs monadsyntax

Theorem typed_copy_assign_marked_mem[local]:
  stmt_state_rel ctx fn ce cx es u /\
  find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p u = SOME dw /\ local_ptrs_reserved ce sa /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u) /\
  (!b n. b+n <= w2n dw \/ w2n dw+type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory /\
  gas_path_mem ctx fn s g (OK t) /\
  (!tail. write_place cx (MemoryPlace id []) v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  let ff = es with scopes :=
    pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest in
  gas_marked_exec T (ctx,fn) (write_place cx (MemoryPlace id []) v) (es,s)
    (REPLICATE g F) (INL ()) ff (OK t) /\
  stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac
  >- (irule gas_marked_exec_no_source_read >> simp[gas_marked_path_def]) >>
  `stmt_state_rel ctx fn ce cx
    (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest) t` by
    (irule typed_copy_assign_state >> metis_tac[]) >>
  gvs[stmt_state_rel_def, compileEnvTheory.state_rel_gas_obs] >> gvs[]
QED

Theorem widened_assign_copy_continuation_mem:
  compile_assign_value ce (Var p) LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\ entry.type = dtv /\
  local_region ce es.scopes s id (w2n dw) sz /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. write_place cx (MemoryPlace id []) v (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
      with gas_obs := tail)) ==>
  ?marks ff t.
    gas_marked_exec T (ctx,fn) (write_place cx (MemoryPlace id []) v) (es,s)
      marks (INL ()) ff (OK t) /\
    ff = es with scopes :=
      pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest /\
    stmt_state_rel ctx fn ce cx (ff with gas_obs := []) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ return_buf_frame d ce sb t /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `(!x. src = Var x \/ Var p = Var x ==> not_fresh_at sa x)` by
    (rpt strip_tac >> gvs[]) >>
  Q.SUBGOAL_THEN
    `(?aid. FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id) \/
      (?name. local_region ce es.scopes s name (w2n dw) sz)` assume_tac
  >- metis_tac[] >>
  drule_all widened_local_copy_endpoint_mem >> strip_tac >>
  `lookup_var p u = SOME dw` by
    (first_x_assum (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     simp[eval_operand_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u` by metis_tac[] >>
  `val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory` by simp[] >>
  `!b n. b+n <= w2n dw \/ w2n dw+type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n u.vs_memory` by metis_tac[] >>
  drule_all typed_copy_assign_marked_mem >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qexistsl_tac [`REPLICATE g F`, `es with scopes :=
    pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest`, `t`] >>
  simp[] >> gvs[]
QED

Theorem retained_assignment_source_ready[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec T (ctx,fn) (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) ==>
  ?pre scope entry rest.
    find_containing_scope id ee.scopes = SOME (pre,scope,entry,rest) /\
    find_containing_scope id (ee with gas_obs := []).scopes =
      SOME (pre,scope,entry,rest) /\
    !tail. write_place cx (MemoryPlace id []) v
      ((ee with gas_obs := []) with gas_obs := tail) =
      (INL (), ((ee with gas_obs := []) with scopes :=
        pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `?pre scope entry rest.
    find_containing_scope id ee.scopes = SOME (pre,scope,entry,rest) /\
    entry.assignable /\
    !tail. write_place cx (MemoryPlace id []) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (scope |+ (id,entry with <|value := v; popped := []|>))::rest)
        with gas_obs := tail)` by
    (irule assign_local_continuation_all_tails >>
     goal_assum (drule_at (Pat `gas_admissible _ _ _`)) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     fs[gas_marked_exec_def, vyperStateTheory.bind_def]) >>
  qexistsl_tac [`pre`, `scope`, `entry`, `rest`] >> gvs[]
QED
