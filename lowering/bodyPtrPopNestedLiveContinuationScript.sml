Theory bodyPtrPopNestedLiveContinuation
Ancestors
  bodyPtrPopNestedLiveEntry bodyPtrPopNestedLiveSuffixFrame bodyPtrPopNestedLiveSuffix
  bodyPtrPopNestedLivePositivePost exprSimPopNestedLocalProps
  gasSummaryComposePtr fragGasPathPtr bodyPtrDefs
  vyperState venomState compileEnv finite_map exprSimDefs venomExecSemantics fragExec

Theorem pop_empty_memory_marked_ptr:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) /\
  gas_path_ptr D 0 ctx func PG G tn s 0 H tf r ==>
  gas_marked_exec_ptr D (ctx,func) PG (pop_place cx (MemoryPlace id path))
    (es,s,G,tn) [] (INR (Error (RuntimeError "pop empty memory array"))) es H tf r
Proof
  strip_tac >> rewrite_tac[gas_marked_exec_ptr_def] >>
  simp[] >> gen_tac >> irule pop_memory_place_live_empty >> simp[]
QED

Theorem pop_positive_memory_marked_ptr:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  gas_path_ptr D 0 ctx func PG G tn s 0 H tf r ==>
  gas_marked_exec_ptr D (ctx,func) PG (pop_place cx (MemoryPlace id path))
    (es,s,G,tn) []
    (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs-1))]))))
    (es with scopes := pre ++ sc |+ (id,entry with
      <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest)
    H tf r
Proof
  strip_tac >> rewrite_tac[gas_marked_exec_ptr_def] >> simp[] >>
  gen_tac >> irule pop_memory_place_live >> simp[]
QED

Theorem pop_empty_memory_continuation:
  gas_marked_exec_ptr D (ctx,func) PG (eval_target_place cx bt)
    (es,s0,G0,tn0) marks (INL (MemoryPlace id path)) mid G tn (OK s) /\
  find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) /\
  compile_dynarray_pop (Var src) 32 scale ctor imm LocMemory sm = (dst,sb) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = 0w ==>
  ?res fin H tf rr.
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (eval_target_place cx bt) (pop_place cx))
      (es,s0,G0,tn0) marks res fin H tf rr /\
    exit_result rr /\ expr_exit res rr
Proof
  strip_tac >> drule_all pop_memory_suffix_empty_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty memory array"))`,
    `mid with gas_obs := []`, `H`, `tf`,
    `Abort Revert_abort (revert_state (set_returndata [] t))`] >>
  conj_tac
  >- (irule (SRULE [listTheory.APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      goal_assum drule >>
      irule pop_empty_memory_marked_ptr >> simp[] >> metis_tac[]) >>
  simp[expr_exit_def, exit_result_def]
QED
