(* Source-typed public boundary; scalar values need no source buffer contract. *)
Theory bodyPtrMakeArrayScalarEndpoint
Ancestors
  bodyPtrMakeArrayScalarUnwrap bodyPtrMakeArrayScalarSource
  bodyPtrMakeArrayScalarCoverage exprSimOperands bodyPtrMakeArrayScalarSemantics
  bodyPtrDefs loweringPosts context compileEnv venomState ptrDiscipline

Theorem scalar_unwrap_ptr_endpoint:
  unwrap_value ce vv sm = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 es' tv vv s /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tv,es') /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx es' G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  not_fresh_at sm dst /\ ptr_covers G tn dst s n ==>
  ?ty Gf tnf sf.
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v op sf /\
    eval_operand op sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf op = {} /\
    ptr_val_ok cx (expr_type e) v op Gf tnf sf /\
    ghost_inv d ce cx es' Gf tnf sf /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var dst sf = lookup_var dst s /\ ptr_covers Gf tnf dst sf n
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  drule_all scalar_source_result_typed >> strip_tac >>
  qexists_tac `ty` >> simp[] >>
  Cases_on `vv`
  >- (drule_all scalar_stack_unwrap_endpoint >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]) >>
  rename1 `LocatedValue t p` >>
  drule_all scalar_unwrap_typed_instruction >>
  disch_then (qx_choose_then `opc` (qx_choose_then `tmp`
    (qx_choose_then `bb` (qx_choose_then `a`
      (map_every assume_tac o CONJUNCTS))))) >> gnvs[] >>
  `not_local_ptr ce es'.scopes tmp` by
    (irule fresh_not_local_ptr >> qexists_tac `sm` >> simp[] >> metis_tac[]) >>
  `(!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\ tmp <> dst`
    by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sm.cs_next_id opc [p.ptr_operand] [tmp]) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   s.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[] >>
  reverse (Cases_on `p.ptr_location = LocMemory`)
  >- (qpat_assum `sb.cs_current_bb = sm.cs_current_bb`
        (fn th => rewrite_tac[GSYM th]) >>
      irule scalar_external_unwrap_endpoint >> simp[] >> metis_tac[]) >>
  `ptr_mem_ok cx (expr_type e) v p.ptr_operand G tn s /\
   op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  drule_all scalar_memory_source_coverage >> strip_tac >> gvs[] >>
  qpat_assum `sb.cs_current_bb = sm.cs_current_bb`
    (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_memory_unwrap_endpoint >> simp[] >> metis_tac[]
QED

(* Integration audit (no additional source invariant):
   The marked child-success branch in the S1 reference
   exprSimAggregateLoops, aggregate_make_tuple_sim[child_success], retains
   eval_expr cx h (es with gas_obs := gas_explicit m1 s0.vs_gas_readings)
     = (INL tv, es1)
   and expr_body_pre at exactly that marked initial source state (lines
   556-562).  Its read_result at es1 is obtained at line 572.  The subsequent
   destination ADD (child_steps, lines 605-621) changes only the target state,
   preserving these source facts and vv_post.  Thus a pointer loop port must
   retain the marked initial state when calling this wrapper; substituting
   the unmarked es is neither needed nor justified.  Array elements use
   this exact tuple loop via compile_make_array_elems_as_tuple and
   aggregate_make_array_elems_sim (reference lines 1112-1129).
   Unlike semantic typing,
   allocas_from 0 is unconditional: allocation addresses are natural numbers;
   the proof above discharges it at every consumer state.  No aggregate
   caller is asked to carry that implementation-side load premise. *)
