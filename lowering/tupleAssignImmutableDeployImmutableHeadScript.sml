(* Standalone direct immutable target outcome. *)
Theory tupleAssignImmutableDeployImmutableHead
Ancestors
  tupleAssignImmutableDeployHead tuplePlaceHeadGas tuplePlaceHead
  stmtSimForRounds gasOutcome gasSummary fragGasMode fragGasPath
  vyperInterpreter vyperState exprSimHypsDefs stmtSimDefs compileEnv

Theorem tuple_immutable_head_outcome:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  ~block_is_terminated sp /\ body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  well_typed_target env (TopLevelNameTarget (src,id)) (EL i tys) /\
  call_evaluation_safe cx (int_calls_target (TopLevelNameTarget (src,id))) /\
  compile_get_target_ptr compile_expr cenv (TopLevelNameTarget (src,id)) sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (if is_word_type (EL i ltys) then
     if is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) then
       compile_store_at_loc cenv.ce_imm_alloca (FST r) (EL i elems) (FST (SND r))
     else emit_void INVALID []
   else compile_assign_value cenv (FST r)
     (case FST (SND r) of SOME l => l | NONE => LocMemory) (EL i elems)
     (is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))
     NONE (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) (EL i ltys)
     (type_memory_bytes cenv
       (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))) sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (src,id))) (EL i vs))
    (es,s0)
    (\res ff t. res = INL () /\ ~block_is_terminated sb /\
      expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
      (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_frame cenv es sp s0 cenv ff t)
    (\res ff r. expr_exit res r)
Proof
  strip_tac >>
  `!p. ignore_bind (write_place cx p (EL i vs)) (return ()) =
       write_place cx p (EL i vs)` by
    (gen_tac >> simp[FUN_EQ_THM] >> gen_tac >>
     Cases_on `write_place cx p (EL i vs) x` >>
     rename1 `_ = (rr,ss)` >> Cases_on `rr` >>
     simp[ignore_bind_def, bind_def, return_def]) >>
  `assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (src,id))) (EL i vs) =
   bind (eval_target_place cx (TopLevelNameTarget (src,id)))
     (\p. ignore_bind (write_place cx p (EL i vs)) (return ()))` by
    simp[Once evaluate_def] >>
  pop_assum (once_rewrite_tac o single) >>
  irule (Q.INST [`sb` |-> `sb`, `env` |-> `env`, `tops` |-> `tops`,
    `ity` |-> `ity`, `tvs` |-> `tvs`] tuple_immutable_head_gas_continuation_open) >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
  simp[LET_THM] >>
  qexistsl [`tops`,`ity`,`env`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_return_path >> qexists `t` >> simp[] >>
  simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >>
  fs[tuple_place_head_def]
QED
