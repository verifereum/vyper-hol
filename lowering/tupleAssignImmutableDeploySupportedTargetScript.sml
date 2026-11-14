(* Supported mutable tuple heads reuse the shared marked place step. *)
Theory tupleAssignImmutableDeploySupportedTarget
Ancestors
  tuplePlaceHeadOpen stmtSimForRounds tuplePlaceHeadGas tuplePlaceOpen supportedStmts targetPlaceLive
  targetPlaceSimCases exprSimDefs stmtSimDefs stmtSimProps
  gasSummary gasOutcome fragGasMode fragGasPath freshWrites
  vyperState vyperInterpreter

Theorem tuple_immutable_mutable_head_outcome:
  tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
  supported_target tops bindings bt /\
  ~block_is_terminated sp /\ target_pre cenv cx env bt es /\
  target_sim ctx func cenv cx env bt es /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\ ~immutable_root cx bt /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
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
     (case FST (SND r) of SOME l => l | NONE => LocMemory)
     (EL i elems)
     (is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))
     NONE (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) (EL i ltys)
     (type_memory_bytes cenv
       (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))) sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (assign_tuple_targets cx (BaseTarget bt) (EL i vs)) (es,s0)
    (\H res ff t. res = INL () /\ ~block_is_terminated sb /\
      expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx st0 ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
        stmt_state_rel H ctx func cenv cx ff t /\
        storage_well_formed_on cx ff (FST H) /\
      (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
      (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      alloca_frame cenv es sp s0 cenv ff t)
    (\H res ff r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (supported_expr tops) (target_indices bt)` by
    (Cases_on `bt` >> gvs[supportedStmtsTheory.supported_target_def,
                         targetPlaceLiveTheory.target_indices_def]
     >~ [`SubscriptTarget root key`]
     >- (Cases_on `root` >> gvs[targetPlaceLiveTheory.target_indices_def]) >>
     rename1 `AttributeTarget root fld` >>
     Cases_on `root` >> gvs[targetPlaceLiveTheory.target_indices_def]) >>
  `!p. ignore_bind (write_place cx p (EL i vs)) (return ()) =
       write_place cx p (EL i vs)` by
    (gen_tac >> simp[FUN_EQ_THM] >> gen_tac >>
     Cases_on `write_place cx p (EL i vs) x` >>
     rename1 `_ = (rr,ss)` >> Cases_on `rr` >>
     simp[ignore_bind_def, bind_def, return_def]) >>
  `assign_tuple_targets cx (BaseTarget bt) (EL i vs) =
   bind (eval_target_place cx bt)
     (\p. ignore_bind (write_place cx p (EL i vs)) (return ()))` by
    simp[Once evaluate_def] >>
  pop_assum (once_rewrite_tac o single) >>
  irule (Q.INST [`sb` |-> `sb`, `env` |-> `env`, `tops` |-> `tops`,
    `tvs` |-> `tvs`] (SRULE [LET_THM] tuple_place_head_gas_continuation_open)) >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_return] >>
  qexistsl [`tops`,`env`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_return_path >> qexists `t` >> conj_tac
  >~ [`gas_marked_path _ _ _ _ _ _`]
  >- (simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >>
      fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx ff t /\
   storage_well_formed_on cx ff (FST H)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  `storage_well_formed_on cx (ff with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx ff (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  simp[]
QED
