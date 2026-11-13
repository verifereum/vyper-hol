(* Supported mutable tuple heads reuse the shared marked place step. *)
Theory tupleAssignImmutableDeploySupportedTarget
Ancestors
  tuplePlaceHeadGas tuplePlaceOpen supportedStmts targetPlaceLive
  targetPlaceSimCases exprSimDefs stmtSimDefs stmtSimProps
  gasSummary gasOutcome fragGasMode fragGasPath freshWrites
  vyperState vyperInterpreter

Theorem tuple_immutable_mutable_head_outcome:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
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
  gas_outcome F (cx_tops cx) (ctx,func)
    (assign_tuple_targets cx (BaseTarget bt) (EL i vs)) (es,s0)
    (\res ff t. res = INL () /\ ~block_is_terminated sb /\
      expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
      (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
      (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      alloca_frame cenv es sp s0 cenv ff t)
    (\res ff r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (supported_expr tops) (target_indices bt)` by
    (Cases_on `bt` >> gvs[supportedStmtsTheory.supported_target_def,
                         targetPlaceLiveTheory.target_indices_def]
     >~ [`SubscriptTarget root key`]
     >- (Cases_on `root` >> gvs[targetPlaceLiveTheory.target_indices_def]) >>
     rename1 `AttributeTarget root fld` >>
     Cases_on `root` >> gvs[targetPlaceLiveTheory.target_indices_def]) >>
  `expr_sim_inv cenv cx env es` by fs[targetPlaceSimTheory.target_pre_def] >>
  `target_indices_pre cenv cx env bt` by fs[targetPlaceSimTheory.target_pre_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (drule_all tuplePlaceTargetGasTheory.tuple_place_target_gas_admissible >> simp[]) >>
  `type_place_target env bt = SOME (Type (EL i tys))` by
    fs[vyperTypeSystemTheory.well_typed_target_def] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
    (\res ee t. ?p. res = INL p /\
      target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r t /\
      t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (irule target_place_sim >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  simp[Once evaluate_def] >>
  irule tuple_place_gas_outcome_bind_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >>
    gvs[exprSimDefsTheory.expr_exit_def] >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ marks (INL p) mid (OK s)` >>
  `~s.vs_halted` by
    (fs[gas_marked_exec_def] >> drule gas_marked_path_exec >>
     strip_tac >> metis_tac[gas_path_normal]) >>
  mp_tac (SRULE [LET_THM] tuple_place_marked_head_step) >>
  impl_tac >- simp[] >> strip_tac >>
  `arg_type_fits (EL i ltys) (EL i tys)` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_index_fit >> simp[]) >>
  `~block_is_terminated sb` by
    (irule (SRULE [LET_THM] tuple_place_success_store_open) >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
     simp[] >> qexistsl [`EL i ltys`, `EL i elems`] >>
     gvs[SRULE [LET_THM] tuple_place_success_store_open]) >>
  `!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==>
     lookup_var x t = SOME v` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by
       (irule not_fresh_at_mono >> qexists `sp` >> simp[]) >>
     fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  `!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
     FLOOKUP t.vs_allocas id = SOME entry` by
    (rpt strip_tac >> fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl [`INL ()`,`ff`,`OK t`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >> rpt strip_tac >>
      drule tuplePlaceSourceGasTheory.tuple_place_write_gas_obs >> simp[]) >>
  simp[]
QED
