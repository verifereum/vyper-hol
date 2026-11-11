(* Successful head continuations retain compiler openness. *)
Theory tuplePlaceHeadOpen
Ancestors
  tuplePlaceHeadGas tuplePlaceOpen tuplePlacePointerReady
  tuplePlaceTargetGas targetPlaceSimCases gasSummary fragGasMode fragGasPath

Theorem tuple_place_head_gas_continuation_open:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  ~block_is_terminated sp /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
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
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys;
       arr = case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
         | _ => NONE
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) arr (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  (!ff t. ~block_is_terminated sb /\ expr_sim_inv cenv cx env ff /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv es sp s0 cenv ff t ==>
    gas_outcome F (cx_tops cx) (ctx,func) next (ff with gas_obs := [],t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt)
      (\p. ignore_bind (write_place cx p (EL i vs)) next)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[targetPlaceSimTheory.target_pre_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule tuple_place_target_gas_admissible >> metis_tac[]) >>
  `type_place_target env bt = SOME (Type (EL i tys))` by
    fs[vyperTypeSystemTheory.well_typed_target_def] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
    (\res ee t. ?p. res = INL p /\
      target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r t /\
      t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (irule target_place_sim >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  irule tuple_place_gas_outcome_bind_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >>
    gvs[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  `arg_type_fits (EL i ltys) (EL i tys)` by
    (drule_all tuple_place_index_fit >> simp[]) >>
  `~block_is_terminated sb` by
    (irule (SRULE [LET_THM] tuple_place_success_store_open) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def] >> drule gas_marked_path_exec >>
     strip_tac >> metis_tac[gas_path_normal]) >>
  drule_all (SRULE [LET_THM] tuple_place_marked_head_step) >> strip_tac >>
  irule tuple_place_write_gas_prefix >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.target_post_def] >> strip_tac >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED
