(* Effectful mutable target evaluation, conditional on endpoint transport.
   Reachability of the transport contract is deliberately not asserted here. *)
Theory tupleAssignImmutableDeployEffectful
Ancestors
  tupleAssignImmutableDeployEffectfulBind tupleAssignImmutableDeployLoadedStore

Theorem tuple_effectful_head_with_transport:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
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
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  (!marks p mid s.
    gas_marked_exec F (ctx,func) (eval_target_place cx bt)
      (es,s0) marks (INL p) mid (OK s) /\
    target_post ctx func cenv cx es sp sa s0 (mid with gas_obs := [])
      (PlaceR p) (Type (EL i tys)) r s ==>
    tuple_place_head ctx func cenv cx (mid with gas_obs := []) lo sa
      tys ltys ltvs vs elems w i s /\
    MAP FDOM mid.scopes = MAP FDOM es.scopes /\
    (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (!dw loc. eval_operand (FST r) s = SOME dw /\
      FST (SND r) = SOME loc /\ loc = LocMemory /\ ~EVERY is_word_type ltys ==>
      w2n w + type_memory_size_list ltvs <= w2n dw \/
      w2n dw + type_memory_size (EL i tvs) <= w2n w)) /\
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
  irule tuple_effectful_head_bind_conditional >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ (TupleT tys) = _` (irule_at Any) >>
  qexists `sb` >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule tuple_loaded_mutable_store_step >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_sim_inv _ _ _ ee` (irule_at Any) >>
      qpat_assum `evaluate_type _ (TupleT tys) = _` (irule_at Any) >>
      qexists `dst` >>
      simp[listTheory.EVERY_NOT_EXISTS, combinTheory.o_DEF]) >>
  gvs[]
QED
