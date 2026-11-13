(* Overlap-safe bytestring stores at a memory assignment destination. *)
Theory assignPlaceBytestringContinuationMem
Ancestors
  assignPlaceMemoryContinuationMem placeTypedCopyPrimitiveMem
  placeMemoryCopyEffect exprSimHyps stmtLowering valueCopy compileEnv
  fragGasPathMem venomState context valueCopyBytes

Theorem assign_place_bytestring_continuation_mem:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  compile_assign_value cenv dst_op LocMemory op F NONE dty sty dyn n sa = ((),sb) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand op s = SOME sw /\ eval_operand dst_op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  local_ptrs_reserved cenv sa /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `compile_store_memory_typed cenv dst_op dty op sty sa = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def, compile_store_memory_def] >>
     simp[Once compile_store_memory_typed_def]) >>
  `w2n w + type_memory_size dtv <= s.vs_alloca_next /\
   w2n w + type_memory_size dtv < dimword (:256)` by
    (irule assign_memory_destination_bounds >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  drule_all typed_memory_bytestring_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule assign_direct_effect_state >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >> gvs[typed_copy_effect_def]
QED
