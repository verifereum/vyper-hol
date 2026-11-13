(* Stores into an argument buffer, framed from before its allocation. *)
Theory bodyIntCallStageEndpointStore
Ancestors
  bodyIntCallJointAggCore bodyIntCallFamCallIntStageStore bodyIntCallJointContract
  bodyIntCallFamCallIntStageAllocation

Theorem intcall_stage_physical_store_cont:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_cont fp ce env es0 sa s0 es su s /\
  compile_store_memory ce src dst dty sty su = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa.cs_next_id <= inst.inst_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sb.cs_next_var /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     regions_disjoint a n (w2n dw) (type_memory_size dtv)) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==>
     regions_disjoint a n b k) /\
  (~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
    !sw. eval_operand src s = SOME sw ==>
      regions_disjoint (w2n sw) (type_memory_size stv)
        (w2n dw) (type_memory_size dtv) /\
      w2n sw + type_memory_size stv < dimword (:256)) /\
  fn_has_code su sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\ val_wf dtv v /\
    intcall_expr_cont fp ce env es0 sa s0 es sb u /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
    eval_operand dst u = SOME dw /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    (!name a n. local_region ce es.scopes u name a n ==>
       regions_disjoint a n (w2n dw) (type_memory_size dtv))
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es su s /\ ~s.vs_halted /\
   s.vs_current_bb = su.cs_current_bb /\
   s.vs_inst_idx = LENGTH su.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce su /\ expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_expr_res_def] >>
  `!ty tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)` by
    metis_tac[intcall_owned_destination_immutable_clear] >>
  `val_wf dtv v /\ val_wf stv v` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `acyclic_struct_metadata ce.ce_struct_fields /\
   sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv fp.jc_cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[bodySimTheory.body_inv_def, exprSimHypsDefsTheory.expr_sim_inv_def] >>
     metis_tac[]) >>
  fs[loweringPostsTheory.expr_val_rel_def] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    intcall_stage_store_effect >>
  disch_then (drule_at (Pat `eval_operand src s = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst s = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspec_then `v` mp_tac) >>
  (impl_tac >- (simp[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
    `~is_word_type sty` by
      metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
    fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])) >>
  strip_tac >>
  `alloca_inv s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `intcall_expr_cont fp ce env es0 sa s0 es sb u` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)
       intcall_owned_store_cont >>
     disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     disch_then irule >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name a n. local_region ce es.scopes u name a n <=>
      local_region ce es.scopes s name a n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `su` >> fs[placeMemoryCopyEffectTheory.typed_copy_effect_def]) >>
  qexists `u` >> simp[] >>
  conj_tac >- metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_path] >>
  conj_tac >- fs[placeMemoryCopyEffectTheory.typed_copy_effect_def] >>
  conj_tac >- metis_tac[bodyIntCallCopySharpDynamicTheory.typed_copy_effect_operand_preserved] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED
