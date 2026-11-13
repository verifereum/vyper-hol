(* Saved scalar tuple members survive an effectful destination evaluation. *)
Theory assignScalarTargetFramePtr
Ancestors
  bodyPtrSubscriptSeamArrayMemoryFrame exprSimSubscriptArrayFrame
  exprSimProps bodyPtrDefs loweringPosts context vyperInterpreter vyperState
  ptrDiscipline venomState loweringStateRelDefs
  vyperTypeEvalSoundness vyperExprNoControl targetPlaceSimCases gasContext
  exprSimHypsDefs vyperTypeInvariants vyperTypeExprSoundness

Theorem scalar_value_target_frame_ptr:
  expr_val_at cenv cx ty lo sa es v op s /\
  ptr_val_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ dynarray_free tv /\
  expr_sim_inv cenv cx env es /\
  wb_frame cenv es ee sa s t /\ ghost_kept cenv es sa G tn s H tt /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  eval_operand op t = eval_operand op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  op_taint tt op = op_taint tn op /\ op_prov H op = op_prov G op /\
  local_ptrs_reserved cenv sa /\ local_ptrs_rel func cenv es.scopes s /\
  sa.cs_next_id <= sb.cs_next_id ==>
  ptr_val_ok cx ty v op H tt t /\
  expr_val_at cenv cx ty lo sb ee v op t
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- gvs[ptr_val_ok_def,expr_val_at_def] >>
  `vv_at cenv cx ty lo sa es (Value v)
    (LocatedValue ty (mk_ptr op LocMemory)) s` by
    (simp[vv_at_def,mk_ptr_def,read_result_def,return_def] >>
     gvs[expr_val_at_def] >> metis_tac[local_place_at_value]) >>
  `ptr_mem_ok cx ty v op H tt t` by
    (mp_tac (Q.INST [`p` |-> `mk_ptr op LocMemory`, `r` |-> `Value v`,
       `sa` |-> `lo`, `sb` |-> `sa`, `s'` |-> `t`,
       `G'` |-> `H`, `tn'` |-> `tt`]
       (SPEC_ALL vv_at_ptr_mem_frame)) >>
     simp[mk_ptr_def,read_result_def,return_def] >>
     impl_tac >- (gvs[ptr_val_ok_def] >> metis_tac[]) >> simp[]) >>
  `vv_at cenv cx ty lo sb ee (Value v)
    (LocatedValue ty (mk_ptr op LocMemory)) t` by
    (mp_tac (Q.INST [`sa` |-> `lo`, `sb` |-> `sa`, `sc` |-> `sb`,
       `es'` |-> `ee`, `s'` |-> `t`, `r` |-> `Value v`,
       `p` |-> `mk_ptr op LocMemory`] (SPEC_ALL vv_at_located_frame)) >>
     (impl_tac >- (simp[mk_ptr_def] >> metis_tac[])) >> simp[]) >>
  conj_tac >- gvs[ptr_val_ok_def] >>
  drule vv_at_memory_val_at >> simp[mk_ptr_def,read_result_def,return_def]
QED

(* Typed targets can fail only in the source exits represented by the compiler. *)
Theorem typed_tuple_target_admissible_ptr:
  expr_sim_inv cenv cx env es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  `env_consistent env cx (es with gas_obs := gs) /\
   state_well_typed (es with gas_obs := gs) /\ context_well_typed cx /\
   accounts_well_typed (es with gas_obs := gs).accounts /\
   functions_well_typed cx` by
    (qpat_assum `expr_sim_inv _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_results_mutual)) >> strip_tac >>
  Cases_on `res` >- simp[target_place_res_ok_def] >>
  drule eval_target_place_no_control >> strip_tac >>
  Cases_on `y` >> gvs[no_control_exc_def,target_place_res_ok_def,
    no_type_error_result_def] >>
  rename1 `eval_target_place _ _ _ = (INR (Error err),_)` >>
  Cases_on `err` >> gvs[target_place_res_ok_def,no_type_error_result_def]
QED
