(* Source layout and entry facts for homogeneous MakeArray. *)
Theory bodyMakeArraySourceMods
Ancestors
  bodyMakeElementsContractMods exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs
  exprSimAggregateLayout exprSimAggregateLoops exprSimAggregateSource exprSimSource
  typedMemoryCopy vyperTypeInvariants vyperTypeEvalCaseProofs vyperTypeSystem
  allocLimits allocLimitsProps gasShadowCompileBase exprLoweringProps fragExec
  supportedExprTraverse supportedProgram vyperTypeCallGraph vyperTypeCallStackSoundness
  gasContext exprSimDefs list rich_list words

Theorem make_array_source_layout_mods:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  ?tv. ann = ArrayT et n /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n) /\
    EVERY (\e. arg_type_fits (expr_type e) et) args /\
    compatible_bound n (LENGTH args) /\ 0 < type_slot_size tv /\
    type_memory_bytes ce et = type_memory_size tv /\
    type_memory_bytes ce (ArrayT et n) = type_memory_size (ArrayTV tv n) /\
    (if (case n of Dynamic _ => T | _ => F) then 32 else 0) +
      LENGTH args * type_memory_size tv <= type_memory_bytes ce (ArrayT et n) /\
    type_memory_bytes ce (ArrayT et n) < dimword (:256)
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP env_consistent_type_defs_get_tenv) >>
  fs[Once well_typed_expr_def, well_typed_builtin_app_def, EVERY_MAP] >>
  gvs[] >>
  `?tv. evaluate_type (get_tenv cx) et = SOME tv /\ 0 < type_slot_size tv /\
    0 < bound_length n /\ type_slot_size (ArrayTV tv n) < dimword (:256)` by
    (qpat_x_assum `well_formed_type _ (ArrayT _ _)` mp_tac >>
     rewrite_tac[well_formed_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) et` >>
     simp[Once vyperValueTheory.evaluate_type_def]) >>
  rename1 `evaluate_type (get_tenv cx) et = SOME tv` >>
  `!ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
     type_memory_bytes ce ty = type_memory_size rt` by
    (rpt strip_tac >> irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n)` by
    simp[Once vyperValueTheory.evaluate_type_def] >>
  `type_memory_bytes ce (ArrayT et n) < dimword (:256)` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, alloc_limits_expr_def, wordsTheory.dimword_def] >>
     decide_tac) >>
  qpat_assum `!ty rt. _ ==> type_memory_bytes _ ty = _`
    (qspec_then `ArrayT et n` (drule_then assume_tac)) >>
  simp[] >> Cases_on `n` >>
  gvs[vyperValueTheory.compatible_bound_def, valueEncodingTheory.type_memory_size_def] >>
  simp[arithmeticTheory.LE_MULT_RCANCEL]
QED

Theorem make_array_source_action_mods:
  compatible_bound n (LENGTH args) /\ evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) st =
    ((case FST (eval_exprs cx args st) of
        INL vs => INL (Value (ArrayV (make_array_value tv n vs)))
      | INR ex => INR ex), SND (eval_exprs cx args st))
Proof
  strip_tac >> Cases_on `eval_exprs cx args st` >> simp[] >>
  irule aggregate_eval_make_array >> simp[]
QED

Theorem make_array_child_pre[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
  expr_body_pre_mods mods ce cx env e ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  rw[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, EXISTS_MEM] >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
            int_calls_exprs_every_mem]
QED

Theorem make_array_source_entry_mods:
  expr_body_pre_mods mods ce cx env (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) es /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
   body_exprs_full_ok_mods mods exps cx args) ==>
  body_exprs_full_ok_mods mods exps cx args /\
  (!e ee. MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
     expr_body_pre_mods mods ce cx env e ee) /\
  (gas_admissible (eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args))
     expr_vv_res_ok es ==> make_elements_admissible_mods cx args es)
Proof
  strip_tac >> drule_then strip_assume_tac make_array_source_layout_mods >>
  conj_tac >- fs[vyperContextTheory.builtin_args_length_ok_def] >>
  conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC make_array_child_pre) >>
  rewrite_tac[make_elements_admissible_mods_def, gas_admissible_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[] >>
  rename1 `eval_exprs cx args (es with gas_obs := gs) = (INR ex,st)` >>
  `eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)
      (es with gas_obs := gs) = (INR ex,st)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` kall_tac >>
     drule_all make_array_source_action_mods >> disch_then (fn th => simp[th])) >>
  qpat_x_assum `!gs res ee. _ ==> expr_vv_res_ok res` drule >>
  simp[expr_vv_res_ok_def, expr_res_ok_def]
QED
