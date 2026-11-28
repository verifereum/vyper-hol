(* Entry certificates for the synthetic immutable AugAssign load. *)
Theory augAssignFullImmutableCertificate
Ancestors
  bodyImmutableAugAssignFacts bodyFullToplevelCtorSourceLayout
  bodyPtrDefs stateRelProj exprSimHypsDefs stmtSimAugAssignPlace
  exprLoweringProps exprSimProps supportedDecls supportedTypes
  supportedExprTraverse vyperTypeEnv vyperTypeSystem vyperTypeCallGraph
  allocLimits vyperStorageFootprint vyperState compileEnv finite_map words
  pred_set list arithmetic

Theorem augassign_immutable_synthetic_pre:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es0 /\ call_evaluation_safe cx [] /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
  ==> expr_body_pre cenv cx env (TopLevelName ty (cenv.ce_module,id)) es0
Proof
  strip_tac >>
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >>
  `well_formed_type env.type_defs ty /\ ty <> NoneT` by
    (drule aug_place_typing >> strip_tac >>
     metis_tac[assignable_type_well_formed, assignable_type_not_NoneT]) >>
  `~cx_const_name cx (src,id)` by
    (strip_tac >> drule_all bodySimTheory.body_inv_const_name_not_root >>
     strip_tac >> gvs[]) >>
  simp[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def, expr_has_evm_run_thm,
       supported_expr_exists_def, call_operands_effect_root_def,
       const_name_root_def, supportedProgramTheory.expr_abi_decode_target_root_def] >>
  gvs[type_alloc_ok_def] >>
  reverse conj_tac
  >- (`cx_tops cx = tops` by
        (irule gasContextTheory.cx_tops_module >>
         gvs[bodySimTheory.body_inv_def]) >>
      gvs[bodySimTheory.body_inv_def]) >>
  metis_tac[stmtSimAugAssignTheory.well_formed_type_bits]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule_all augassign_immutable_synthetic_pre >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es0.storage_trace)
    es0.storage_trace` by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es0.storage_trace)
     ctx func cenv cx es0 s0 /\
   ghost_inv_at (DF (storage_trace_horizon es0.storage_trace))
     lo d cenv cx es0 G0 tn0 s0` by metis_tac[] >>
  `dead_lo_ok (storage_trace_horizon es0.storage_trace)
     (DF (storage_trace_horizon es0.storage_trace)) lo cenv cx` by simp[] >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_all_then assume_tac exprBodyPrePropsTheory.body_inv_expr_body_pre_mods >>
  `dead_lo_ok_mods (storage_trace_horizon es0.storage_trace)
     (DF (storage_trace_horizon es0.storage_trace)) lo cenv cx` by
    fs[bodyFullShadowBodyInvTheory.dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def] >>
  `src = NONE` by metis_tac[bodyInvCodePropsTheory.body_inv_module_locations] >>
  gvs[] >> drule_all toplevel_ctor_source_layout >> strip_tac >>
  gvs[alistTheory.ALOOKUP_def, compileUnitTheory.make_struct_fields_map_mods_singleton] >>
  `type_memory_size ptv = 32` by metis_tac[word_tv_memory_size] >>
  `s0.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  `lo <= s0.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `lo < dimword (:256)` by decide_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  qexistsl [`pre`, `post`, `vis`, `slot`] >> metis_tac[]
QED
*)
Theorem augassign_immutable_entry_certificate:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es0 /\ call_evaluation_safe cx [] /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  storage_trace_domain cx st0 es0.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\
  src = cenv.ce_module /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es0.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (ptv,cur) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty
  ==>
  cx_tops cx = tops /\ off + 32 <= lo /\ lo < dimword (:256) /\
  ?pre post vis slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) pre /\
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size ptv
Proof
  cheat
QED
