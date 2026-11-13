(* Memory cases of the body induction for an assignment or augmented
   assignment whose target is an immutable: a constructor's write to its
   immutables region (bodyMemAssignOther's and bodyMemAugAssignOther's
   splits).  S1's twins are stmtSimAssignPlace's immutable_deploy_assign_case
   and bodyAugAssignOther's immutable_deploy_augassign_case. *)
Theory bodyMemImmutableDeploy
Ancestors
  immutableAssignRhsOutcome immutableAssignValueOutcomeMem immutableAssignEmptyOutcome
  immutableAssignMemPost immutableAssignCode immutableAssignOpen exprSimHyps
  exprLoweringProps exprOperandVar stmtLoweringMono stmtSimProps
  supportedStmts stmtSimDefs compileEnv context vyperInterpreter vyperState exprSimHypsDefs
  immutableStoreOptionPathMem immutableFixedCopyPathMem immutableAssignEmpty bodyMemoryPreds targetPlaceSim bodyImmutableAssignFacts immutableAssignStoreMem immutableFixedCopyMem immutableFixedCopyTransportMem immutableLoopStoreMem immutableNormalizeMem immutableAssignAdmissibility immutableAssignWordMem immutableAssignFixedMem immutableAssignBytesMem immutableAssignNormalizedMem
  bodyAugPlaceTarget immutableAugAssignScalarAssembly
Libs monadsyntax

Theorem body_assign_immutable_deploy_mem:
  !cx t e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
                 body_base_target_mem_ok cx t) /\
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget t) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ ~is_abi_dynamic cenv.ce_struct_fields ty /\
        (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    immutable_root cx t ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all immutable_assignment_shape >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[bodyAssignPlaceTheory.body_assign_place_rhs_pre] >>
  `expr_vv_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  Cases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >>
  drule_all immutable_assignment_globals >> strip_tac >>
  drule_all immutable_assignment_layout >> strip_tac >> gvs[] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule immutable_assign_empty_stmt_mem >> metis_tac[]) >>
  suspend "ordinary"
QED

Resume body_assign_immutable_deploy_mem[ordinary]:
  markerLib.RESUME_TAC >> (
  `?dtv. evaluate_type (get_tenv cx) ity = SOME dtv` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
     qpat_x_assum `!src id ty. _ ==> IS_SOME _` (drule_then mp_tac) >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     PairCases_on `x` >> metis_tac[]) >>
  `off + type_memory_size dtv < dimword (:256)` by metis_tac[] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `compile_get_target_ptr compile_expr cenv
      (TopLevelNameTarget (cenv.ce_module,id)) =
    comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity))` by
    (simp[FUN_EQ_THM, comp_return_def] >> gen_tac >>
     irule immutable_assignment_target_lowering >> simp[]) >>
  drule_all immutable_assign_code_parts >> strip_tac >> gvs[] >>
  `~block_is_terminated sb` by metis_tac[immutable_assign_loccode_open] >>
  `supported_expr tops e /\ supported_program tops /\
   get_module_code cx NONE = SOME tops /\
   cenv.ce_func_return_type = build_func_return_type tops` by
    fs[supported_stmt_def, supported_assignment_def, bodySimTheory.body_inv_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  suspend "outcome")
QED

Resume body_assign_immutable_deploy_mem[outcome]:
  markerLib.RESUME_TAC >> (
  `ci_mono sa sm /\ ci_mono sm su /\ ci_mono su sb` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_unwrap_value,
      cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!x. op = Var x ==> not_fresh_at su x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> gvs[vv_operand_def]) >>
  `!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at su x` by metis_tac[local_ptrs_reserved_imm_base] >>
  simp[Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac `gas_outcome T _ _ _ _ Q R` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `env` |-> `env`, `tops` |-> `tops`,
    `ity` |-> `ity`, `dtv` |-> `dtv`, `off` |-> `off`, `vv` |-> `vv`,
    `sm` |-> `sm`, `su` |-> `su`, `op` |-> `op`,
    `src` |-> `cenv.ce_module`, `id` |-> `id`]
    (SPEC_ALL immutable_assign_rhs_outcome)) >>
  impl_tac
  >- (simp[] >> reverse conj_tac
      >- (rpt strip_tac >> simp[Abbr `R`, stmt_exit_def] >>
          metis_tac[expr_exit_INR_type]) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      suspend "suffix") >>
  simp[])
QED

Resume body_assign_immutable_deploy_mem[suffix]:
  markerLib.RESUME_TAC >> (
  qmatch_goalsub_abbrev_tac `Q (INL ()) fin _` >>
  `?mods old. ALOOKUP ee.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables cenv.ce_module mods) id = SOME (dtv,old)` by
    metis_tac[immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup] >>
  `write_place cx (ImmutablePlace cenv.ce_module id []) v ee = (INL (),fin)` by
    (drule_all bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source >>
     disch_then (qspec_then `v` assume_tac) >>
     simp[Abbr `fin`, vyperStateTheory.update_immutable_def]) >>
  qpat_x_assum `?gs pv. _` (qx_choosel_then [`gs`,`pv`] strip_assume_tac) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `(do pv <- eval_expr cx e; read_result cx pv od) (es with gas_obs := gs) =
    (INL v,ee)` by simp[bind_def] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `es` |-> `es with gas_obs := gs`,
    `ers` |-> `es`, `si` |-> `sa`, `s` |-> `u`, `itv` |-> `dtv`,
    `loc` |-> `vv_location vv`]
    (SPEC_ALL immutable_assign_value_mem_stmt_post)) >>
  impl_tac >- simp[] >> strip_tac >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  qexists_tac `q` >> simp[] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `t` |-> `q`]
    (SPEC_ALL immutable_assign_mem_entry_post)) >>
  impl_tac >- simp[] >> strip_tac >>
  simp[Abbr `Q`] >> qexists_tac `cenv` >> simp[])
QED

Finalise body_assign_immutable_deploy_mem

(* Constructor augmented assignment through the counted scalar assembly. *)
Theorem body_augassign_immutable_deploy_mem:
  !cx ty t bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty t bop e) /\
    body_stmt_safe tops (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    immutable_root cx t ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  rpt strip_tac >> Cases_on `t`
  >- gvs[]
  >- (irule immutable_augassign_scalar_assembly >> metis_tac[])
  >> metis_tac[aug_place_supported_stmt_target_info,
               aug_place_supported_root_not_immutable]
QED
