(* An internal function's return statement, memory-safely, for the
   returns bodyMemIntCallReturnDirect leaves out: a widened internal call's
   value (lowered at a type other than its own), or a compound value
   widening into the caller's return buffer. *)
Theory bodyMemIntCallReturnWidened
Ancestors
  bodyMemoryDefs intCallReturnMem intCallReturnWidenMem
  internalReturnValueEndpointMem internalReturnBytestringMem
  internalReturnCompoundEndpointMem internalReturnCompositionMem
  internalReturnEndpointMetadataMem
  internalReturnEndpointFrameMem externalReturnNormalizedMem
  intCallReturnDirectBranchesMem stmtSimReturn compileEnv valueEncoding
  compileVyper loweringPosts exprLoweringProps stmtLowering

Theorem internal_return_widened_mem:
  !tops ctx func cx cenv ret_ty ret_tv rb rpc rsz cenv' env lctx eo es.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_imm_alloca = NONE /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME rb <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. rb = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap + 64 < dimword (:256) /\
       (cenv.ce_is_ctor ==>
        !nm io ity itv.
          FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
          evaluate_type (get_tenv cx) ity = SOME itv ==>
          regions_disjoint io (type_memory_size itv) (w2n bw) cap)) /\
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
            expr_sim_mem ctx func cenv' cx ty e es /\
            expr_vv_sim_mem ctx func cenv' cx ty e es) /\
    ~(!e. eo = SOME e ==>
              lowered_value_type cenv' e = expr_type e /\
              (expr_type e = ret_ty \/ is_word_type ret_ty \/
               is_bytestring_type ret_ty)) ==>
    stmt_frag_mem rb ctx func cx lctx
        (case rb of
           NONE => intret_q func cenv cx ret_tv
         | SOME (bw,cap) => intret_mem_q func cenv cx ret_tv bw)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
Proof
  rpt gen_tac >> strip_tac >>
  `cenv'.ce_returns_count = cenv.ce_returns_count /\
   cenv'.ce_return_pc = cenv.ce_return_pc` by
    (qpat_x_assum `same_frame _ _` mp_tac >>
     simp[bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  `?e bw cap. eo = SOME e /\ rb = SOME (bw,cap) /\
    cenv'.ce_returns_count = 0 /\ ~is_word_type ret_ty /\
    well_typed_expr env e /\ type_widens_to (get_tenv cx) (expr_type e) ret_ty` by
    (irule internal_return_widened_reachable >>
     metis_tac[]) >> gvs[] >>
  irule internal_return_memory_compose_mem >> simp[intret_mem_q_gas_obs] >>
  rpt gen_tac >> strip_tac >>
  `ret_pc_ok cenv' sm t /\
   return_buf_frame (SOME (bw,type_memory_size ret_tv)) cenv' sm t` by
    (irule internal_return_endpoint_frames_mem >> metis_tac[]) >>
  `cenv'.ce_imm_alloca = NONE` by
    (qpat_x_assum `same_frame _ _` mp_tac >>
     simp[bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[stmtLoweringTheory.compile_internal_return_from_env_def,
       comp_bind_def, comp_return_def] >> strip_tac >>
  `type_memory_bytes cenv' ret_ty = type_memory_size ret_tv` by
    (irule externalReturnCopyRecursiveTheory.return_copy_memory_size >>
     qexists_tac `get_tenv cx` >> fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  irule internal_return_endpoint_post_frame_mem >>
  first_assum (irule_at (Pat `same_frame _ _`)) >>
  Cases_on `is_bytestring_type ret_ty`
  >- (irule internal_return_bytestring_suffix_mem >>
      simp[] >> conj_tac
      >- (match_mp_tac (GEN_ALL internal_return_endpoint_constructor_separation) >>
          first_assum (irule_at (Pat `same_frame _ _`)) >>
          first_assum (irule_at (Pat `expr_sim_inv _ _ _ _`)) >>
          simp[] >> metis_tac[]) >>
      first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
      first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  suspend "compound"
QED

Resume internal_return_widened_mem[compound]:
  `post_value_type cenv' e = lowered_value_type cenv' e` by
    (irule compound_return_post_type >> metis_tac[]) >>
  drule_all return_value_physical_typed >> strip_tac >>
  Cases_on `lowered_value_type cenv' e = ret_ty`
  >- suspend "equal" >>
  irule internal_return_compound_suffix_mem >> simp[] >>
  conj_tac >- fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  conj_tac >- gvs[bodySimTheory.body_inv_def, bodySimTheory.same_frame_def,
                 compile_env_component_equality] >>
  conj_tac
  >- (match_mp_tac (GEN_ALL internal_return_endpoint_constructor_separation) >>
      first_assum (irule_at (Pat `same_frame _ _`)) >>
      first_assum (irule_at (Pat `expr_sim_inv _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  conj_tac >- fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `IS_SOME (type_stmt _ _ _)`)) >>
  first_assum (irule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  (* HELD: the remaining goal is source/return-buffer disjointness,
     regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap.  It does
     not follow from the current return_buf_frame_def, which doesn't separate
     the caller's buffer from the callee's allocations; held until
     return_buf_frame carries the caller-buffer frontier.  The closing steps
     once a disjointness lemma exists:
  irule <disjointness lemma> >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> fs[expr_post_def] >> metis_tac[]
  *)
  cheat
QED

Resume internal_return_widened_mem[equal]:
  `stv = ret_tv /\ post_value_type cenv' e = ret_ty` by fs[] >>
  `value_has_type ret_tv v` by metis_tac[] >>
  `expr_store_bound cx ret_ty v op t /\
   ?sw. eval_operand op t = SOME sw /\
     (type_memory_size ret_tv = 0 \/
      w2n sw + type_memory_size ret_tv <= t.vs_alloca_next)` by
    (qpat_x_assum `!stv. _` (qspec_then `ret_tv` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[] >> disch_tac >>
  irule internal_return_equal_endpoint_mem >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  first_assum (irule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >>
  match_mp_tac (GEN_ALL internal_return_endpoint_constructor_separation) >>
  first_assum (irule_at (Pat `same_frame _ _`)) >>
  first_assum (irule_at (Pat `expr_sim_inv _ _ _ _`)) >> simp[] >> metis_tac[]
QED

Finalise internal_return_widened_mem
