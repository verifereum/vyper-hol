(*
 * Pop on a member of a constructor immutable: helpers for
 * exprSimPopNestedImmutableDeploy's pop_nested_immutable_deploy_sim.
 *
 *   body_target_idx_case  — the indices' judgments of a target from
 *                           body_base_target_ok, for pop_nested_sim's
 *                           body-level consumer.
 *   body_imm_var_type     — in a body whose compile env is the main
 *                           module's, an assignable immutable has its
 *                           declared type in ce_module_var_type.
 *   imm_place_at,
 *   imm_target_post       — where a target rooted at an initialized
 *                           immutable points: k bytes into the
 *                           immutable's capacity region at its
 *                           ImmutableLoc, k the path's mem_path_offset
 *                           (targetPlaceSim's place_ptr_rel has no
 *                           immutable case).
 *   imm_target_walk       — the counted walk of such a target with pure
 *                           indices, as target_sim has it for the other
 *                           roots, for pop_nested_immutable_deploy_pure_sim.
 *                           Admitted pending alan; provable as stated, no
 *                           invariant change needed.
 *   pop_nested_immutable_deploy_impure_index_case — RESIDUAL, FALSE as
 *                           stated: such a pop with an index that pops or
 *                           calls.
 *)

Theory exprSimPopImmutableTarget
Ancestors
  exprSimPopNestedLocalMemory vyperTargetPlaceWrite
  compileVyper vyperTypeInvariants vyperTypeContract vyperPureExpr
  abiEncoderMemory immutableValue immutableEncoding immutableEncodingProofs
  exprSimTopLevelImmutable gasSummary fragGasPath fragGasMode
  exprSimArrayIndex immutableCopyExecution varsExt freshWrites fragGasSeq fragGasSeqAbort
  exprOperandVar exprSimWordArgs exprBopSimProps
  bodySim targetPlaceSim targetPlaceSimCasesBase targetPlaceSimCases
  targetPlaceSimDefs
  exprSimHypsDefs exprSimDefs loweringPosts gasOutcome gasContext
  exprLowering exprLoweringProps compileEnv vyperAST vyperState
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph venomState
Libs wordsLib intLib

(* In a body, the indices' judgments of a target, internal calls allowed:
   body_base_target_ok gives body_expr_ok for each index whose base place
   evaluates, and body_inv turns it into the index's cases. *)
Theorem body_target_idx_case:
  !bt cx tops ctx func cenv.
    body_inv tops ctx cenv cx /\ body_base_target_ok cx bt ==>
    target_idx_case F ctx func cenv cx bt
Proof
  recInduct base_assignment_target_induct >>
  rw[target_idx_case_def, body_base_target_ok_def] >>
  gvs[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[]
QED

Theorem is_immutable_decl_mem[local]:
  !tops id. is_immutable_decl id tops ==>
    ?vis ty init. MEM (VariableDecl vis Immutable id ty init) tops
Proof
  Induct_on `tops` >> rw[is_immutable_decl_def] >>
  Cases_on `h` >> gvs[is_immutable_decl_def] >>
  Cases_on `v0` >> gvs[is_immutable_decl_def] >>
  metis_tac[]
QED

Theorem build_var_type_map_mem[local]:
  !tops vis mut id ty init.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel NONE) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_var_type_map tops (NONE,id) = SOME ty
Proof
  Induct >> simp[] >> Cases >>
  simp[build_var_type_map_def, toplevel_vtype_keys_toplevel_def] >>
  rw[] >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
  res_tac >> gvs[toplevel_vtype_keys_toplevel_def] >>
  qpat_x_assum `!y. ~MEM y tops \/ _`
    (qspec_then `VariableDecl vis mut id ty init` mp_tac) >>
  gvs[toplevel_vtype_keys_toplevel_def]
QED

(* In a body whose compile env is the main module's, an assignable
   immutable has its declared type in ce_module_var_type: expr_sim_inv
   puts it in the compile env's module, its declaration is in tops, and
   body_inv has tops's declared types there, keyed apart. *)
Theorem body_imm_var_type:
  !tops ctx cenv cx env es src id ty0.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    cenv.ce_module = NONE /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
    cenv.ce_module_var_type (src,id) = SOME ty0
Proof
  rpt strip_tac >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  `?ts. get_module_code cx src = SOME ts /\
        FLOOKUP env.bare_globals (src,id) = SOME ty0 /\
        is_immutable_decl id ts` by
    (fs[env_context_consistent_def] >> metis_tac[]) >>
  `src = NONE` by (fs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[] >>
  `ts = tops` by fs[body_inv_def] >> gvs[] >>
  drule is_immutable_decl_mem >> strip_tac >>
  `cx.in_deploy` by
    (CCONTR_TAC >>
     gvs[env_context_consistent_def, bare_global_assignable_complete_def]) >>
  `bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[env_context_consistent_def] >>
  `FLOOKUP env.bare_global_assignable (NONE,id) = SOME ty` by
    (gvs[bare_global_assignable_complete_def] >> res_tac >> gvs[]) >>
  gvs[body_inv_def] >> drule_all build_var_type_map_mem >> simp[]
QED

(* The place pv is at w, of type ty: an immutable of the module being
   lowered, initialized at es, with the place's path inside it at offset k
   of its evaluated type, readable at es, and w the immutable's offset
   plus k.  The immutable's bytes end below 2 ** 256. *)
Definition imm_place_at_def:
  (imm_place_at cenv cx (es:evaluation_state)
     (PlaceR (ImmutablePlace src id path)) (w:bytes32)
     ty <=>
     ?off itv iv k tv v.
       src = cenv.ce_module /\
       FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
       off + type_memory_size itv < dimword (:256) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) id =
         SOME (itv,iv) /\
       mem_path_offset itv path = SOME (k,tv) /\
       evaluate_subscripts itv iv path = INL v /\
       evaluate_type (get_tenv cx) ty = SOME tv /\
       w = n2w (off + k)) /\
  (imm_place_at cenv cx (es:evaluation_state) pv w ty <=> F)
End

(* target_post with imm_place_at for place_ptr_rel: the pointer r's
   operand is at the place, its location code, its place type ty's; and
   target_post's frame. *)
Definition imm_target_post_def:
  imm_target_post ctx func cenv cx es sa sb s0 es' pv ty
    (r : operand # data_location option # place_ty option) s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (FST r) s = SOME w /\ imm_place_at cenv cx es' pv w ty) /\
    FST (SND r) = SOME LocCode /\
    SND (SND r) = SOME (ValPT ty) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Theorem imm_place_at_gas_obs[local,simp]:
  !cenv cx es pv w ty gs.
    imm_place_at cenv cx (es with gas_obs := gs) pv w ty <=>
    imm_place_at cenv cx es pv w ty
Proof
  simp[oneline imm_place_at_def]
QED

Theorem imm_place_at_pure_index[local]:
  !cenv cx es pv w ty e gs res ee.
    pure_expr e /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (res,ee) /\
    imm_place_at cenv cx es pv w ty ==>
    ee with gas_obs := [] = es with gas_obs := [] /\
    imm_place_at cenv cx ee pv w ty
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
  drule read_result_state >> strip_tac >> gvs[]
QED

Theorem imm_target_post_frame[local]:
  !ctx func cenv cx es sa sb s0 ee pv ty r s.
    imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r s <=>
    stmt_state_rel ctx func cenv cx ee s /\
    (?w. eval_operand (FST r) s = SOME w /\ imm_place_at cenv cx ee pv w ty) /\
    FST (SND r) = SOME LocCode /\ SND (SND r) = SOME (ValPT ty) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    wb_frame cenv es sa s0 s
Proof
  simp[imm_target_post_def, wb_frame_def]
QED

Theorem imm_target_post_trans[local]:
  !ctx func cenv cx es sa sm sb s0 em s1 ee s2 pv ty r pv0 ty0 r0.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM em.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    imm_target_post ctx func cenv cx es sa sm s0 em pv0 ty0 r0 s1 /\
    imm_target_post ctx func cenv cx em sm sb s1 ee pv ty r s2 ==>
    imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r s2
Proof
  simp[imm_target_post_frame] >> rpt strip_tac >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`em`, `sm`, `s1`] >> simp[]) >>
  goal_assum $ drule_at Any
QED

Theorem imm_place_at_index_post[local]:
  !ctx func cenv cx es e gs res ee pv w ty p sa sb s0 v op s.
    pure_expr e /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (res,ee) /\
    imm_place_at cenv cx es pv w ty /\ eval_operand p s0 = SOME w /\
    (!x. p = Var x ==> not_fresh_at sa x) /\ (!l. p <> Label l) /\
    expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s ==>
    imm_place_at cenv cx (ee with gas_obs := []) pv w ty /\
    eval_operand p s = SOME w
Proof
  rpt gen_tac >> strip_tac >>
  drule_all imm_place_at_pure_index >> strip_tac >> simp[] >>
  irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s0`] >>
  fs[expr_post_def]
QED

Theorem imm_target_root_assignable[local]:
  !env cx es cenv src id ty.
    expr_sim_inv cenv cx env es /\
    type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty
Proof
  rpt strip_tac >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,id)`
  >- (gvs[well_typed_expr_def] >>
      Cases_on `FLOOKUP env.bare_globals (src,id)` >>
      gvs[] >> fs[env_context_consistent_def] >>
      qpat_x_assum `!src' id' ty. _ /\ _ ==> _`
        (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
      simp[] >> strip_tac >> res_tac >> gvs[]) >>
  gvs[well_typed_expr_def]
QED

Theorem imm_target_root_layout[local]:
  !env cx es cenv src id ty.
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
    ?ts off tv iv.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = NONE /\
      src = cenv.ce_module /\
      FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      off + type_memory_size tv < dimword (:256) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                 NONE => FEMPTY
               | SOME imms => get_source_immutables src imms) id = SOME (tv,iv) /\
      evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rpt strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = _ ==> _`
       drule >> simp[] >> strip_tac >> simp[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_bare_global_ready_src >>
  strip_tac >>
  fs[env_consistent_def, env_immutables_consistent_def] >>
  `find_var_decl_by_name id ts = NONE` by
    (drule_all env_context_consistent_bare_global_find_NONE >>
     strip_tac >> gvs[]) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  qpat_x_assum `!src id ty. _ ==> IS_SOME _` drule >>
  Cases_on `FLOOKUP (case ALOOKUP x src of
                       NONE => FEMPTY | SOME imm => imm) id` >> simp[] >>
  rename1 `_ = SOME tvv` >> PairCases_on `tvv` >>
  `evaluate_type (get_tenv cx) ty = SOME tvv0` by metis_tac[] >>
  fs[expr_sim_inv_def] >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_globals _ = _ ==> _`
    drule >> strip_tac >>
  qexists_tac `off` >> simp[]
QED

Theorem imm_target_root_walk[local]:
  !nocalls ctx func cenv cx env es ty src id sa sb r s0.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    target_idx_case nocalls ctx func cenv cx (TopLevelNameTarget (src,id)) /\
    (nocalls ==> int_calls_target (TopLevelNameTarget (src,id)) = []) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_sim_inv cenv cx env es /\
    target_indices_pre cenv cx env (TopLevelNameTarget (src,id)) /\
    EVERY pure_expr (target_indices (TopLevelNameTarget (src,id))) /\
    type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv (TopLevelNameTarget (src,id)) sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx (TopLevelNameTarget (src,id))) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_base_place cx (TopLevelNameTarget (src,id))) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
         imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  drule_all imm_target_root_assignable >> strip_tac >>
  drule_all imm_target_root_layout >> strip_tac >>
  `cenv.ce_module_var_type (src,id) = SOME ty` by metis_tac[] >>
  gvs[compile_get_target_ptr_def, comp_return_def] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`, `es`, `OK s0`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
           evaluate_def, lookup_global_def, bind_def,
           lift_option_type_def, return_def, get_immutables_def,
           get_address_immutables_def] >>
      Cases_on `ALOOKUP es.immutables cx.txn.target` >>
      gvs[get_source_immutables_def, return_def, raise_def]) >>
  disj1_tac >> simp[] >>
  simp[imm_target_post_def, imm_place_at_def, eval_operand_def,
       exprSimPropsTheory.locals_kept_mem, mem_path_offset_def, evaluate_subscripts_def]
QED

Theorem imm_place_at_value_type[local]:
  !cenv cx env es src id path itv iv k tv v.
    expr_sim_inv cenv cx env es /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
      SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,tv) /\
    evaluate_subscripts itv iv path = INL v ==>
    value_has_type tv v /\ well_formed_type_value tv
Proof
  rpt strip_tac >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  drule_all vyperTypeEnvTheory.state_well_typed_immutables_ALOOKUP >>
  strip_tac >>
  drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >>
  strip_tac >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_type,
            vyperPlaceStatePreservationTheory.subscripts_type_well_formed]
QED


Theorem imm_typed_step_memory[local]:
  !tv v sub d ptv pv b mem.
    value_has_type tv v /\ well_formed_type_value tv /\
    mem_path_offset tv [sub] = SOME (d,ptv) /\
    evaluate_subscripts tv v [sub] = INL pv /\
    val_in_memory tv v b mem ==>
    val_in_memory ptv pv (b+d) mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sub`
  >- ((rename1 `ValueSubscript idx` >> Cases_on `idx` >>
       Cases_on `tv` >>
       gvs[mem_path_offset_def, mem_step_offset_def, AllCaseEqs()] >>
       Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
       rename1 `ArrayV av` >> Cases_on `av` >>
       gvs[vyperTypingTheory.value_has_type_def, evaluate_subscripts_def,
           vyperValueOperationTheory.array_index_def, AllCaseEqs()])
      >- (gvs[valueEncodingPropsTheory.val_in_memory_tuple] >>
          `LENGTH l' = LENGTH l` by
            metis_tac[vyperTypingTheory.values_have_types_length] >>
          `!xs. type_memory_size_list xs = SUM (MAP type_memory_size xs)` by
            (Induct >> simp[valueEncodingTheory.type_memory_size_def]) >>
          gvs[listTheory.oEL_EQ_EL] >>
          irule tupleMemoryLayoutTheory.tuple_in_memory_element >> simp[])
      >- (Cases_on `b'` >>
           gvs[vyperTypingTheory.value_has_type_def, mem_step_offset_def,
               valueEncodingPropsTheory.val_in_memory_dynarray,
               listTheory.oEL_EQ_EL] >>
           drule exprSimAggregateEncodingTheory.elems_in_memory_EL >>
           disch_then (qspec_then `Num i` mp_tac) >>
           simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])
       >- (gvs[mem_step_offset_def,
               valueEncodingPropsTheory.val_in_memory_sarray]) >>
      gvs[mem_step_offset_def, valueEncodingPropsTheory.val_in_memory_sarray] >>
      metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup]) >>
  Cases_on `tv` >>
  gvs[mem_path_offset_def, mem_step_offset_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, evaluate_subscripts_def,
      valueEncodingPropsTheory.val_in_memory_struct, AllCaseEqs()] >>
  qpat_x_assum `well_formed_type_value _` kall_tac >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac [`b`, `pv`, `ptv`, `d`, `s`, `l'`, `l`] >>
  Induct >> Cases_on `l'` >>
  simp[vyperTypingTheory.value_has_type_def, mem_field_offset_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[vyperTypingTheory.value_has_type_def, mem_field_offset_def,
       valueEncodingTheory.val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h0 = s` >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem imm_typed_path_memory[local]:
  !path tv v k ptv pv b mem.
    value_has_type tv v /\ well_formed_type_value tv /\
    mem_path_offset tv path = SOME (k,ptv) /\
    evaluate_subscripts tv v path = INL pv /\
    val_in_memory tv v b mem ==>
    val_in_memory ptv pv (b+k) mem
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), pairTheory.EXISTS_PROD] >>
  `mem_path_offset tv [h] = SOME (p_1,p_2)` by
    simp[mem_path_offset_def] >>
  drule exprSimPropsTheory.mem_path_offset_sound >>
  simp[vyperStateTheory.subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule vyperPlaceStatePreservationTheory.evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `v`] mp_tac) >>
  gvs[AllCaseEqs()] >> strip_tac >>
  `val_in_memory p_2 v' (b + p_1) mem` by
    (irule imm_typed_step_memory >> goal_assum (drule_at Any) >> simp[]) >>
  `value_has_type p_2 v' /\ well_formed_type_value p_2` by
    (metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_type,
       vyperPlaceStatePreservationTheory.subscripts_type_well_formed,
       exprSimPropsTheory.mem_path_offset_sound]) >>
  first_x_assum drule_all >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem imm_readable_path_memory[local]:
  !ctx func cenv cx env es s src id itv iv off path k tv v.
    cenv.ce_is_ctor /\ src = cenv.ce_module /\
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
       SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,tv) /\
    evaluate_subscripts itv iv path = INL v ==>
    val_in_memory tv v (off+k) s.vs_memory
Proof
  rpt strip_tac >>
  `val_in_memory itv iv off s.vs_memory` by
    (gvs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
     first_x_assum drule_all >> simp[]) >>
  `value_has_type itv iv /\ well_formed_type_value itv` by
    (irule imm_place_at_value_type >> goal_assum (drule_at Any) >>
     qexistsl [`cenv`, `env`, `0`, `[]`] >>
     simp[mem_path_offset_def, evaluate_subscripts_def]) >>
  irule imm_typed_path_memory >> goal_assum (drule_at Any) >>
  qexistsl [`path`, `iv`] >> simp[]
QED

Theorem imm_readable_dynarray_length[local]:
  !ctx func cenv cx env es s src id itv iv off path k etv n vs.
    cenv.ce_is_ctor /\ src = cenv.ce_module /\
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
       SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts itv iv path = INL (ArrayV (DynArrayV vs)) ==>
    mem_word_at (off+k) s.vs_memory = n2w (LENGTH vs)
Proof
  rpt strip_tac >>
  `val_in_memory (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))
     (off+k) s.vs_memory` by
    (irule imm_readable_path_memory >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexistsl [`ctx`, `env`, `func`] >> simp[]) >>
  fs[valueEncodingPropsTheory.val_in_memory_dynarray]
QED

Theorem imm_iload_step_frame[local]:
  !inst s t.
    inst.inst_opcode = ILOAD /\ step_inst_base inst s = OK t ==>
    t = s with vs_vars := t.vs_vars /\
    (!x. ~MEM x inst.inst_outputs ==>
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt strip_tac >>
  gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomExecSemanticsTheory.exec_read1_def, AllCaseEqs()] >>
  simp[venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem imm_readonly_opcode[local]:
  !opc. fresh_write_op opc \/ opc = ILOAD ==>
    ~is_terminator opc /\ opc <> INVOKE /\ ~is_ext_call_op opc /\ opc <> GAS
Proof
  simp[fresh_write_op_def] >> rpt strip_tac >>
  gvs[venomInstTheory.is_terminator_def, venomInstTheory.is_ext_call_op_def]
QED

Theorem imm_readonly_seq_frame[local]:
  !code sa s t.
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) code /\
    run_inst_seq code s = OK t ==>
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt gen_tac >> strip_tac >>
  irule emitHelperPropsTheory.run_inst_seq_protected_frame >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  fs[listTheory.EVERY_MEM] >>
  `fresh_write_op i.inst_opcode \/ i.inst_opcode = ILOAD` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> ~MEM x i.inst_outputs` by metis_tac[] >>
  metis_tac[freshWritesTheory.step_fresh_write_op, imm_iload_step_frame]
QED

Theorem imm_ctor_load_code[local]:
  !region off sa p sb.
    compile_imm_load_word T (SOME region) off sa = (p,sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule contextTheory.compile_imm_load_word_ctor_result >> strip_tac >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, venomInstTheory.mk_inst_def,
       freshWritesTheory.fresh_write_op_def, not_fresh_at_def] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_imm_load_word_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, same_blocks_def] >> strip_tac >> gvs[]
QED

Theorem imm_emit_iload_correct[local]:
  emit_op ILOAD [op1] st = (v,st') /\
  eval_operand op1 ss = SOME a /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME (mload (w2n a) ss) /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory /\ ss'.vs_accounts = ss.vs_accounts /\
    ss'.vs_labels = ss.vs_labels
Proof
  rpt strip_tac >>
  irule (BETA_RULE (Q.SPECL [`ILOAD`, `\a ss. mload (w2n a) ss`]
    emitHelperPropsTheory.emit_op_read1_correct)) >>
  simp[] >> qexists_tac `op1` >> simp[] >>
  simp[venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_read1_def]
QED

Theorem imm_array_len_ctor_none[local]:
  !cnt base_op s b.
    eval_operand base_op s = SOME b ==>
    array_len_ok T cnt (compile_ptr_load T NONE LocCode)
      base_op s (mload (w2n b) s)
Proof
  rpt strip_tac >>
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def,
     contextTheory.compile_imm_load_word_def] >>
  drule emit_op_extends >> strip_tac >> simp[] >>
  drule_all imm_emit_iload_correct >> strip_tac >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem imm_ctor_load_none_code[local]:
  !off sa p sb.
    compile_imm_load_word T NONE off sa = (p,sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  simp[contextTheory.compile_imm_load_word_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, same_blocks_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, venomInstTheory.mk_inst_def,
       freshWritesTheory.fresh_write_op_def, not_fresh_at_def]
QED

Theorem imm_array_ctor_none_code[local]:
  !base_op idx dyn cnt ws esz sgn sa p sb.
    compile_array_subscript base_op idx dyn cnt ws esz sgn
      (compile_ptr_load T NONE LocCode) sa = (p,sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  mp_tac straight_fresh_array_check_ptr >>
  simp[freshWritesTheory.straight_fresh_def] >> disch_then drule >> strip_tac >>
  reverse (Cases_on `dyn`) >>
  gvs[comp_return_def, contextTheory.compile_ptr_load_def]
  >- (fs[same_blocks_def, freshWritesTheory.writes_fresh_def, listTheory.EVERY_MEM] >>
      metis_tac[]) >>
  drule imm_ctor_load_none_code >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[same_blocks_def, listTheory.EVERY_APPEND] >>
  fs[freshWritesTheory.writes_fresh_def, listTheory.EVERY_MEM, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem imm_array_ctor_code[local]:
  !base idx dyn cnt ws esz sgn region sa p sb.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T (SOME region) LocCode) sa = (p,sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  mp_tac straight_fresh_array_check_ptr >>
  simp[freshWritesTheory.straight_fresh_def] >> disch_then drule >> strip_tac >>
  reverse (Cases_on `dyn`) >>
  gvs[comp_return_def, contextTheory.compile_ptr_load_def]
  >- (fs[same_blocks_def, freshWritesTheory.writes_fresh_def, listTheory.EVERY_MEM] >>
      metis_tac[]) >>
  drule imm_ctor_load_code >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[same_blocks_def, listTheory.EVERY_APPEND] >>
  fs[freshWritesTheory.writes_fresh_def, listTheory.EVERY_MEM, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem imm_array_len_ctor[local]:
  !cnt region base_op s b.
    eval_operand base_op s = SOME b /\
    eval_operand region s = SOME 0w ==>
    array_len_ok T cnt (compile_ptr_load T (SOME region) LocCode)
      base_op s (mload (w2n b) s)
Proof
  rpt strip_tac >> rw[array_len_ok_def, contextTheory.compile_ptr_load_def] >>
  drule_all immutable_ctor_load_frame >>
  simp[immutable_operand_frame_def] >> metis_tac[]
QED

Theorem imm_array_ctor_run[local]:
  !base idx dyn cnt ws esz sgn region sa p sb s b i len.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T (SOME region) LocCode) sa = (p,sb) /\
    eval_operand base s = SOME b /\ eval_operand idx s = SOME i /\
    eval_operand region s = SOME 0w /\
    (!x. base = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!x. region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) ==>
    if idx_in_range sgn i len then
      ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >> rename1 `eval_operand bop s = SOME b` >>
  `eval_operand bop (drop_fresh sa s) = SOME b /\
   eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand region (drop_fresh sa s) = SOME 0w` by
    simp[eval_operand_drop_fresh] >>
  `array_len_ok dyn cnt (compile_ptr_load T (SOME region) LocCode)
      bop (drop_fresh sa s) len` by
    (reverse (Cases_on `dyn`) >> gvs[]
     >- simp[array_len_ok_static] >>
     `mload (w2n b) (drop_fresh sa s) = mload (w2n b) s` by
       simp[drop_fresh_def, venomStateTheory.mload_def] >>
     pop_assum (SUBST1_TAC o SYM) >> irule imm_array_len_ctor >> simp[]) >>
  drule imm_array_ctor_code >> strip_tac >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    ~is_ext_call_op inst.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[imm_readonly_opcode]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
      (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  qspecl_then [`sa`, `s`] assume_tac fresh_vars_wrt_drop_fresh >>
  Cases_on `idx_in_range sgn i len` >> simp[]
  >- (drule_all compile_array_subscript_ok >> strip_tac >>
      gvs[vars_ext_result_def, CaseEq "exec_result"] >>
      conj_tac
      >- (rename1 `vars_ext clean actual` >> fs[vars_ext_def] >>
          qpat_x_assum `actual = _` (fn th => once_rewrite_tac[th]) >>
          simp[eval_operand_vars_ext]) >>
      qpat_assum `run_inst_seq _ s = OK _`
        (mp_then Any mp_tac imm_readonly_seq_frame) >>
      disch_then (qspec_then `sa` mp_tac) >> simp[]) >>
  drule_all compile_array_subscript_oob >> strip_tac >>
  gvs[vars_ext_result_def, CaseEq "exec_result"] >> metis_tac[]
QED

Theorem imm_array_ctor_path[local]:
  !base idx dyn cnt ws esz sgn region sa p sb s b i len ctx func.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T (SOME region) LocCode) sa = (p,sb) /\
    eval_operand base s = SOME b /\ eval_operand idx s = SOME i /\
    eval_operand region s = SOME 0w /\
    (!x. base = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!x. region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    if idx_in_range sgn i len then
      ?t. gas_marked_path F ctx func s 0
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t j. gas_marked_path F ctx func s 0
          (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >>
  drule imm_array_ctor_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `EVERY (\ins. ins.inst_opcode <> GAS /\ ins.inst_opcode <> INVOKE /\
       ~is_terminator ins.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[imm_readonly_opcode]) >>
  drule_all imm_array_ctor_run >>
  Cases_on `idx_in_range sgn i len` >> simp[] >> strip_tac
  >- (qexists_tac `t` >> simp[] >>
      `LENGTH (FILTER (\ins. ins.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
        (simp[listTheory.LENGTH_EQ_NUM_compute, listTheory.FILTER_EQ_NIL,
              listTheory.EVERY_MEM] >> rpt strip_tac >>
         qpat_x_assum `EVERY (\ins. ins.inst_opcode <> GAS /\ _) _`
           (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
         disch_then drule >> simp[]) >>
      drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      simp[gas_marked_path_def] >> disch_then irule >>
      conj_tac >- (fs[listTheory.EVERY_MEM]) >>
      qexists_tac `bb` >> gvs[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
  simp[] >> metis_tac[]
QED

Theorem imm_array_ctor_counted[local]:
  !base idx dyn cnt ws esz sgn region sa p sb s b i len ctx func cenv cx es.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T (SOME region) LocCode) sa = (p,sb) /\
    eval_operand base s = SOME b /\ eval_operand idx s = SOME i /\
    eval_operand region s = SOME 0w /\
    (!x. base = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!x. region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    (!x. p = Var x ==> not_fresh_at sb x) /\
    if idx_in_range sgn i len then
      ?t. gas_marked_path F ctx func s 0 (OK t) /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        stmt_state_rel ctx func cenv cx es t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
          lookup_var x t = SOME w) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        locals_kept cenv es s t
    else ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule (cj 3 compiler_subscript_ops_var) >> simp[]) >>
  drule_all imm_array_ctor_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  Cases_on `idx_in_range sgn i len` >> simp[] >> strip_tac
  >- (`!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w` by simp[lookup_var_def] >>
      `stmt_state_rel ctx func cenv cx es t` by
        (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
         irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
         conj_tac >> rpt strip_tac >>
         qmatch_goalsub_rename_tac `lookup_var zz` >>
         `not_fresh_at sa zz` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         simp[lookup_var_def]) >>
      qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
      simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
           eval_operand_def, lookup_var_def] >>
      drule imm_array_ctor_code >> strip_tac >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      fs[same_blocks_def, exprSimPropsTheory.locals_kept_mem]) >>
  goal_assum $ drule_at Any
QED

Theorem imm_array_ctor_none_run[local]:
  !base_op idx dyn cnt ws esz sgn sa p sb s b i len.
    compile_array_subscript base_op idx dyn cnt ws esz sgn
      (compile_ptr_load T NONE LocCode) sa = (p,sb) /\
    eval_operand base_op s = SOME b /\ eval_operand idx s = SOME i /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) ==>
    if idx_in_range sgn i len then
      ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx (drop_fresh sa s) = SOME i` by
    simp[eval_operand_drop_fresh] >>
  `array_len_ok dyn cnt (compile_ptr_load T NONE LocCode)
      base_op (drop_fresh sa s) len` by
    (reverse (Cases_on `dyn`) >> gvs[]
     >- simp[array_len_ok_static] >>
     `mload (w2n b) (drop_fresh sa s) = mload (w2n b) s` by
       simp[drop_fresh_def, venomStateTheory.mload_def] >>
     pop_assum (SUBST1_TAC o SYM) >> irule imm_array_len_ctor_none >> simp[]) >>
  drule imm_array_ctor_none_code >> strip_tac >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    ~is_ext_call_op inst.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[imm_readonly_opcode]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
      (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  qspecl_then [`sa`, `s`] assume_tac fresh_vars_wrt_drop_fresh >>
  Cases_on `idx_in_range sgn i len` >> simp[]
  >- (drule_all compile_array_subscript_ok >> strip_tac >>
      gvs[vars_ext_result_def, CaseEq "exec_result"] >>
      conj_tac
      >- (rename1 `vars_ext clean actual` >> fs[vars_ext_def] >>
          qpat_x_assum `actual = _` (fn th => once_rewrite_tac[th]) >>
          simp[eval_operand_vars_ext]) >>
      qpat_assum `run_inst_seq _ s = OK _`
        (mp_then Any mp_tac imm_readonly_seq_frame) >>
      disch_then (qspec_then `sa` mp_tac) >> simp[]) >>
  drule_all compile_array_subscript_oob >> strip_tac >>
  gvs[vars_ext_result_def, CaseEq "exec_result"] >> metis_tac[]
QED

Theorem imm_array_ctor_none_path[local]:
  !base_op idx dyn cnt ws esz sgn sa p sb s b i len ctx func.
    compile_array_subscript base_op idx dyn cnt ws esz sgn
      (compile_ptr_load T NONE LocCode) sa = (p,sb) /\
    eval_operand base_op s = SOME b /\ eval_operand idx s = SOME i /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    if idx_in_range sgn i len then
      ?t. gas_marked_path F ctx func s 0
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t j. gas_marked_path F ctx func s 0
          (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >>
  drule imm_array_ctor_none_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `EVERY (\ins. ins.inst_opcode <> GAS /\ ins.inst_opcode <> INVOKE /\
       ~is_terminator ins.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[imm_readonly_opcode]) >>
  drule_all imm_array_ctor_none_run >>
  Cases_on `idx_in_range sgn i len` >> simp[] >> strip_tac
  >- (qexists_tac `t` >> simp[] >>
      `LENGTH (FILTER (\ins. ins.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
        (simp[listTheory.LENGTH_EQ_NUM_compute, listTheory.FILTER_EQ_NIL,
              listTheory.EVERY_MEM] >> rpt strip_tac >>
         qpat_x_assum `EVERY (\ins. ins.inst_opcode <> GAS /\ _) _`
           (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
         disch_then drule >> simp[]) >>
      drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      simp[gas_marked_path_def] >> disch_then irule >>
      conj_tac >- (fs[listTheory.EVERY_MEM]) >>
      qexists_tac `bb` >> gvs[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
  simp[] >> metis_tac[]
QED

Theorem imm_array_ctor_counted_optional[local]:
  !base_op idx dyn cnt ws esz sgn imm sa p sb s b i len ctx func cenv cx es.
    compile_array_subscript base_op idx dyn cnt ws esz sgn
      (compile_ptr_load T imm LocCode) sa = (p,sb) /\
    eval_operand base_op s = SOME b /\ eval_operand idx s = SOME i /\
    (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    (!x. p = Var x ==> not_fresh_at sb x) /\
    if idx_in_range sgn i len then
      ?t. gas_marked_path F ctx func s 0 (OK t) /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        stmt_state_rel ctx func cenv cx es t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
          lookup_var x t = SOME w) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        locals_kept cenv es s t
    else ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  rpt gen_tac >> Cases_on `imm` >> simp[] >> strip_tac
  >- (conj_tac
      >- (drule (cj 3 compiler_subscript_ops_var) >> simp[]) >>
      drule_all imm_array_ctor_none_path >>
      disch_then (qspec_then `ctx` mp_tac) >>
      qpat_x_assum `len = _` SUBST_ALL_TAC >>
      Cases_on `idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt)` >> simp[] >> strip_tac
      >- (`!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
             lookup_var x t = SOME w` by simp[lookup_var_def] >>
          `stmt_state_rel ctx func cenv cx es t` by
            (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
             irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
             conj_tac >> rpt strip_tac >>
             qmatch_goalsub_rename_tac `lookup_var zz` >>
             `not_fresh_at sa zz` by
               (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
             simp[lookup_var_def]) >>
          qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
          simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
               eval_operand_def, lookup_var_def] >>
          drule imm_array_ctor_none_code >> strip_tac >>
          qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
          fs[same_blocks_def, exprSimPropsTheory.locals_kept_mem]) >>
      goal_assum $ drule_at Any) >>
  drule_all imm_array_ctor_counted >> simp[]
QED

Theorem imm_place_at_extend[local]:
  !cenv cx es src id path w ty tv sub d etv ety.
    imm_place_at cenv cx es (PlaceR (ImmutablePlace src id path)) w ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    evaluate_type (get_tenv cx) ety = SOME etv /\
    mem_step_offset tv sub = SOME (d,etv) /\
    (!itv iv.
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
        SOME (itv,iv) ==>
      ?ev. evaluate_subscripts itv iv (path ++ [sub]) = INL ev) ==>
    imm_place_at cenv cx es (PlaceR (ImmutablePlace src id (path ++ [sub])))
      (w + n2w d) ety
Proof
  rpt strip_tac >> gvs[imm_place_at_def] >>
  drule_all exprSimPropsTheory.mem_path_offset_snoc >> strip_tac >>
  qexists_tac `k + d` >>
  simp[wordsTheory.word_add_n2w, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem imm_extend_place_step[local]:
  !cx es src id path itv iv tv v sub ev.
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
        SOME (itv,iv) /\
    subscripts_type itv path = SOME tv /\
    evaluate_subscripts itv iv path = INL v /\
    evaluate_subscripts tv v [sub] = INL ev ==>
    extend_place cx (PlaceR (ImmutablePlace src id path)) sub es =
      (INL (PlaceR (ImmutablePlace src id (path ++ [sub]))), es)
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       ignore_bind_def, lift_option_type_def, lift_sum_def, return_def,
       extend_memory_place_def]
QED

Theorem imm_extend_place_attr[local]:
  !cx es src id path itv iv tv v fld res ee.
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
        SOME (itv,iv) /\
    subscripts_type itv path = SOME tv /\
    evaluate_subscripts itv iv path = INL v /\
    extend_place cx (PlaceR (ImmutablePlace src id path))
      (AttrSubscript fld) es = (res,ee) /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ee = es /\
    res = INL (PlaceR (ImmutablePlace src id (path ++ [AttrSubscript fld]))) /\
    ?ev. evaluate_subscripts itv iv (path ++ [AttrSubscript fld]) = INL ev
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       ignore_bind_def, lift_option_type_def, lift_sum_def, return_def,
       extend_memory_place_def] >>
  Cases_on `v` >> simp[evaluate_subscripts_def, raise_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `ALOOKUP vals fld` >> Cases_on `ALOOKUP vals fld` >>
  gvs[raise_def, return_def] >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[AttrSubscript fld]` mp_tac) >>
  simp[evaluate_subscripts_def]
QED

Theorem imm_attr_place_step[local]:
  !cenv cx env es pv w sid fld fty res ee.
    expr_sim_inv cenv cx env es /\
    imm_place_at cenv cx es pv w (StructT sid) /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
    extend_place cx pv (AttrSubscript fld) es = (res,ee) /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ee = es /\
    ?pv'. res = INL pv' /\
      imm_place_at cenv cx es pv'
        (w + n2w (target_field_offset cenv (SOME LocCode)
                    (SOME (ValPT (StructT sid))) fld)) fty
Proof
  rpt gen_tac >> strip_tac >>
  drule_all stmtSimAssignAttrTheory.attribute_type_struct_field >> strip_tac >>
  Cases_on `pv` >> gvs[imm_place_at_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[imm_place_at_def] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  drule_all imm_extend_place_attr >> strip_tac >> gvs[] >>
  drule_all exprSimFieldLayoutTheory.struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all exprSimAttributeFieldsTheory.struct_field_type >> strip_tac >>
  drule_all exprSimAttributeFieldsTheory.mem_field_offset_layout >> strip_tac >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld, ftv)` by
    simp[mem_step_offset_def] >>
  drule_all exprSimPropsTheory.mem_path_offset_snoc >> strip_tac >>
  simp[target_field_offset_def, imm_place_at_def] >>
  pure_rewrite_tac[wordsTheory.word_add_n2w, arithmeticTheory.ADD_ASSOC] >>
  REFL_TAC
QED

Theorem imm_attr_source_tail[local]:
  !cenv cx es pv w ty fld res ee.
    imm_place_at cenv cx es pv w ty /\
    extend_place cx pv (AttrSubscript fld) es = (res,ee) /\
    (!m. res <> INR (Error (TypeError m))) ==>
    !gs. extend_place cx pv (AttrSubscript fld) (es with gas_obs := gs) =
      (res,ee with gas_obs := gs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `pv` >> gvs[imm_place_at_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[imm_place_at_def] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  drule_all imm_extend_place_attr >> strip_tac >> gvs[] >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[AttrSubscript fld]` assume_tac) >>
  gen_tac >> irule imm_extend_place_step >> simp[] >>
  metis_tac[]
QED

Theorem imm_target_post_add[local]:
  !ctx func cenv cx es sa sm sb s0 ee pv ty rb s dst w0 off pv' ty'.
    imm_target_post ctx func cenv cx es sa sm s0 ee pv ty rb s /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
    eval_operand (FST rb) s = SOME w0 /\
    imm_place_at cenv cx ee pv' (w0 + n2w off) ty' ==>
    ?q. run_inst_seq (emitted_insts sm sb) s = OK q /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv' ty'
          (dst, SOME LocCode, SOME (ValPT ty')) q
Proof
  rpt strip_tac >> drule_all emitHelperPropsTheory.buffer_emit_add_run >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sm.cs_next_var)` >>
  qexists_tac `update_var x (w0 + n2w off) s` >> simp[] >>
  `!z. not_fresh_at sa z ==> z <> x` by
    (rw[Abbr `x`, not_fresh_at_def] >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `!z. not_fresh_at sa z ==>
       lookup_var z (update_var x (w0 + n2w off) s) = lookup_var z s` by
    metis_tac[emitHelperPropsTheory.lookup_var_update_var] >>
  `not_local_ptr cenv ee.scopes x` by
    (rw[not_local_ptr_def] >> strip_tac >>
     metis_tac[local_ptrs_reserved_def]) >>
  fs[imm_target_post_def] >>
  `stmt_state_rel ctx func cenv cx ee (update_var x (w0 + n2w off) s)` by
    metis_tac[stmt_state_rel_update_var] >>
  simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >> rpt conj_tac
  >~ [`not_fresh_at sb _`]
  >- simp[Abbr `x`, not_fresh_at_def, ASCIInumbersTheory.toString_11]
  >~ [`locals_kept _ _ _ (update_var _ _ _)`]
  >- (irule exprSimPropsTheory.locals_kept_mem_tail >> qexists_tac `s` >> simp[update_var_def]) >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem imm_target_post_inst_idx[local,simp]:
  !ctx func cenv cx es sa sb s0 ee pv ty r s n.
    imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r
      (s with vs_inst_idx := n) <=>
    imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r s
Proof
  rpt gen_tac >>
  `!q. eval_operand q (s with vs_inst_idx := n) = eval_operand q s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[imm_target_post_def, stmt_state_rel_inst_idx, lookup_var_def,
       locals_kept_def]
QED

Theorem imm_attr_add_path[local]:
  !ctx func cenv cx es sa sm sb s0 ee pv ty rb dst off pv' ty' t w0.
    imm_target_post ctx func cenv cx es sa sm s0 ee pv ty rb t /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
    fn_has_code sm sb func /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand (FST rb) t = SOME w0 /\
    imm_place_at cenv cx ee pv' (w0 + n2w off) ty' ==>
    ?q. gas_marked_path F ctx func t 0 (OK q) /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv' ty'
          (dst, SOME LocCode, SOME (ValPT ty')) q /\
        q.vs_current_bb = sb.cs_current_bb /\
        q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all imm_target_post_add >> strip_tac >>
  drule_all emitHelperPropsTheory.buffer_emit_add_run >> strip_tac >> gvs[] >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
                 (w0 + n2w off) t with vs_inst_idx := SUC t.vs_inst_idx` >>
  simp[] >> rpt conj_tac
  >- (pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
      qpat_assum `t.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
      irule emitHelperPropsTheory.emit_op_zero_path >> simp[] >>
      qexistsl_tac [`[FST rb; Lit (n2w off)]`, `dst`, `ADD`, `sb`] >>
      simp[venomInstTheory.is_terminator_def] >> gen_tac >>
      irule emitHelperPropsTheory.step_ADD >> simp[eval_operand_def]) >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, update_var_def]
QED

Theorem imm_attr_walk_compose[local]:
  !ctx func cenv cx env es sa sm sb s0 bt sid fld fty rb dst.
    expr_sim_inv cenv cx env (es with gas_obs := []) /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [FST rb; Lit (n2w (target_field_offset cenv
      (FST (SND rb)) (SND (SND rb)) fld))] sm = (dst,sb) /\
    fn_has_code sm sb func /\
    gas_admissible (bind (eval_base_place cx bt)
      (\pv. extend_place cx pv (AttrSubscript fld))) target_res_ok es /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
        imm_target_post ctx func cenv cx es sa sm s0 ee pv (StructT sid) rb t /\
        t.vs_current_bb = sm.cs_current_bb /\
        t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (\res ee r. expr_exit res r) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld)))
      (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv fty
          (dst,FST (SND rb),target_field_type cenv (SND (SND rb)) fld) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "summary" >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume imm_attr_walk_compose[summary]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL pv, es with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `extend_place cx pv (AttrSubscript fld) (es with gas_obs := [])` >>
  rename1 `extend_place _ _ _ _ = (res1,es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
        imm_place_at cenv cx (es with gas_obs := []) pv w0 (StructT sid)` by
    (fs[imm_target_post_def] >> metis_tac[]) >>
  `FST (SND rb) = SOME LocCode /\
   SND (SND rb) = SOME (ValPT (StructT sid))` by
    fs[imm_target_post_def] >>
  `target_field_type cenv (SND (SND rb)) fld = SOME (ValPT fty)` by
    (drule_all stmtSimAssignAttrTheory.attribute_type_struct_field >>
     strip_tac >> simp[target_field_type_def]) >>
  drule_all imm_attr_source_tail >> strip_tac >>
  `expr_sim_inv cenv cx env (es with gas_obs := [])` by simp[] >>
  drule_all imm_attr_place_step >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) imm_attr_add_path >>
  disch_then (drule_at (Pat `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL pv'`, `es_end`, `OK q`] >> simp[] >>
  irule (Q.INST [`right` |-> `[]`]
    gasSummaryComposeTheory.gas_marked_exec_bind_normal
    |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`es_end`, `t`, `pv`] >>
  simp[gas_marked_exec_def, gas_explicit_nil] >>
  gen_tac >>
  `es_end with gas_obs := tail = es with gas_obs := tail` by
    (qpat_x_assum `es_end with gas_obs := [] = _`
      (mp_tac o Q.AP_TERM `\zz:evaluation_state. zz with gas_obs := tail`) >>
     simp[]) >>
  simp[]
QED

Finalise imm_attr_walk_compose

Theorem imm_target_attr_step[local]:
  !ctx func cenv cx env es sa sb s0 bt fld fty r.
    expr_sim_inv cenv cx env es /\ local_ptrs_reserved cenv sa /\
    type_place_target env (AttributeTarget bt fld) = SOME (Type fty) /\
    compile_get_target_ptr compile_expr cenv (AttributeTarget bt fld) sa = (r,sb) /\
    fn_has_code sa sb func /\
    gas_admissible (eval_base_place cx (AttributeTarget bt fld)) target_res_ok es /\
    (!bty sm rb.
      type_place_target env bt = SOME (Type bty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
      fn_has_code sa sm func /\
      gas_admissible (eval_base_place cx bt) target_res_ok es ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
        (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
          imm_target_post ctx func cenv cx es sa sm s0 ee pv bty rb t /\
          t.vs_current_bb = sm.cs_current_bb /\
          t.vs_inst_idx = LENGTH sm.cs_current_insts)
        (\res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_base_place cx (AttributeTarget bt fld)) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv fty r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var`
    by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))`
    by simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  irule imm_attr_walk_compose >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`sid`, `sm`] >> simp[]
QED

Theorem imm_extend_place_index[local]:
  !cx es src id path itv iv etv bd av ix.
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
        SOME (itv,iv) /\
    subscripts_type itv path = SOME (ArrayTV etv bd) /\
    evaluate_subscripts itv iv path = INL (ArrayV av) ==>
    extend_place cx (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV ix)) es =
    (case array_index (ArrayTV etv bd) av ix of
       NONE => (INR (Error (RuntimeError "evaluate_subscripts array_index")),es)
     | SOME v =>
       (INL (PlaceR (ImmutablePlace src id
          (path ++ [ValueSubscript (IntV ix)]))),es))
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       ignore_bind_def, lift_option_type_def, lift_sum_def, return_def,
       extend_memory_place_def, evaluate_subscripts_def] >>
  Cases_on `array_index (ArrayTV etv bd) av ix` >>
  simp[return_def, raise_def, evaluate_subscripts_def]
QED

(* The counted walk of a target rooted at an immutable in the
   constructor, with pure indices, given their judgments, the
   constructor's compile env and the root's declared type in it: from s0
   related at es, the target's fragment ends at the place's pointer
   (imm_target_post), the source state unchanged, or exits as the source
   does.  Admitted pending alan; provable as stated, no invariant change
   needed. *)
Theorem imm_index_word_range[local]:
  !sgn i ix n.
    n < dimword (:256) /\ i = (integer_word$i2w ix : bytes32) /\
    (if sgn then -(&(2 ** 255)) <= ix /\ ix < &(2 ** 255)
     else 0 <= ix /\ ix < &(dimword (:256))) ==>
    (idx_in_range sgn i (n2w n) <=> 0 <= ix /\ Num ix < n)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `sgn`
  >- (`integer_word$w2i (integer_word$i2w ix : bytes32) = ix` by
        (irule integer_wordTheory.w2i_i2w >>
         simp[wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def] >>
         intLib.ARITH_TAC) >>
      simp[idx_in_range_def, integer_wordTheory.WORD_LTi,
           integer_wordTheory.w2i_eq_w2n] >>
      Cases_on `ix < 0` >- intLib.ARITH_TAC >>
      `0 <= ix` by intLib.ARITH_TAC >>
      `Num ix < dimword (:256)` by
        (simp[wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
      simp[integer_wordTheory.i2w_def]) >>
  gvs[] >>
  `~(ix < 0)` by intLib.ARITH_TAC >>
  `Num ix < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  simp[idx_in_range_def, integer_wordTheory.i2w_def]
QED

Theorem imm_index_word_nat[local]:
  !sgn i ix n.
    n < dimword (:256) /\ i = (integer_word$i2w ix : bytes32) /\
    (if sgn then -(&(2 ** 255)) <= ix /\ ix < &(2 ** 255)
     else 0 <= ix /\ ix < &(dimword (:256))) /\
    idx_in_range sgn i (n2w n) ==>
    i = n2w (Num ix)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all imm_index_word_range >> strip_tac >>
  `0 <= ix` by metis_tac[] >>
  qpat_x_assum `if sgn then _ else _` kall_tac >>
  `~(ix < 0)` by intLib.ARITH_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

Theorem imm_array_index_range[local]:
  !etv bd av ix n sgn i.
    n = array_length (ArrayTV etv bd) av /\ n < dimword (:256) /\
    i = (integer_word$i2w ix : bytes32) /\
    (if sgn then -(&(2 ** 255)) <= ix /\ ix < &(2 ** 255)
     else 0 <= ix /\ ix < &(dimword (:256))) /\
    (!al. av = SArrayV al ==> ?k. bd = Fixed k) ==>
    (IS_SOME (array_index (ArrayTV etv bd) av ix) <=>
     idx_in_range sgn i (n2w n))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all imm_index_word_range >> disch_then SUBST1_TAC >>
  Cases_on `av` >> gvs[vyperValueOperationTheory.array_index_def,
                       vyperValueOperationTheory.array_length_def] >>
  simp[listTheory.oEL_THM] >>
  simp[COND_RAND] >>
  Cases_on `ALOOKUP l (Num ix)` >> simp[]
QED

Theorem imm_typed_array_length[local]:
  !tenv et bd etv av.
    evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) ==>
    array_length (ArrayTV etv bd) av < dimword (:256) /\
    (!al. av = SArrayV al ==> ?k. bd = Fixed k)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperValueOperationTheory.array_length_def, vyperValueTheory.type_slot_size_def,
      bound_length_def] >>
  `n <= n * type_slot_size etv` by
    (once_rewrite_tac[GSYM arithmeticTheory.MULT_RIGHT_1] >>
     simp[arithmeticTheory.LE_MULT_LCANCEL]) >>
  decide_tac
QED

Theorem imm_typed_index_interval[local]:
  !tenv ity itv ix.
    is_int_type ity /\ evaluate_type tenv ity = SOME itv /\
    value_has_type itv (IntV ix) ==>
    (if is_signed_type ity then
       -(&(2 ** 255)) <= ix /\ ix < &(2 ** 255)
     else 0 <= ix /\ ix < &(dimword (:256)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ity` >> gvs[] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      vyperTypingTheory.value_has_type_def, is_signed_type_def,
      vyperValueTheory.within_int_bound_def]
  >- (`2 ** n <= 2 ** 256` by simp[] >>
      `ix = &Num ix` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
      `Num ix < 2 ** 256` by decide_tac >>
      qpat_x_assum `ix = &Num ix` SUBST1_TAC >> gvs[]) >>
  `n - 1 <= 255` by decide_tac >>
  `2 ** (n - 1) <= 2 ** 255` by simp[] >>
  Cases_on `ix < 0`
  >- (`Num (-ix) <= 2 ** 255` by
        (qpat_x_assum `if _ then _ else _` mp_tac >>
         pure_asm_rewrite_tac[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      `-ix = &Num (-ix)` by
        (simp[Once $ GSYM integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC) >>
      qpat_x_assum `if _ then _ else _` kall_tac >>
      qpat_x_assum `Num (-ix) <= _` mp_tac >>
      pure_once_rewrite_tac[GSYM integerTheory.INT_LE] >>
      simp[] >> intLib.ARITH_TAC) >>
  `Num ix < 2 ** 255` by
    (qpat_x_assum `if _ then _ else _` mp_tac >>
     pure_asm_rewrite_tac[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `ix = &Num ix` by
    (simp[Once $ GSYM integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC) >>
  qpat_x_assum `if _ then _ else _` kall_tac >>
  qpat_x_assum `Num ix < _` mp_tac >>
  pure_once_rewrite_tac[GSYM integerTheory.INT_LT] >>
  simp[] >> intLib.ARITH_TAC
QED

Theorem imm_typed_array_index_range[local]:
  !tenv et bd etv av ity itv ix i.
    evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    is_int_type ity /\ evaluate_type tenv ity = SOME itv /\
    value_has_type itv (IntV ix) /\ i = val_to_w256 (IntV ix) ==>
    (array_index (ArrayTV etv bd) av ix = NONE <=>
       ~idx_in_range (is_signed_type ity) i
         (n2w (array_length (ArrayTV etv bd) av))) /\
    (idx_in_range (is_signed_type ity) i
       (n2w (array_length (ArrayTV etv bd) av)) ==>
       i = n2w (Num ix))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all imm_typed_array_length >> strip_tac >>
  drule_all imm_typed_index_interval >> strip_tac >>
  fs[valueEncodingTheory.val_to_w256_def] >>
  `IS_SOME (array_index (ArrayTV etv bd) av ix) <=>
     idx_in_range (is_signed_type ity) i
       (n2w (array_length (ArrayTV etv bd) av))` by
    (irule imm_array_index_range >> simp[] >> goal_assum $ drule_at Any) >>
  conj_tac >- (Cases_on `array_index (ArrayTV etv bd) av ix` >> gvs[]) >>
  strip_tac >> irule imm_index_word_nat >> simp[] >>
  qexistsl_tac [`array_length (ArrayTV etv bd) av`, `is_signed_type ity`] >>
  simp[]
QED

Theorem imm_typed_array_step_offset[local]:
  !cenv cx env es et bd etv av ix v.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    array_index (ArrayTV etv bd) av ix = SOME v ==>
    mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV ix)) =
      SOME ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
            Num ix * elem_size_in_location cenv LocCode et, etv)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) et = SOME etv` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> strip_tac >>
  drule_all imm_typed_array_length >> strip_tac >>
  `valid_index (ArrayTV etv bd) av ix` by
    (irule vyperArrayTheory.array_index_bounds >>
     conj_tac >- metis_tac[] >> goal_assum $ drule_at Any) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperValueOperationTheory.array_length_def,
      vyperArrayTheory.valid_index_def,
      mem_step_offset_def, elem_size_in_location_def, is_slot_addressed_def] >>
  `ix = &Num ix` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  qpat_x_assum `ix < _` mp_tac >>
  qpat_x_assum `ix = &Num ix` SUBST1_TAC >> simp[] >> decide_tac
QED

Theorem imm_index_place_step[local]:
  !cenv cx env es pv w et bd ix pv' ee.
    expr_sim_inv cenv cx env es /\
    imm_place_at cenv cx es pv w (ArrayT et bd) /\
    extend_place cx pv (ValueSubscript (IntV ix)) es = (INL pv',ee) ==>
    ee = es /\
    imm_place_at cenv cx es pv'
      (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                Num ix * elem_size_in_location cenv LocCode et)) et
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `pv` >> gvs[imm_place_at_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[imm_place_at_def] >>
  `?etv. tv = ArrayTV etv bd /\
          evaluate_type (get_tenv cx) et = SOME etv` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  drule_all imm_place_at_value_type >> strip_tac >>
  `?av. v = ArrayV av` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >> gvs[] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  drule_all imm_extend_place_index >>
  Cases_on `array_index (ArrayTV etv bd) av ix` >> simp[] >> strip_tac >> gvs[] >>
  drule_all imm_typed_array_step_offset >> strip_tac >>
  drule_all exprSimPropsTheory.mem_path_offset_snoc >> strip_tac >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[ValueSubscript (IntV ix)]` assume_tac) >>
  simp[imm_place_at_def, evaluate_subscripts_def] >>
  pure_rewrite_tac[wordsTheory.word_add_n2w, arithmeticTheory.ADD_ASSOC] >>
  REFL_TAC
QED

Theorem imm_target_post_after_index[local]:
  !ctx func cenv cx es sa sm sn s0 em pv ty rb t e gs res ee v op u.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM em.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= sn.cs_next_var /\
    imm_target_post ctx func cenv cx es sa sm s0 em pv ty rb t /\
    pure_expr e /\
    bind (eval_expr cx e) (read_result cx) (em with gas_obs := gs) = (res,ee) /\
    (!l. FST rb <> Label l) /\
    expr_post ctx func cenv cx e em sm sn t (ee with gas_obs := []) v op u ==>
    imm_target_post ctx func cenv cx es sa sn s0 (ee with gas_obs := []) pv ty rb u
Proof
  rpt gen_tac >> strip_tac >>
  `?w. eval_operand (FST rb) t = SOME w /\ imm_place_at cenv cx em pv w ty`
    by (fs[imm_target_post_frame] >> metis_tac[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sm x` by fs[imm_target_post_frame] >>
  drule_all imm_place_at_index_post >> strip_tac >>
  gvs[imm_place_at_gas_obs] >>
  simp[imm_target_post_frame] >> rpt conj_tac
  >- fs[expr_post_def]
  >- fs[imm_target_post_frame]
  >- fs[imm_target_post_frame]
  >- (fs[imm_target_post_frame] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`em`, `sm`, `t`] >>
      fs[imm_target_post_frame] >>
      metis_tac[expr_post_frame]) >>
  metis_tac[]
QED

Theorem imm_target_post_after_index_reset[local]:
  !ctx func cenv cx es sa sm sn s0 pv ty rb t e gs res v op u.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= sn.cs_next_var /\
    imm_target_post ctx func cenv cx es sa sm s0 (es with gas_obs := []) pv ty rb t /\
    pure_expr e /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (res,es with gas_obs := []) /\
    (!l. FST rb <> Label l) /\
    expr_post ctx func cenv cx e (es with gas_obs := []) sm sn t
      (es with gas_obs := []) v op u ==>
    imm_target_post ctx func cenv cx es sa sn s0 (es with gas_obs := []) pv ty rb u
Proof
  rpt gen_tac >> strip_tac >>
  irule (imm_target_post_after_index |> SPEC_ALL |>
    Q.INST [`em` |-> `es with gas_obs := []`, `ee` |-> `es with gas_obs := []`] |>
    GEN_ALL |> SRULE []) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem imm_gas_outcome_bind_result[local]:
  !memory tops ctx func (source : evaluation_state -> eval_result evaluation_result)
    es s0 P R next Q.
    gas_outcome memory tops (ctx,func) source (es,s0)
      (\res ee t. ?v. res = INL v /\ P v ee t)
      (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
    (!marks v mid t.
      gas_marked_exec memory (ctx,func) source (es,s0) marks (INL v) mid (OK t) /\
      P v (mid with gas_obs := []) t ==>
      gas_outcome memory tops (ctx,func) (next v)
        (mid with gas_obs := [],t) Q R) ==>
    gas_outcome memory tops (ctx,func) (bind source next) (es,s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "summary" >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume imm_gas_outcome_bind_result[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> simp[]) >>
  first_x_assum drule_all >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "tail_summary" >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[GSYM ignore_bind_def]
QED

Resume imm_gas_outcome_bind_result[tail_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`, `t`, `v`] >> gvs[]
QED

Finalise imm_gas_outcome_bind_result

Theorem imm_gas_outcome_bind_value[local]:
  !memory tops ctx func (source : evaluation_state -> value evaluation_result)
    es s0 P R next Q.
    gas_outcome memory tops (ctx,func) source (es,s0)
      (\res ee t. ?v. res = INL v /\ P v ee t)
      (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
    (!marks v mid t.
      gas_marked_exec memory (ctx,func) source (es,s0) marks (INL v) mid (OK t) /\
      P v (mid with gas_obs := []) t ==>
      gas_outcome memory tops (ctx,func) (next v)
        (mid with gas_obs := [],t) Q R) ==>
    gas_outcome memory tops (ctx,func) (bind source next) (es,s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "summary" >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[ignore_bind_def]
QED

Resume imm_gas_outcome_bind_value[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> simp[]) >>
  first_x_assum drule_all >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "tail_summary" >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[GSYM ignore_bind_def]
QED

Resume imm_gas_outcome_bind_value[tail_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`, `t`, `v`] >> gvs[]
QED

Finalise imm_gas_outcome_bind_value

Theorem imm_subscript_compile_parts[local]:
  !cenv bt e sa rb sm et bd r sb.
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    FST (SND rb) = SOME LocCode /\
    SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
    compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) ==>
    ?op sn dst.
      lower_value compile_expr cenv (expr_type e) e sm = (op,sn) /\
      compile_array_subscript (FST rb) op
        (case bd of Fixed _ => F | Dynamic _ => T)
        (case bd of Fixed n => n | Dynamic _ => 0)
        (word_scale LocCode) (elem_size_in_location cenv LocCode et)
        (is_signed_type (expr_type e))
        (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb) /\
      r = (dst,SOME LocCode,SOME (ValPT et))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `bd` >> simp[] >> strip_tac >> gvs[]
QED

Theorem imm_target_type_only[local]:
  !bt env cx cenv es src id vt.
    expr_sim_inv cenv cx env es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    type_place_target env bt = SOME vt ==> ?ty. vt = Type ty
Proof
  Induct_on `bt` using base_assignment_target_induct >>
  rpt gen_tac >> strip_tac >>
  gvs[target_root_def, Once well_typed_expr_def, AllCaseEqs()]
  >- (`env_context_consistent env cx` by
        fs[expr_sim_inv_def, env_consistent_def] >>
      Cases_on `vt` >> simp[] >>
      fs[env_context_consistent_def] >>
      qpat_x_assum `!src id kt vt. _ ==> _` drule >>
      strip_tac >> res_tac >> gvs[]) >>
  `?bty. vt' = Type bty` by metis_tac[] >> gvs[] >>
  Cases_on `bty` >> gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem imm_target_subscript_type[local]:
  !bt e env cx cenv es src id ty.
    expr_sim_inv cenv cx env es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    type_place_target env (SubscriptTarget bt e) = SOME (Type ty) ==>
    ?bd. type_place_target env bt = SOME (Type (ArrayT ty bd)) /\
         well_typed_expr env e /\ is_int_type (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  drule_all imm_target_type_only >> strip_tac >> gvs[] >>
  rename1 `subscript_vtype (Type bty) _ = _` >>
  Cases_on `bty` >> gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem imm_subscript_base_code[local]:
  !cenv bt e sa rb sm r sb func.
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
    fn_has_code sa sb func ==>
    fn_has_code sa sm func /\ cs_extends sm sb
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_get_target_ptr_def]) >>
  qmatch_goalsub_abbrev_tac `comp_bind _ rest` >>
  `!result st. ci_mono st (SND (rest result st))` by
    (rpt gen_tac >> Cases_on `SND (SND result)`
     >- (simp[Abbr `rest`, LET_THM] >>
         match_mp_tac ci_mono_bind >> conj_tac
         >- simp[stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
         rpt gen_tac >> BETA_TAC >> match_mp_tac ci_mono_bind >>
         simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
              ci_mono_comp_return]) >>
     rename1 `SND (SND result) = SOME pt` >> Cases_on `pt`
     >- (simp[Abbr `rest`, LET_THM] >>
         match_mp_tac ci_mono_bind >> conj_tac
         >- simp[stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
         rpt gen_tac >> BETA_TAC >> match_mp_tac ci_mono_bind >> conj_tac
         >- (rpt gen_tac >> IF_CASES_TAC >>
             simp[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
         rpt gen_tac >> BETA_TAC >> match_mp_tac ci_mono_bind >>
         simp[ci_mono_compile_mapping_subscript, ci_mono_comp_return]) >>
     simp[Abbr `rest`, LET_THM] >>
     match_mp_tac ci_mono_bind >> conj_tac
     >- simp[stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
     rpt gen_tac >> BETA_TAC >> match_mp_tac ci_mono_bind >>
     simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
          ci_mono_comp_return]) >>
  simp[comp_bind_def] >> strip_tac >>
  `ci_mono sm sb` by metis_tac[pairTheory.SND] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem imm_expr_exit_inr[local]:
  !(res : 'a + exception) r.
    expr_exit res r <=>
      ?exc. res = INR exc /\ expr_exit (INR exc : 'a + exception) r
Proof
  Cases >> simp[]
QED

Theorem imm_mapping_compile_not_label[local]:
  !base_op key sa op sb.
  compile_mapping_subscript base_op key sa = (op,sb) ==>
  !l. op <> Label l
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem imm_array_compile_not_label[local]:
  !base_op idx dyn cnt ws esz sgn loader sa op sb.
  compile_array_subscript base_op idx dyn cnt ws esz sgn loader sa = (op,sb) ==>
  !l. op <> Label l
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem imm_target_compile_not_label[local]:
  compile_get_target_ptr cfn cenv bt sa = (r,sb) /\
  target_root bt = TopLevelNameTarget (src,id) ==>
  !l. FST r <> Label l
Proof
  Cases_on `bt` >> simp[target_root_def]
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars p` >> simp[comp_return_def] >>
      Cases_on `x` >> simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[Once compile_get_target_ptr_def, LET_THM, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) 
  >- (Cases_on `SND (SND result)`
      >- (gvs[comp_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> gvs[]) >>
          imp_res_tac imm_array_compile_not_label >> rpt strip_tac >> gvs[]) >>
      Cases_on `x` >> gvs[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac imm_array_compile_not_label >>
      imp_res_tac imm_mapping_compile_not_label >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem imm_field_offset_footprint[local]:
  !fields id k child.
    mem_field_offset fields id = SOME (k,child) ==>
    k + type_memory_size child <= type_memory_size_fields fields
Proof
  Induct >> simp[mem_field_offset_def, valueEncodingTheory.type_memory_size_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[mem_field_offset_def, valueEncodingTheory.type_memory_size_def] >>
  Cases_on `h0 = id` >> gvs[AllCaseEqs()] >>
  simp[pairTheory.EXISTS_PROD] >> strip_tac >> gvs[] >>
  first_x_assum drule >> decide_tac
QED

Theorem imm_tuple_offset_footprint[local]:
  !tvs i. i < LENGTH tvs ==>
    type_memory_size_list (TAKE i tvs) + type_memory_size (EL i tvs) <=
      type_memory_size_list tvs
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `i` >>
  simp[valueEncodingTheory.type_memory_size_def] >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem imm_step_offset_footprint[local]:
  !tv sub k child.
    mem_step_offset tv sub = SOME (k,child) ==>
    k + type_memory_size child <= type_memory_size tv
Proof
  Cases >> Cases_on `sub` >> simp[mem_step_offset_def] >>
  rpt gen_tac >>
  TRY (rename1 `ValueSubscript value` >> Cases_on `value` >>
       simp[mem_step_offset_def]) >>
  simp[mem_step_offset_def, valueEncodingTheory.type_memory_size_def, AllCaseEqs()]
  >- (strip_tac >> gvs[] >> drule imm_tuple_offset_footprint >> simp[])
  >- (Cases_on `b` >> simp[mem_step_offset_def,
        valueEncodingTheory.type_memory_size_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      `Num i + 1 <= n` by decide_tac >>
      ` (Num i + 1) * type_memory_size child <= n * type_memory_size child` by
        simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
                       arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  metis_tac[imm_field_offset_footprint]
QED

Theorem imm_path_offset_footprint[local]:
  !path tv k child.
    mem_path_offset tv path = SOME (k,child) ==>
    k + type_memory_size child <= type_memory_size tv
Proof
  Induct >> simp[mem_path_offset_def] >> rpt gen_tac >>
  simp[AllCaseEqs(), pairTheory.EXISTS_PROD] >> strip_tac >> gvs[] >>
  drule imm_step_offset_footprint >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem imm_path_offset_nonwrap[local]:
  !tv path k child off.
    mem_path_offset tv path = SOME (k,child) /\
    off + type_memory_size tv < dimword (:256) ==>
    off + k < dimword (:256)
Proof
  rpt strip_tac >> drule imm_path_offset_footprint >> decide_tac
QED

Theorem imm_target_subscript_step[local]:
  !nocalls ctx func cenv cx env es sa sb s0 bt e ty r src id.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    expr_sim_inv cenv cx env es /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    target_idx_case nocalls ctx func cenv cx (SubscriptTarget bt e) /\
    (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
    target_indices_pre cenv cx env (SubscriptTarget bt e) /\ pure_expr e /\
    type_place_target env (SubscriptTarget bt e) = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
    (!bty sm rb.
      type_place_target env bt = SOME (Type bty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
      fn_has_code sa sm func /\
      gas_admissible (eval_base_place cx bt) target_res_ok es ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
        (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
          imm_target_post ctx func cenv cx es sa sm s0 ee pv bty rb t /\
          t.vs_current_bb = sm.cs_current_bb /\
          t.vs_inst_idx = LENGTH sm.cs_current_insts)
        (\res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_base_place cx (SubscriptTarget bt e)) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all imm_target_subscript_type >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr compile_expr cenv bt sa = (rb,sm)` >>
  drule_all imm_subscript_base_code >> strip_tac >>
  `eval_base_place cx (SubscriptTarget bt e) =
     bind (eval_base_place cx bt) (\pv.
       bind (bind (eval_expr cx e) (read_result cx))
         (\v. extend_place cx pv (ValueSubscript v)))` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_assoc] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  irule imm_gas_outcome_bind_result >>
  qexists_tac `\pv ee t. ee = es with gas_obs := [] /\
    imm_target_post ctx func cenv cx es sa sm s0 ee pv (ArrayT ty bd) rb t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  reverse conj_tac
  >- (simp[GSYM imm_expr_exit_inr] >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `FST (SND rb) = SOME LocCode /\
   SND (SND rb) = SOME (ValPT (ArrayT ty bd))` by fs[imm_target_post_def] >>
  drule_all imm_subscript_compile_parts >> strip_tac >> gvs[] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v,es with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx e` by
    (fs[target_idx_case_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := [])` by
    (fs[target_indices_pre_def] >> first_x_assum irule >> simp[]) >>
  `nocalls ==> int_calls_expr e = []` by
    fs[int_calls_expr_def] >>
  `expr_sim ctx func cenv cx (expr_type e) e (es with gas_obs := [])` by
    metis_tac[expr_sim_case_def] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm sn` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_expr_sa, pairTheory.SND] >>
  `ci_mono sn sb` by
    (`!op st. ci_mono st
        (SND (compile_ptr_load T cenv.ce_imm_alloca LocCode op st))` by
       simp[ci_mono_compile_ptr_load] >>
     drule ci_mono_compile_array_subscript >>
     disch_then assume_tac >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `local_ptrs_reserved cenv sm` by
    (fs[local_ptrs_reserved_def, ci_mono_def] >>
     conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `!gs. mid with gas_obs := gs = es with gas_obs := gs` by
    (gen_tac >>
     qpat_x_assum `mid with gas_obs := [] = _`
       (mp_tac o Q.AP_TERM `\st. st with gas_obs := gs`) >> simp[]) >>
  `!gs. eval_base_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ gs) =
      (INL v,es with gas_obs := gs)` by
    fs[gas_marked_exec_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     simp[Once bind_def] >> simp[Once bind_def] >>
     gvs[target_res_ok_def, expr_res_ok_def]) >>
  `!exc r. expr_exit (INR exc : value + exception) r =
      expr_exit (INR exc : eval_result + exception) r` by
    (Cases >> Cases >> simp[expr_exit_def] >>
     Cases_on `e'` >> simp[expr_exit_def]) >>
  irule imm_gas_outcome_bind_value >>
  qexists_tac `\iv ee u.
    expr_post ctx func cenv cx e (es with gas_obs := []) sm sn t ee iv op u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(res:value + exception) ee r. ?exc. res = INR exc /\
          expr_exit (INR exc : eval_result + exception) r) =
        (\res (ee:evaluation_state) r. expr_exit res r)` by
        (simp[FUN_EQ_THM] >> Cases >> simp[] >> metis_tac[]) >>
      BETA_TAC >> pop_assum SUBST1_TAC >> BETA_TAC >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then irule >> simp[] >> fs[imm_target_post_def]) >>
  rpt gen_tac >> strip_tac >>
  suspend "suffix"
QED

Resume imm_target_subscript_step[suffix]:
  gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `target_idx_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `target_indices_pre _ _ _ _` kall_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` kall_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _` kall_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v',mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?w. eval_operand (FST rb) t = SOME w /\
        imm_place_at cenv cx es v w (ArrayT ty bd)` by
    (fs[imm_target_post_frame] >> metis_tac[]) >>
  drule_all imm_place_at_pure_index >> strip_tac >> gvs[] >>
  `!l. FST rb <> Label l` by metis_tac[imm_target_compile_not_label] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  drule_all imm_target_post_after_index_reset >> strip_tac >>

  `word_value_type (expr_type e)` by simp[word_value_type_def] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks' t.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_word_result) >>
  strip_tac >>
  qpat_x_assum `!tv. INL v' = INL tv ==> _`
    (qspec_then `v'` mp_tac) >> simp[] >> strip_tac >>
  drule_all vyperTypeStatePreservationTheory.int_typed_value_is_IntV >>
  strip_tac >> gvs[] >>
  qpat_x_assum `target_root _ = _` kall_tac >>
  qpat_x_assum `!ts. get_module_code _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `nocalls ==> int_calls_target _ = _` kall_tac >>
  qpat_x_assum `nocalls ==> int_calls_expr _ = _` kall_tac >>
  qpat_x_assum `type_place_target _ _ = _` kall_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `gas_admissible (bind _ _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_base_place _ _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (bind _ _) _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ (eval_base_place _ _) _ _ _ _ _` kall_tac >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` kall_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` kall_tac >>
  qpat_x_assum `!gs. eval_base_place _ _ _ = _` kall_tac >>
  qpat_x_assum `!gs. mid with gas_obs := gs = _` kall_tac >>
  qpat_x_assum `imm_target_post _ _ _ _ _ _ sm _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_res_ok _` kall_tac >>
  qpat_x_assum `!exc r. _` kall_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t' /\
   ?bw. eval_operand (FST rb) t' = SOME bw /\
        imm_place_at cenv cx es v bw (ArrayT ty bd)` by
    fs[imm_target_post_frame] >>
  `?iw. eval_operand op t' = SOME iw` by
    fs[expr_post_def, expr_val_rel_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region t' = SOME 0w` by
    (fs[stmt_state_rel_def, immutable_base_zero_def]) >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def, ci_mono_def] >>
     conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[] >> metis_tac[]) >>
  `!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
      not_fresh_at sn x` by fs[local_ptrs_reserved_def] >>
  `!x. FST rb = Var x ==> not_fresh_at sn x` by
    fs[imm_target_post_def] >>
  `!x. op = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
     qexistsl [`cenv`, `e`, `op`, `sm`, `expr_type e`] >> simp[]) >>
  drule_all (imm_array_ctor_counted_optional |> SPEC_ALL |>
    Q.INST [`len` |-> `if dyn then mload (w2n b) s else n2w cnt`] |>
    GEN_ALL |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >> strip_tac >>
  `iw = val_to_w256 (IntV i)` by
    (drule exprSimSourceTheory.word_value_type_word >> strip_tac >>
     fs[expr_post_def, expr_val_rel_def, exprSimPropsTheory.typed_val_to_w256_word_value]) >>
  qpat_x_assum `monad_bind _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `imm_place_at _ _ mid' _ _ _` kall_tac >>
  qpat_x_assum `imm_place_at _ _ es v w _` kall_tac >>
  qpat_x_assum `mid' with gas_obs := [] = _` kall_tac >>
  qpat_x_assum `eval_operand (FST rb) t = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `pure_expr _` kall_tac >>
  qpat_x_assum `well_typed_expr _ _` kall_tac >>
  rpt (qpat_x_assum `fn_has_code _ _ _` kall_tac) >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  rpt (qpat_x_assum `local_ptrs_reserved _ _` kall_tac) >>
  qpat_x_assum `cs_extends _ _` kall_tac >>
  qpat_x_assum `t.vs_current_bb = _` kall_tac >>
  qpat_x_assum `t.vs_inst_idx = _` kall_tac >>
  qpat_x_assum `~t.vs_halted` kall_tac >>
  Cases_on `v` >> fs[imm_place_at_def] >>
  Cases_on `p` >> fs[imm_place_at_def] >>
  drule_all imm_place_at_value_type >> strip_tac >>
  `?etv. tv = ArrayTV etv bd /\ evaluate_type (get_tenv cx) ty = SOME etv` by
    fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  gvs[] >>
  Cases_on `v` >> fs[vyperTypingTheory.value_has_type_def] >>
  `off + k < dimword (:256)` by
    (irule imm_path_offset_nonwrap >> goal_assum (drule_at Any) >> simp[]) >>
  `val_in_memory (ArrayTV etv bd) (ArrayV a) (off+k) t'.vs_memory` by
    (irule imm_readable_path_memory >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexistsl [`ctx`, `env`, `func`] >> simp[]) >>
  `((if (case bd of Fixed _ => F | Dynamic _ => T) then
       mload ((k+off) MOD dimword (:256)) t'
     else n2w (case bd of Fixed n => n | Dynamic _ => 0)) : bytes32) =
     n2w (array_length (ArrayTV etv bd) a)` by
    (Cases_on `bd` >> Cases_on `a` >>
     gvs[vyperTypingTheory.value_has_type_def,
         vyperValueOperationTheory.array_length_def,
         valueEncodingPropsTheory.val_in_memory_dynarray,
         mload_def, valueEncodingTheory.mem_word_at_def, arithmeticTheory.ADD_COMM]) >>
  gvs[] >>
  `(array_index (ArrayTV etv bd) a i = NONE <=>
       ~idx_in_range (is_signed_type (expr_type e)) (val_to_w256 (IntV i))
          (n2w (array_length (ArrayTV etv bd) a))) /\
   (idx_in_range (is_signed_type (expr_type e)) (val_to_w256 (IntV i))
       (n2w (array_length (ArrayTV etv bd) a)) ==>
     val_to_w256 (IntV i) = n2w (Num i))` by
    (irule imm_typed_array_index_range >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` kall_tac >>
  qpat_x_assum `(if _ then mload _ _ else _) = _` kall_tac >>
  qpat_x_assum `k + type_memory_size _ <= _` kall_tac >>
  `!gs. extend_place cx (PlaceR (ImmutablePlace cenv.ce_module s l))
      (ValueSubscript (IntV i)) (es with gas_obs := gs) =
    (case array_index (ArrayTV etv bd) a i of
       NONE => (INR (Error (RuntimeError "evaluate_subscripts array_index")),
                es with gas_obs := gs)
     | SOME v => (INL (PlaceR (ImmutablePlace cenv.ce_module s
                    (l ++ [ValueSubscript (IntV i)]))), es with gas_obs := gs))` by
    (gen_tac >> irule imm_extend_place_index >> simp[]) >>
  Cases_on `array_index (ArrayTV etv bd) a i`
  >- suspend "out_of_bounds"
  >> suspend "in_bounds"

QED

Resume imm_target_subscript_step[out_of_bounds]:
  gvs[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
    `es with gas_obs := []`, `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, gas_explicit_nil, expr_exit_def,
       fragExecTheory.exit_result_def]
QED

Resume imm_target_subscript_step[in_bounds]:
  gvs[] >>
  `imm_place_at cenv cx (es with gas_obs := [])
      (PlaceR (ImmutablePlace cenv.ce_module s l)) (n2w (k+off))
      (ArrayT ty bd)` by
    (fs[imm_target_post_frame] >> metis_tac[optionTheory.SOME_11]) >>
  `imm_place_at cenv cx (es with gas_obs := [])
      (PlaceR (ImmutablePlace cenv.ce_module s (l ++ [ValueSubscript (IntV i)])))
      (n2w (k+off) + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
         Num i * elem_size_in_location cenv LocCode ty)) ty` by
    (drule_at (Pat `imm_place_at _ _ _ _ _ _`) imm_index_place_step >>
     disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `eval_operand dst t = SOME (n2w (k+off) +
      n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
         Num i * elem_size_in_location cenv LocCode ty))` by
    (qpat_x_assum `eval_operand dst t = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >>
     simp[Once wordsTheory.word_add_n2w] >>
     pure_rewrite_tac[word_scale_def, is_slot_addressed_def,
          wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w,
          arithmeticTheory.ADD_CLAUSES] >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  `wb_frame cenv es sa s0 t` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`sn`, `t'`] >> simp[] >>
     fs[imm_target_post_frame] >> decide_tac) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module s
                 (l ++ [ValueSubscript (IntV i)])))`,
    `es with gas_obs := []`, `OK t`] >>
  simp[gas_marked_exec_def, gas_explicit_nil, imm_target_post_frame] >>
  qpat_x_assum `imm_place_at _ _ _ _ _ ty` mp_tac >>
  simp[imm_place_at_gas_obs, arithmeticTheory.ADD_COMM]
QED

Finalise imm_target_subscript_step

Theorem imm_target_walk:
  !bt nocalls ctx func cenv cx env es ty src id sa sb r s0.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
    EVERY pure_expr (target_indices bt) /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
         imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  Induct_on `bt` using base_assignment_target_induct >>
  rpt gen_tac >> strip_tac >>
  gvs[target_root_def]
  >- suspend "root"
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume imm_target_walk[root]:
  irule imm_target_root_walk >> simp[] >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `nocalls` >> simp[]
QED
Resume imm_target_walk[subscript]:
  fs[targetPlaceLiveTheory.target_indices_def] >>
  irule imm_target_subscript_step >> simp[] >>
  conj_tac
  >- (qexists_tac `env` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> conj_tac
      >- (qexists_tac `env` >> fs[target_indices_pre_def]) >>
      qexists_tac `nocalls` >>
      fs[target_idx_case_def, vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  qexists_tac `nocalls` >> simp[]
QED
Resume imm_target_walk[attribute]:
  fs[targetPlaceLiveTheory.target_indices_def] >>
  irule imm_target_attr_step >> simp[] >> qexists_tac `env` >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> conj_tac
      >- (qexists_tac `env` >> fs[target_indices_pre_def]) >>
      qexists_tac `nocalls` >>
      fs[target_idx_case_def, vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Finalise imm_target_walk

(* Pop consumes a place, rather than the eval_result produced by the walk. *)
Theorem imm_target_walk_place:
  !bt nocalls ctx func cenv cx env es ty src id sa sb r s0.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
    EVERY pure_expr (target_indices bt) /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
      (\res ee t. ?p. res = INL p /\ ee = es with gas_obs := [] /\
         imm_target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, bind_def] >>
     rpt strip_tac >> Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >>
     simp[target_place_res_ok_def]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
         imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)` by
    (irule imm_target_walk >> simp[] >> conj_tac
     >- (qexists `env` >> simp[]) >>
     qexists `nocalls` >> simp[]) >>
  `eval_target_place cx bt = vyperState$bind (eval_base_place cx bt) get_place` by
    simp[FUN_EQ_THM, Once evaluate_def, bind_def] >>
  pop_assum SUBST1_TAC >>
  irule imm_gas_outcome_bind_result >>
  qexists `\pv ee t. ee = es with gas_obs := [] /\
    imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(res:eval_result + exception) ee r.
          ?exc. res = INR exc /\ expr_exit (INR exc : place + exception) r) =
        (\res (ee:evaluation_state) r. expr_exit res r)` by
        (simp[FUN_EQ_THM] >> Cases >>
         simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
      BETA_TAC >> pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  Cases_on `v` >>
  gvs[imm_target_post_def, oneline imm_place_at_def] >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL p`, `es`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
       get_place_def, return_def] >>
  metis_tac[]
QED

Theorem immutable_value_bytes_rel_at:
  !tv v bytes.
    immutable_value_bytes_rel tv v bytes <=>
    LENGTH bytes = type_memory_size tv /\
    !i. i < type_memory_size tv /\ EL i (immutable_value_mask tv v) ==>
        EL i bytes = EL i (encode_immutable_value tv v)
Proof
  rpt gen_tac >>
  simp[immutableValueTheory.immutable_value_bytes_rel_def, listTheory.EVERY_EL] >>
  Cases_on `LENGTH bytes = type_memory_size tv` >> simp[] >>
  simp[listTheory.EL_ZIP, boolTheory.AND_IMP_INTRO]
QED

Theorem immutable_prefix_agreement[local]:
  !n bs bytes.
    LENGTH bs <= n /\ LENGTH bytes = n /\ TAKE (LENGTH bs) bytes = bs ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_mask_fit n (REPLICATE (LENGTH bs) T),
            ZIP (bytes, immutable_fit n bs)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[listTheory.EVERY_EL, listTheory.EL_ZIP, immutable_mask_fit_def,
       immutable_fit_def] >> rpt strip_tac >>
  gvs[listTheory.EL_TAKE, listTheory.EL_APPEND_EQN, rich_listTheory.EL_REPLICATE] >>
  metis_tac[listTheory.EL_TAKE]
QED

Theorem immutable_memory_prefix_agreement[local]:
  !cap bs off mem.
    LENGTH bs <= cap /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_mask_fit cap (REPLICATE (LENGTH bs) T),
            ZIP (mem_bytes_at off cap mem, immutable_fit cap bs)))
Proof
  rpt gen_tac >> strip_tac >> irule immutable_prefix_agreement >> simp[] >>
  `cap = LENGTH bs + (cap - LENGTH bs)` by decide_tac >>
  qpat_x_assum `cap = _` (fn th => once_rewrite_tac[th]) >>
  simp[Once abi_encoder_mem_split, rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem immutable_payload_memory_bytes[local]:
  !cap bs off mem.
    32 + LENGTH bs <= cap /\ mem_word_at off mem = n2w (LENGTH bs) /\
    mem_bytes_at (off + 32) (LENGTH bs) mem = bs ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_mask_fit cap (REPLICATE (32 + LENGTH bs) T),
            ZIP (mem_bytes_at off cap mem,
                 immutable_fit cap (word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs))))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encoder_bytes_source_prefix >> strip_tac >>
  qspecl_then [`cap`, `word_to_bytes (n2w (LENGTH bs):bytes32) T ++ bs`,
               `off`, `mem`] mp_tac immutable_memory_prefix_agreement >>
  gvs[byteTheory.LENGTH_word_to_bytes, arithmeticTheory.ADD_COMM]
QED

Theorem immutable_base_memory_bytes:
  !bt v base mem.
    immutable_value_admissible (BaseTV bt) v /\
    val_in_memory (BaseTV bt) v base mem ==>
    immutable_value_bytes_rel (BaseTV bt) v
      (mem_bytes_at base (type_memory_size (BaseTV bt)) mem)
Proof
  Cases_on `bt` >> Cases_on `v` >>
  gvs[immutable_value_admissible_def, AllCaseEqs()] >>
  gvs[valueEncodingTheory.val_in_memory_def, immutable_value_bytes_rel_def,
      immutable_value_mask_def, encode_immutable_value_def,
      immutable_word_bytes_def, valueEncodingTheory.type_memory_size_def] >>
  all_tac
  >~ [`STRLEN text`]
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`32 * word_size n + 32`, `MAP (n2w o ORD) text`,
                      `base'`, `mem`] immutable_payload_memory_bytes) >>
      simp[] >> mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >>
      decide_tac) >>
  all_tac
  >~ [`BytesT bound`]
  >- (Cases_on `bound` >>
      gvs[valueEncodingTheory.type_memory_size_def] >>
      rpt strip_tac
      >- gvs[immutable_mask_fit_def, immutable_fit_def,
             abi_encoder_word_window, byteTheory.LENGTH_word_to_bytes,
             listTheory.TAKE_LENGTH_TOO_LONG, rich_listTheory.TAKE_APPEND,
             immutable_mask_same_bytes] >>
      irule (SRULE [arithmeticTheory.ADD_COMM] immutable_payload_memory_bytes) >> simp[] >>
      mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >> decide_tac) >>
  gvs[valueEncodingTheory.val_in_memory_def, immutable_value_bytes_rel_def,
      immutable_value_mask_def, encode_immutable_value_def,
      valueEncodingTheory.type_memory_size_def, immutable_mask_fit_def, immutable_fit_def,
      immutable_word_bytes_def, valueEncodingTheory.typed_val_to_w256_def,
      abi_encoder_word_window, rich_listTheory.TAKE_APPEND,
      byteTheory.LENGTH_word_to_bytes, immutable_mask_same_bytes,
      listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem immutable_flag_memory_bytes:
  !n v base mem.
    immutable_value_admissible (FlagTV n) v /\
    val_in_memory (FlagTV n) v base mem ==>
    immutable_value_bytes_rel (FlagTV n) v
      (mem_bytes_at base (type_memory_size (FlagTV n)) mem)
Proof
  Cases_on `v` >>
  gvs[immutable_value_admissible_def, valueEncodingTheory.val_in_memory_def,
      immutable_value_bytes_rel_def, immutable_value_mask_def,
      encode_immutable_value_def, immutable_word_bytes_def,
      valueEncodingTheory.type_memory_size_def, abi_encoder_word_window,
      immutable_mask_fit_def, immutable_fit_def, rich_listTheory.TAKE_APPEND,
      byteTheory.LENGTH_word_to_bytes, listTheory.TAKE_LENGTH_TOO_LONG,
      immutable_mask_same_bytes, valueEncodingTheory.typed_val_to_w256_def]
QED

Theorem immutable_default_zero_bytes:
  !tv. immutable_value_bytes_rel tv (default_value tv)
    (REPLICATE (type_memory_size tv) (0w:word8))
Proof
  gen_tac >>
  once_rewrite_tac[GSYM (cj 1 immutableEncodingProofsTheory.no_ctor_default_encoding)] >>
  simp[]
QED

Theorem immutable_none_memory_bytes:
  !v base mem.
    immutable_value_admissible NoneTV v /\
    val_in_memory NoneTV v base mem ==>
    immutable_value_bytes_rel NoneTV v
      (mem_bytes_at base (type_memory_size NoneTV) mem)
Proof
  simp[immutable_value_bytes_rel_def, immutable_value_mask_def,
       valueEncodingTheory.type_memory_size_def, encode_immutable_value_def,
       valueEncodingTheory.mem_bytes_at_def]
QED

Theorem immutable_base_default_memory_bytes[local]:
  !bt base mem.
    val_in_memory (BaseTV bt) (default_value (BaseTV bt)) base mem ==>
    immutable_value_bytes_rel (BaseTV bt) (default_value (BaseTV bt))
      (mem_bytes_at base (type_memory_size (BaseTV bt)) mem)
Proof
  rpt gen_tac >>
  Cases_on `immutable_value_admissible (BaseTV bt) (default_value (BaseTV bt))`
  >- metis_tac[immutable_base_memory_bytes] >>
  Cases_on `bt` >>
  gvs[immutable_value_admissible_def, vyperValueTheory.default_value_def,
      valueEncodingTheory.val_in_memory_def,
      immutable_value_bytes_rel_def, immutable_value_mask_def,
      encode_immutable_value_def, immutable_word_bytes_def,
      valueEncodingTheory.type_memory_size_def,
      valueEncodingTheory.typed_val_to_w256_def,
      abi_encoder_word_window, immutable_mask_fit_def, immutable_fit_def,
      rich_listTheory.TAKE_APPEND, byteTheory.LENGTH_word_to_bytes,
      listTheory.TAKE_LENGTH_TOO_LONG, immutable_mask_same_bytes] >>
  Cases_on `b` >>
  gvs[immutable_value_admissible_def, vyperValueTheory.default_value_def,
      valueEncodingTheory.val_in_memory_def,
      valueEncodingTheory.type_memory_size_def,
      valueEncodingTheory.typed_val_to_w256_def,
      abi_encoder_word_window, immutable_mask_fit_def, immutable_fit_def,
      rich_listTheory.TAKE_APPEND, byteTheory.LENGTH_word_to_bytes,
      listTheory.TAKE_LENGTH_TOO_LONG, immutable_mask_same_bytes]
QED

Theorem immutable_masked_append[local]:
  !mask1 mask2 actual1 actual2 expected1 expected2.
    LENGTH mask1 = LENGTH actual1 /\ LENGTH actual1 = LENGTH expected1 /\
    LENGTH mask2 = LENGTH actual2 /\ LENGTH actual2 = LENGTH expected2 ==>
    (EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask1 ++ mask2, ZIP (actual1 ++ actual2, expected1 ++ expected2))) <=>
     EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask1, ZIP (actual1, expected1))) /\
     EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask2, ZIP (actual2, expected2))))
Proof
  rpt gen_tac >> strip_tac >>
  simp[GSYM rich_listTheory.ZIP_APPEND]
QED

Theorem immutable_masked_memory_append[local]:
  !mask1 mask2 expected1 expected2 base mem.
    LENGTH mask1 = LENGTH expected1 /\ LENGTH mask2 = LENGTH expected2 ==>
    (EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask1 ++ mask2,
            ZIP (mem_bytes_at base (LENGTH expected1 + LENGTH expected2) mem,
                 expected1 ++ expected2))) <=>
     EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask1, ZIP (mem_bytes_at base (LENGTH expected1) mem, expected1))) /\
     EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask2, ZIP (mem_bytes_at (base + LENGTH expected1)
                          (LENGTH expected2) mem, expected2))))
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abi_encoder_mem_split] >>
  irule immutable_masked_append >> simp[]
QED

Theorem immutable_tuple_cons_memory_bytes[local]:
  !tv tvs v vs base mem.
    immutable_value_bytes_rel tv v (mem_bytes_at base (type_memory_size tv) mem) /\
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_tuple_mask tvs vs,
            ZIP (mem_bytes_at (base + type_memory_size tv) (type_memory_size_list tvs) mem,
                 encode_immutable_tuple tvs vs))) ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_tuple_mask (tv::tvs) (v::vs),
            ZIP (mem_bytes_at base (type_memory_size_list (tv::tvs)) mem,
                 encode_immutable_tuple (tv::tvs) (v::vs))))
Proof
  map_every qx_gen_tac [`tv`, `tvs`, `v`, `vs`, `off`, `mem`] >>
  qspecl_then [`immutable_value_mask tv v`, `immutable_tuple_mask tvs vs`,
               `encode_immutable_value tv v`, `encode_immutable_tuple tvs vs`]
    mp_tac immutable_masked_memory_append >>
  simp[immutableEncodingProofsTheory.section_tuple_mask_length,
       immutableEncodingProofsTheory.immutable_tuple_length] >>
  disch_then (qspec_then `off` (qspec_then `mem` assume_tac)) >>
  simp[Once immutable_value_mask_def, Once encode_immutable_value_def,
       valueEncodingTheory.type_memory_size_def, immutable_value_bytes_rel_def]
QED

Theorem immutable_tuple_memory_bytes[local]:
  !tvs vs off mem.
    (!tv. MEM tv tvs ==> !v base memory.
       (immutable_value_admissible tv v \/ v = default_value tv) /\
       val_in_memory tv v base memory ==>
       immutable_value_bytes_rel tv v (mem_bytes_at base (type_memory_size tv) memory)) /\
    (immutable_tuple_admissible tvs vs \/ vs = MAP default_value tvs) /\
    tuple_in_memory vs tvs off mem ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_tuple_mask tvs vs,
            ZIP (mem_bytes_at off (type_memory_size_list tvs) mem,
                 encode_immutable_tuple tvs vs)))
Proof
  Induct >- simp[immutable_value_mask_def, valueEncodingTheory.type_memory_size_def,
                encode_immutable_value_def, valueEncodingTheory.mem_bytes_at_def] >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  drule immutableEncodingProofsTheory.section_tuple_cons_valid >>
  strip_tac >> gvs[valueEncodingTheory.val_in_memory_def] >>
  irule immutable_tuple_cons_memory_bytes >> conj_tac
  >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem immutable_fields_cons_memory_bytes[local]:
  !name tv fields v vs base mem.
    immutable_value_bytes_rel tv v (mem_bytes_at base (type_memory_size tv) mem) /\
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_fields_mask fields vs,
            ZIP (mem_bytes_at (base + type_memory_size tv) (type_memory_size_fields fields) mem,
                 encode_immutable_fields fields vs))) ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_fields_mask ((name,tv)::fields) ((name,v)::vs),
            ZIP (mem_bytes_at base (type_memory_size_fields ((name,tv)::fields)) mem,
                 encode_immutable_fields ((name,tv)::fields) ((name,v)::vs))))
Proof
  map_every qx_gen_tac [`name`, `tv`, `fields`, `v`, `vs`, `off`, `mem`] >>
  qspecl_then [`immutable_value_mask tv v`, `immutable_fields_mask fields vs`,
               `encode_immutable_value tv v`, `encode_immutable_fields fields vs`]
    mp_tac immutable_masked_memory_append >>
  simp[immutableEncodingProofsTheory.section_fields_mask_length,
       immutableEncodingProofsTheory.immutable_fields_length] >>
  disch_then (qspec_then `off` (qspec_then `mem` assume_tac)) >>
  simp[Once immutable_value_mask_def, Once encode_immutable_value_def,
       valueEncodingTheory.type_memory_size_def, immutable_value_bytes_rel_def]
QED

Theorem immutable_fields_memory_bytes[local]:
  !fields vs off mem.
    (!tv. MEM tv (MAP SND fields) ==> !v base memory.
       (immutable_value_admissible tv v \/ v = default_value tv) /\
       val_in_memory tv v base memory ==>
       immutable_value_bytes_rel tv v (mem_bytes_at base (type_memory_size tv) memory)) /\
    (immutable_fields_admissible fields vs \/
      vs = MAP (\(id,t). (id,default_value t)) fields) /\
    fields_in_memory vs fields off mem ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_fields_mask fields vs,
            ZIP (mem_bytes_at off (type_memory_size_fields fields) mem,
                 encode_immutable_fields fields vs)))
Proof
  Induct >- simp[immutable_value_mask_def, valueEncodingTheory.type_memory_size_def,
                encode_immutable_value_def, valueEncodingTheory.mem_bytes_at_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  drule immutableEncodingProofsTheory.section_fields_cons_valid >>
  strip_tac >> gvs[valueEncodingTheory.val_in_memory_def] >>
  irule immutable_fields_cons_memory_bytes >> conj_tac
  >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem immutable_elems_mask_length[local]:
  !vs tv. LENGTH (FLAT (MAP (immutable_value_mask tv) vs)) =
    LENGTH vs * type_memory_size tv
Proof
  Induct >> simp[arithmeticTheory.MULT_CLAUSES]
QED

Theorem immutable_elems_memory_bytes[local]:
  !vs tv off mem.
    (!v. MEM v vs ==> !base memory.
      val_in_memory tv v base memory ==>
      immutable_value_bytes_rel tv v
        (mem_bytes_at base (type_memory_size tv) memory)) /\
    elems_in_memory vs off tv mem ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (FLAT (MAP (immutable_value_mask tv) vs),
            ZIP (mem_bytes_at off (LENGTH vs * type_memory_size tv) mem,
                 FLAT (MAP (encode_immutable_value tv) vs))))
Proof
  Induct >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  map_every qx_gen_tac [`head`, `tv`, `off`, `mem`] >> strip_tac >>
  qspecl_then [`immutable_value_mask tv head`, `FLAT (MAP (immutable_value_mask tv) vs)`,
               `encode_immutable_value tv head`, `FLAT (MAP (encode_immutable_value tv) vs)`]
    mp_tac immutable_masked_memory_append >>
  simp[immutable_elems_mask_length, immutableEncodingProofsTheory.immutable_flat_map_length] >>
  disch_then (qspec_then `off` (qspec_then `mem` assume_tac)) >>
  gvs[valueEncodingTheory.val_in_memory_def] >>
  simp[arithmeticTheory.MULT_CLAUSES, immutable_value_bytes_rel_def] >>
  qpat_x_assum `!v. v = head \/ _ ==> _` (qspec_then `head` mp_tac) >>
  simp[immutable_value_bytes_rel_def]
QED

Theorem immutable_masked_memory_fit[local]:
  !mask expected cap off mem.
    LENGTH mask = LENGTH expected /\ LENGTH expected <= cap /\
    EVERY (\(used,(actual,want)). used ==> actual = want)
      (ZIP (mask, ZIP (mem_bytes_at off (LENGTH expected) mem, expected))) ==>
    EVERY (\(used,(actual,want)). used ==> actual = want)
      (ZIP (immutable_mask_fit cap mask,
        ZIP (mem_bytes_at off cap mem, immutable_fit cap expected)))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.EVERY_EL, listTheory.EL_ZIP] >>
  rpt strip_tac >>
  Cases_on `n < LENGTH expected` >>
  gvs[immutable_mask_fit_def, immutable_fit_def, listTheory.EL_TAKE,
      listTheory.EL_APPEND_EQN, rich_listTheory.EL_REPLICATE,
      valueEncodingTheory.mem_bytes_at_def, listTheory.EL_ZIP] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem immutable_dynamic_memory_bytes[local]:
  !tv vs cap off mem.
    LENGTH vs <= cap /\
    (!v. MEM v vs ==> !base memory.
      val_in_memory tv v base memory ==>
      immutable_value_bytes_rel tv v
        (mem_bytes_at base (type_memory_size tv) memory)) /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem ==>
    immutable_value_bytes_rel (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (mem_bytes_at off (type_memory_size (ArrayTV tv (Dynamic cap))) mem)
Proof
  rpt gen_tac >> strip_tac >>
  simp[immutable_value_bytes_rel_def, Once immutable_value_mask_def,
       Once encode_immutable_value_def, SF ETA_ss] >>
  irule immutable_masked_memory_fit >>
  simp[immutable_elems_mask_length,
       immutableEncodingProofsTheory.immutable_flat_map_length,
       immutable_word_bytes_def, byteTheory.LENGTH_word_to_bytes,
       valueEncodingTheory.type_memory_size_def] >>
  qspecl_then [`REPLICATE 32 T`, `FLAT (MAP (immutable_value_mask tv) vs)`,
    `immutable_word_bytes (n2w (LENGTH vs))`,
    `FLAT (MAP (encode_immutable_value tv) vs)`]
    mp_tac immutable_masked_memory_append >>
  simp[immutable_elems_mask_length,
       immutableEncodingProofsTheory.immutable_flat_map_length,
       immutable_word_bytes_def, byteTheory.LENGTH_word_to_bytes] >>
  disch_then (qspec_then `off` (qspec_then `mem` assume_tac)) >>
  gvs[valueEncodingTheory.val_in_memory_def] >>
  conj_tac >- (gvs[abi_encoder_word_window] >>
    irule immutable_mask_same_bytes >> simp[byteTheory.LENGTH_word_to_bytes]) >>
  irule immutable_elems_memory_bytes >> simp[]
QED

Theorem immutable_slots_length[local]:
  !n f size. (!i. i < n ==> LENGTH (f i) = size) ==>
    LENGTH (FLAT (GENLIST f n)) = n * size
Proof
  Induct >> simp[listTheory.GENLIST_CONS, arithmeticTheory.MULT_CLAUSES] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem immutable_slots_memory_bytes[local]:
  !n masks bytes stride off mem.
    (!i. i < n ==> LENGTH (masks i) = stride /\ LENGTH (bytes i) = stride /\
      EVERY (\(used,(actual,want)). used ==> actual = want)
        (ZIP (masks i, ZIP (mem_bytes_at (off + i * stride) stride mem, bytes i)))) ==>
    EVERY (\(used,(actual,want)). used ==> actual = want)
      (ZIP (FLAT (GENLIST masks n),
        ZIP (mem_bytes_at off (n * stride) mem, FLAT (GENLIST bytes n))))
Proof
  Induct >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  map_every qx_gen_tac [`masks`, `bytes`, `stride`, `off`, `mem`] >> strip_tac >>
  `LENGTH (masks 0) = stride /\ LENGTH (bytes 0) = stride` by simp[] >>
  `LENGTH (FLAT (GENLIST (masks o SUC) n)) = n * stride /\
   LENGTH (FLAT (GENLIST (bytes o SUC) n)) = n * stride` by
    (conj_tac >> irule immutable_slots_length >> simp[]) >>
  qspecl_then [`masks 0`, `FLAT (GENLIST (masks o SUC) n)`,
    `bytes 0`, `FLAT (GENLIST (bytes o SUC) n)`]
    mp_tac immutable_masked_memory_append >> simp[] >>
  disch_then (qspec_then `off` (qspec_then `mem` assume_tac)) >>
  simp[listTheory.GENLIST_CONS, arithmeticTheory.MULT_CLAUSES] >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `_ <=> _` kall_tac >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[arithmeticTheory.MULT_CLAUSES,
       AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem immutable_default_memory_mask[local]:
  !tv bytes.
    immutable_value_bytes_rel tv (default_value tv) bytes ==>
    EVERY (\(used,(actual,want)). used ==> actual = want)
      (ZIP (immutable_value_mask tv (default_value tv),
        ZIP (bytes, REPLICATE (type_memory_size tv) 0w)))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `tv` immutable_default_zero_bytes) >>
  gvs[immutable_value_bytes_rel_at, listTheory.EVERY_EL, listTheory.EL_ZIP,
      rich_listTheory.EL_REPLICATE] >> metis_tac[]
QED

Theorem immutable_fixed_memory_bytes[local]:
  !tv kvs n off mem.
    (!v base memory.
      (immutable_value_admissible tv v \/ v = default_value tv) /\
      val_in_memory tv v base memory ==>
      immutable_value_bytes_rel tv v (mem_bytes_at base (type_memory_size tv) memory)) /\
    EVERY (\(i,v). immutable_value_admissible tv v) kvs /\
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem ==>
    immutable_value_bytes_rel (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))
      (mem_bytes_at off (type_memory_size (ArrayTV tv (Fixed n))) mem)
Proof
  rpt gen_tac >> strip_tac >>
  simp[immutable_value_bytes_rel_def, Once immutable_value_mask_def,
       Once encode_immutable_value_def, SF ETA_ss] >>
  irule immutable_masked_memory_fit >>
  `LENGTH (FLAT (GENLIST (\i. case ALOOKUP kvs i of
      NONE => REPLICATE (type_memory_size tv) 0w
    | SOME x => encode_immutable_value tv x) n)) = n * type_memory_size tv` by
    (irule immutable_slots_length >> rpt strip_tac >>
     Cases_on `ALOOKUP kvs i` >> simp[]) >>
  `LENGTH (FLAT (GENLIST (\i. immutable_value_mask tv
      (case ALOOKUP kvs i of NONE => default_value tv | SOME x => x)) n)) =
    n * type_memory_size tv` by
    (irule immutable_slots_length >> simp[]) >>
  gvs[valueEncodingTheory.type_memory_size_def, SF ETA_ss] >>
  irule immutable_slots_memory_bytes >> rpt strip_tac >>
  Cases_on `ALOOKUP kvs i` >> gvs[]
  >- (irule immutable_default_memory_mask >> first_x_assum irule >>
      gvs[valueEncodingTheory.val_in_memory_def]) >>
  rename1 `ALOOKUP kvs i = SOME child` >>
  `immutable_value_admissible tv child` by
    (imp_res_tac alistTheory.ALOOKUP_MEM >>
     gvs[listTheory.EVERY_MEM] >>
     first_x_assum (qspec_then `(i,child)` mp_tac) >> simp[]) >>
  `val_in_memory tv child (off + i * type_memory_size tv) mem` by
    (gvs[valueEncodingTheory.val_in_memory_def] >>
     drule_all valueEncodingProofsTheory.kvs_in_memory_lookup >> simp[]) >>
  `immutable_value_bytes_rel tv child
    (mem_bytes_at (off + i * type_memory_size tv) (type_memory_size tv) mem)` by
    (first_x_assum irule >> simp[]) >>
  gvs[immutable_value_bytes_rel_def]
QED

Theorem immutable_memory_bytes_inverse:
  !tv v off mem.
    (immutable_value_admissible tv v \/ v = default_value tv) /\
    val_in_memory tv v off mem ==>
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) mem)
Proof
  measureInduct_on `type_value_size tv` >>
  Cases_on `tv`
  >- (rpt strip_tac >> metis_tac[immutable_base_memory_bytes,
        immutable_base_default_memory_bytes])
  >- (rename1 `TupleTV tvs` >> rpt gen_tac >>
      Cases_on `v` >> simp[Once immutable_value_admissible_def,
        vyperValueTheory.default_value_def,
        vyperValueTheory.default_value_tuple_MAP] >> rename1 `ArrayV av` >>
      Cases_on `av` >> simp[Once immutable_value_admissible_def] >>
      disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
      simp[immutable_value_bytes_rel_def, Once immutable_value_mask_def,
           Once encode_immutable_value_def, valueEncodingTheory.type_memory_size_def] >>
      irule immutable_masked_memory_fit >>
      simp[immutableEncodingProofsTheory.section_tuple_mask_length,
        immutableEncodingProofsTheory.immutable_tuple_length] >>
      irule immutable_tuple_memory_bytes >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
          `type_value_size tv < list_size type_value_size tvs + 1` by
            (qpat_x_assum `MEM tv tvs` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> Induct_on `tvs` >>
             simp[listTheory.list_size_def] >> rpt strip_tac >> gvs[] >>
             decide_tac) >> simp[]) >>
      gvs[valueEncodingTheory.val_in_memory_def])
  >- (rename1 `ArrayTV et bound` >>
      `!v off mem. (immutable_value_admissible et v \/ v = default_value et) /\
         val_in_memory et v off mem ==>
         immutable_value_bytes_rel et v (mem_bytes_at off (type_memory_size et) mem)` by
        (rpt strip_tac >> first_x_assum irule >>
         simp[vyperValueTheory.type_value_size_def] >> metis_tac[]) >>
      rpt gen_tac >> Cases_on `bound` >> Cases_on `v` >>
      simp[Once immutable_value_admissible_def, vyperValueTheory.default_value_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[Once immutable_value_admissible_def] >> strip_tac
      >- (irule immutable_fixed_memory_bytes >> conj_tac
          >- metis_tac[] >> simp[] >>
          gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
          PairCases_on `e` >> first_x_assum drule >> simp[])
      >- (irule immutable_fixed_memory_bytes >> simp[] >> metis_tac[])
      >- (irule immutable_dynamic_memory_bytes >> simp[] >>
          gvs[listTheory.EVERY_MEM] >> metis_tac[])
      >> (irule immutable_dynamic_memory_bytes >> simp[] >>
          gvs[valueEncodingTheory.val_in_memory_def]))
  >- (rename1 `StructTV fields` >> rpt gen_tac >>
      Cases_on `v` >> simp[Once immutable_value_admissible_def,
        vyperValueTheory.default_value_def,
        vyperValueTheory.default_value_struct_MAP] >>
      disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
      simp[immutable_value_bytes_rel_def, Once immutable_value_mask_def,
           Once encode_immutable_value_def, valueEncodingTheory.type_memory_size_def] >>
      irule immutable_masked_memory_fit >>
      simp[immutableEncodingProofsTheory.section_fields_mask_length,
        immutableEncodingProofsTheory.immutable_fields_length] >>
      irule immutable_fields_memory_bytes >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
          `type_value_size tv <
            list_size (pair_size (list_size char_size) type_value_size) fields + 1` by
            (qpat_x_assum `MEM tv (MAP SND fields)` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> Induct_on `fields` >>
             simp[listTheory.list_size_def] >>
             qx_gen_tac `entry` >> PairCases_on `entry` >>
             simp[basicSizeTheory.pair_size_def] >> rpt strip_tac >> gvs[] >>
             decide_tac) >> simp[]) >>
      gvs[valueEncodingTheory.val_in_memory_def])
  >- (rpt gen_tac >> strip_tac >> irule immutable_flag_memory_bytes >>
      gvs[vyperValueTheory.default_value_def, immutable_value_admissible_def])
  >> rpt gen_tac >> strip_tac >> irule immutable_none_memory_bytes >>
  gvs[vyperValueTheory.default_value_def, immutable_value_admissible_def]
QED

Theorem immutable_admissible_memory_bytes:
  !tv v off mem.
    immutable_value_admissible tv v /\ val_in_memory tv v off mem ==>
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) mem)
Proof
  metis_tac[immutable_memory_bytes_inverse]
QED

(* A default dynamic array cannot supply a nonempty pop, even through a path. *)
Theorem immutable_default_dynamic_pop_empty:
  !tv cap path vs.
    evaluate_subscripts (ArrayTV tv (Dynamic cap))
      (default_value (ArrayTV tv (Dynamic cap))) path =
        INL (ArrayV (DynArrayV vs)) ==> vs = []
Proof
  rpt gen_tac >> Cases_on `path`
  >- simp[vyperValueTheory.default_value_def, evaluate_subscripts_def] >>
  Cases_on `h` >> simp[vyperValueTheory.default_value_def]
  >- (rename1 `ValueSubscript idx` >> Cases_on `idx` >>
      simp[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
           listTheory.oEL_def] >> Cases_on `0 <= i` >> simp[]) >>
  simp[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
       listTheory.oEL_def] >>
  Cases_on `0 <= i` >> simp[]
QED

(* RESIDUAL, FALSE as stated until ImmutablePlace reads get a popped
   history as MemoryPlace's have (the semantics ledger item shared with
   the array piece's ancestor-pop residual): a nested pop on an immutable
   in the constructor with an index that pops or calls.  Such an index
   can shorten an array on the target's own path after the lowering has
   taken its pointer.  The source's extend_place re-reads the whole path,
   and read_place on an ImmutablePlace has no popped history, so it
   fails; the lowering reads the stale length word and goes on.
   Counterexample: s.a : DynArray[DynArray[DynArray[uint256,3],3],3] =
   [[[7]],[[8]]], target self.s.a[1][len(self.s.a.pop()) - 1], popped.
   The base place s.a[1] is in bounds; the index pops s.a to length 1 and
   gives 0; extend_place reads s.a[1], out of bounds: RuntimeError.  The
   lowering took a[1]'s pointer before the index, a[1]'s length word
   still reads 1, 0 < 1, and the outer pop completes.  An internal call
   in the index can do the same in the constructor (functions_well_typed
   types callee bodies with bare_global_assignable_complete). *)
Theorem pop_nested_immutable_deploy_impure_index_case:
  !ctx func cenv cx env ann bt ty es src id.
    cx.in_deploy /\
    ~EVERY pure_expr (target_indices bt) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* The writable-place interface supplies the mutable path; the immutable
   representation supplies root well-formedness, including sparse arrays. *)
Theorem imm_place_pop_memory:
  !ctx func cenv cx env es s src id path w ann etv n vs.
    cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
    stmt_state_rel ctx func cenv cx es s /\
    imm_place_at cenv cx es (PlaceR (ImmutablePlace src id path)) w
      (ArrayT ann (Dynamic n)) /\
    writable_place_result cx es (PlaceR (ImmutablePlace src id path)) /\
    evaluate_type (get_tenv cx) ann = SOME etv /\
    read_place cx (ImmutablePlace src id path) es =
      (INL (ArrayV (DynArrayV vs)),es) ==>
    ?off itv iv k.
      w = n2w (off + k) /\
      FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      off + type_memory_size itv < dimword (:256) /\
      mem_path_offset itv path = SOME (k,ArrayTV etv (Dynamic n)) /\
      evaluate_subscripts itv iv path = INL (ArrayV (DynArrayV vs)) /\
      mutable_place_path itv path /\ value_has_type itv iv /\
      well_formed_type_value itv /\ val_wf itv iv /\
      val_in_memory itv iv off s.vs_memory /\
      type_memory_bytes cenv ann = type_memory_size etv /\
      k + 32 <= type_memory_size itv /\
      (vs <> [] ==>
        val_in_memory etv (LAST vs)
          (off + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
          (mstore (off + k) (n2w (LENGTH vs - 1)) s).vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[imm_place_at_def, vyperValueTheory.evaluate_type_def] >>
  `v = ArrayV (DynArrayV vs)` by
    (Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     gvs[read_place_def, get_immutables_def, get_address_immutables_def,
         vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, vyperStateTheory.lift_sum_def,
         vyperStateTheory.lift_option_type_def, AllCaseEqs()]) >>
  gvs[] >>
  `mutable_place_path itv path` by
    (Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     gvs[vyperTargetPlaceWriteTheory.writable_place_result_def,
         vyperPlaceWriteSoundnessTheory.runtime_place_writable_def,
         get_immutables_def, get_address_immutables_def,
         vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, AllCaseEqs()]) >>
  `value_has_type itv iv /\ well_formed_type_value itv` by
    (irule imm_place_at_value_type >> goal_assum (drule_at Any) >>
     qexistsl [`cenv`, `env`, `0`, `[]`] >>
     simp[mem_path_offset_def, evaluate_subscripts_def]) >>
  `immutable_value_admissible itv iv /\ val_in_memory itv iv off s.vs_memory` by
    (gvs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
     first_x_assum drule_all >> simp[]) >>
  `val_wf itv iv` by
    metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
  qexistsl [`itv`, `iv`, `k`] >> simp[] >>
  conj_tac
  >- metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  conj_tac
  >- (drule exprSimPropsTheory.mem_path_offset_sound >>
      simp[valueEncodingTheory.type_memory_size_def]) >>
  strip_tac >>
  drule_all exprSimPopNestedLocalMemoryTheory.pop_path_elem_in_memory >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
                    arithmeticTheory.MULT_COMM]
QED

Theorem immutable_default_path_pop_empty:
  !path tv vs.
    mutable_place_path tv path /\
    evaluate_subscripts tv (default_value tv) path = INL (ArrayV (DynArrayV vs)) ==>
    vs = []
Proof
  Induct_on `path`
  >- (Cases_on `tv` >>
      simp[evaluate_subscripts_def, vyperValueTheory.default_value_def,
           vyperValueTheory.default_value_tuple_MAP,
           vyperValueTheory.default_value_struct_MAP] >>
      TRY (rename1 `BaseTV bt` >> Cases_on `bt` >>
           simp[vyperValueTheory.default_value_def] >>
           rename1 `BytesT bd` >> Cases_on `bd` >>
           simp[vyperValueTheory.default_value_def] >> NO_TAC) >>
      Cases_on `b` >> simp[vyperValueTheory.default_value_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def] >>
      rename1 `ArrayTV ct bd` >> Cases_on `bd` >>
      gvs[vyperValueTheory.default_value_def, evaluate_subscripts_def,
          vyperValueOperationTheory.array_index_def, listTheory.oEL_def,
          AllCaseEqs()] >>
      first_x_assum drule_all >> simp[]) >>
  Cases_on `tv` >>
  gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def, AllCaseEqs()] >>
  Cases_on `ALOOKUP l s` >> gvs[] >>
  gvs[vyperValueTheory.default_value_def,
      vyperValueTheory.default_value_struct_MAP, evaluate_subscripts_def,
      alistTheory.ALOOKUP_MAP, AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

(* Diagnostic: insert_sarray's early insertion needs ordered keys, not
   merely distinct keys. This is a probe of the proposed helper interface. *)
Theorem immutable_sparse_insert_order_diagnostic[local]:
  ALL_DISTINCT (MAP FST [(2,IntV 0); (1,IntV 0)]) /\
  ~ALL_DISTINCT
    (MAP FST (insert_sarray 1 (IntV 1) [(2,IntV 0); (1,IntV 0)]))
Proof
  EVAL_TAC
QED

Theorem immutable_fields_admissible_update[local]:
  !fs vals id ct child.
    immutable_fields_admissible fs vals /\ ALOOKUP fs id = SOME ct /\
    immutable_value_admissible ct child ==>
    immutable_fields_admissible fs (AFUPDKEY id (K child) vals)
Proof
  Induct_on `fs` >- simp[immutable_value_admissible_def] >>
  Cases >> Cases_on `vals` >> simp[immutable_value_admissible_def] >>
  PairCases_on `h` >>
  simp[immutable_value_admissible_def, alistTheory.AFUPDKEY_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[immutable_value_admissible_def]
QED

Theorem immutable_sparse_entries_insert[local]:
  !al i child ct n.
    EVERY (\(j,x). j < n /\ immutable_value_admissible ct x) al /\
    i < n /\ immutable_value_admissible ct child ==>
    EVERY (\(j,x). j < n /\ immutable_value_admissible ct x)
      (insert_sarray i child al)
Proof
  Induct_on `al` >- simp[vyperValueOperationTheory.insert_sarray_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  simp[Once vyperValueOperationTheory.insert_sarray_def] >>
  rpt (IF_CASES_TAC >> gvs[])
QED

Theorem immutable_sparse_admissible_insert[local]:
  !al i child ct n.
    SORTED $< (MAP FST al) /\
    immutable_value_admissible (ArrayTV ct (Fixed n)) (ArrayV (SArrayV al)) /\
    i < n /\ immutable_value_admissible ct child ==>
    immutable_value_admissible (ArrayTV ct (Fixed n))
      (ArrayV (SArrayV (insert_sarray i child al)))
Proof
  rpt strip_tac >> simp[immutable_value_admissible_def] >> conj_tac
  >- (irule vyperTypingTheory.SORTED_lt_ALL_DISTINCT >>
      irule vyperAssignPreservesTypeTheory.insert_sarray_SORTED >> simp[]) >>
  irule immutable_sparse_entries_insert >>
  gvs[immutable_value_admissible_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem immutable_sparse_admissible_delete[local]:
  !al i ct n.
    SORTED $< (MAP FST al) /\
    immutable_value_admissible (ArrayTV ct (Fixed n)) (ArrayV (SArrayV al)) ==>
    immutable_value_admissible (ArrayTV ct (Fixed n))
      (ArrayV (SArrayV (ADELKEY i al)))
Proof
  rpt strip_tac >> simp[immutable_value_admissible_def] >> conj_tac
  >- (irule vyperTypingTheory.SORTED_lt_ALL_DISTINCT >>
      irule vyperAssignPreservesTypeTheory.ADELKEY_SORTED >> simp[]) >>
  gvs[immutable_value_admissible_def, alistTheory.ADELKEY_def,
      listTheory.EVERY_MEM, listTheory.MEM_FILTER] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem immutable_fields_admissible_lookup[local]:
  !fs vals id ct v.
    immutable_fields_admissible fs vals /\ ALOOKUP fs id = SOME ct /\
    ALOOKUP vals id = SOME v ==> immutable_value_admissible ct v
Proof
  Induct_on `fs` >- simp[immutable_value_admissible_def] >>
  Cases >> Cases_on `vals` >> simp[immutable_value_admissible_def] >>
  PairCases_on `h` >> simp[immutable_value_admissible_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem immutable_pop_path_admissible:
  !path tv a etv n vs updated.
    mutable_place_path tv path /\ value_has_type tv a /\
    immutable_value_admissible tv a /\
    subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) =
      INL updated ==>
    immutable_value_admissible tv updated
Proof
  Induct_on `path`
  >- (rpt strip_tac >>
      gvs[subscripts_type_def, evaluate_subscripts_def, assign_subscripts_def,
          immutable_value_admissible_def] >>
      simp[rich_listTheory.LENGTH_FRONT] >>
      simp[rich_listTheory.FRONT_BY_TAKE, rich_listTheory.EVERY_TAKE]) >>
  rpt gen_tac >> strip_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def] >>
      rename1 `ArrayTV ct bd` >>
      Cases_on `a` >> gvs[vyperTypingTheory.value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[vyperTypingTheory.value_has_type_def]
      >- suspend "sparse"
      >> suspend "dynamic") >>
  Cases_on `tv` >>
  gvs[vyperPlaceWriteSoundnessTheory.mutable_place_path_def] >>
  Cases_on `a` >> gvs[vyperTypingTheory.value_has_type_def] >>
  suspend "struct"
QED

Resume immutable_pop_path_admissible[sparse]:
  rpt strip_tac >> Cases_on `bd` >>
  gvs[immutable_value_admissible_def, vyperTypingTheory.value_has_type_def,
      subscripts_type_def, subscript_type_def, evaluate_subscripts_def,
      assign_subscripts_def, vyperValueOperationTheory.array_index_def,
      AllCaseEqs()] >>
  `value_has_type ct v` by
    (gvs[vyperTypingTheory.all_have_type_EVERY, listTheory.oEL_THM,
         AllCaseEqs()] >> metis_tac[listTheory.EVERY_EL]) >>
  `immutable_value_admissible ct v` by
    (gvs[listTheory.oEL_THM, AllCaseEqs()] >>
     metis_tac[listTheory.EVERY_EL]) >>
  `immutable_value_admissible ct vj` by
    (first_x_assum drule_all >> simp[]) >>
  gvs[vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >>
  simp[immutable_value_admissible_def, listTheory.IMP_EVERY_LUPDATE,
       rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Resume immutable_pop_path_admissible[dynamic]:
  Cases_on `bd` >>
  gvs[vyperTypingTheory.value_has_type_def,
      subscripts_type_def, subscript_type_def, evaluate_subscripts_def,
      assign_subscripts_def, vyperValueOperationTheory.array_index_def,
      AllCaseEqs()]
  >- (drule_all immutable_default_path_pop_empty >> simp[]) >>
  `value_has_type ct v` by
    (drule_all vyperAssignPreservesTypeTheory.ALOOKUP_sparse_has_type >> simp[]) >>
  `immutable_value_admissible ct v` by
    (gvs[immutable_value_admissible_def, listTheory.EVERY_MEM] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `immutable_value_admissible ct vj` by
    (first_x_assum drule_all >> simp[]) >>
  gvs[vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >>
  IF_CASES_TAC
  >- (irule immutable_sparse_admissible_delete >> simp[]) >>
  irule immutable_sparse_admissible_insert >> simp[]
QED

Resume immutable_pop_path_admissible[struct]:
  gvs[subscripts_type_def, subscript_type_def, evaluate_subscripts_def,
      assign_subscripts_def, AllCaseEqs()] >>
  `value_has_type etv' v` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  `immutable_fields_admissible l l'` by
    gvs[immutable_value_admissible_def] >>
  `immutable_value_admissible etv' v` by
    (drule_all immutable_fields_admissible_lookup >> simp[]) >>
  `immutable_value_admissible etv' v'` by
    (first_x_assum drule_all >> simp[]) >>
  simp[immutable_value_admissible_def] >>
  irule immutable_fields_admissible_update >> goal_assum (drule_at Any) >> simp[]
QED

Finalise immutable_pop_path_admissible

(* A nested pop changes the represented root only at its length word. *)
Theorem immutable_pop_path_bytes:
  !path tv a base k etv n vs updated s.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ immutable_value_admissible tv a /\
    val_in_memory tv a base s.vs_memory /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) =
      INL updated ==>
    immutable_value_bytes_rel tv updated
      (mem_bytes_at base (type_memory_size tv)
        (mstore (base + k) (n2w (LENGTH vs - 1)) s).vs_memory)
Proof
  rpt strip_tac >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `val_wf tv a` by
    metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
  `immutable_value_admissible tv updated` by
    (drule_all immutable_pop_path_admissible >> simp[]) >>
  irule immutable_admissible_memory_bytes >> simp[] >>
  drule_all exprSimPopNestedLocalMemoryTheory.val_in_memory_pop_path >> simp[]
QED
