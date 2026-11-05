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
 *   body_pop_nested_immutable_module_case — RESIDUAL (may be false): the
 *                           same for another module.
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
  compileVyper vyperTypeInvariants vyperTypeContract vyperPureExpr
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

(* RESIDUAL (may be false as stated until body_inv records
   cenv.ce_module = NONE, which build_compile_env sets): a nested pop on
   an immutable in the constructor, in a body whose compile env names
   another module.  body_inv gives ce_module_var_type only at
   (NONE,id), and expr_sim_inv puts the immutable at ce_module, so
   pop_nested_sim's root-type premise does not follow. *)
Theorem body_pop_nested_immutable_module_case:
  !cx bt tops ctx func cenv env ann ty es.
    body_inv tops ctx cenv cx /\ body_base_target_ok cx bt /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    immutable_root cx bt /\ cx.in_deploy /\ cenv.ce_module <> NONE ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
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

(* The counted walk of a target rooted at an immutable in the
   constructor, with pure indices, given their judgments, the
   constructor's compile env and the root's declared type in it: from s0
   related at es, the target's fragment ends at the place's pointer
   (imm_target_post), the source state unchanged, or exits as the source
   does.  Admitted pending alan; provable as stated, no invariant change
   needed. *)
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
  cheat
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
