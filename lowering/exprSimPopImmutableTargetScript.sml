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
