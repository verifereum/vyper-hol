(*
 * The cases of target_subscript_case (targetSubscriptCase), by the
 * target's root and its indices.
 *
 * TOP-LEVEL:
 *   target_subscript_main_case — a local root whose indices pop nothing,
 *                          or a storage root whose indices are all pure
 *   target_subscript_storage_effectful_case — RESIDUAL: a storage root
 *                          with an index that calls or pops
 *   target_subscript_local_pop_case — RESIDUAL: a local root with an index
 *                          that pops
 *)

Theory targetSubscriptSplit
Ancestors
  targetPlaceLive
  targetPlaceSimCasesBase
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps gasSummary gasSummaryCompose gasContext gasExemptCert
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim supportedExprTraverse
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc vyperPureExpr
  venomState venomInst
Libs
  pairLib

Theorem target_subscript_base_exempt_cert:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx bt) (return ()))
    (es, s0) marks (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx (SubscriptTarget bt e)) (return ()))
    (es, s0) marks (err, ee) (leaf, sf)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem target_subscript_index_exempt_cert:
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) left (INL pv) mid (OK t) /\
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (mid with gas_obs := [], t) right (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx (SubscriptTarget bt e)) (return ()))
    (es, s0) (left ++ right) (err, ee) (leaf, sf)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[ignore_bind_def, bind_assoc]
QED

(* Full-target admissibility projects to the base: every base exception
   propagates unchanged, and every base success is in target_res_ok. *)
Theorem target_subscript_base_admissible:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e))
    target_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[target_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  once_rewrite_tac[evaluate_def] >> simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> simp[]
QED

Theorem target_subscript_index_admissible:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e))
    target_res_ok es /\
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) marks (INL pv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  once_rewrite_tac[evaluate_def] >>
  rewrite_tac[GSYM bind_assoc] >> simp[] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >>
  gvs[bind_def, target_res_ok_def, expr_res_ok_def]
QED

(* Internal-call defaults and bodies are bracketed by scope restoration,
   even on exceptions; this boundary requires no invariant on the callee. *)
Theorem target_subscript_restore_scopes:
  finally source (set_scopes prev) es = (res, ee) ==>
  ee.scopes = prev
Proof
  simp[finally_def, bind_def, ignore_bind_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

(* A failed base consumes exactly the same marked path in the full target;
   no index or pointer suffix is evaluated. *)
Theorem target_subscript_base_exception:
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) marks (INR exc) fin r ==>
  gas_marked_exec memory (ctx, func)
    (eval_base_place cx (SubscriptTarget bt e))
    (es, s0) marks (INR exc) fin r
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

(* An element of an array or a mapping, when no index can shrink an array
   the place is already in: the base's fragment, the index's (lower_value),
   then, by the base's place type, the slot of the key
   (compile_mapping_subscript, with compile_keccak256_key for a bytes or
   string key) or the bounds check and the element's pointer
   (compile_array_subscript).  What it takes:
   - the index runs after the base, so the base's target_post must survive
     its fragment: place_ptr_rel does (place_ptr_rel_vars_frame: the local
     pointers and the base's operand are not fresh at the index's start);
     place_readable does too, as without a pop the index leaves the source
     locals as they were (a call restores the caller's scopes);
   - for a storage root, every index is pure, so the source state is the
     one the target started from, and the base's place is read live
     (targetPlaceLive's nested_pop_eval_base_live), so the header the
     bounds check loads is one stmt_state_rel relates;
   - the bounds check: a source RuntimeError for an index out of range
     (evaluate_subscripts array_index for a local's place,
     resolve_array_element's checks for a storage one) against
     compile_array_subscript's ASSERT, which aborts, and an index in range
     against the length the loader reads (an MLOAD at the base's pointer,
     an SLOAD or TLOAD at its slot);
   - the mapping slot: compile_mapping_subscript's SHA3 over the slot and
     key words in a fresh 64-byte buffer against hashmap_slot slot
     (encode_hashmap_key kt kv).
   Given those, the element's place is at the base's pointer plus the
   element's offset (mem_step_offset) for a local, and at the element's
   slot for storage. *)
Theorem target_subscript_main_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    (!nsid. target_root bt = TopLevelNameTarget nsid ==>
            EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
    (!id. target_root bt = NameTarget id ==>
          ~supported_target_exists (\x. ?ty t. x = Pop ty t)
             (SubscriptTarget bt e)) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED

(* RESIDUAL (effectful storage indices): an index that calls or pops can
   shrink an array the target already points into (outer[0][shrink()] = v,
   or with the call in an index of the base), so the header the bounds
   check reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage (storage_dead).  Needs raw
   agreement on slots made dead by a write; exprSimPopNestedStorageEffectful's
   pop_nested_storage_effectful_sim has the same exposure.  The root is any
   module name, so this also covers an immutable's member in the
   constructor, which a call in an index can pop (es.immutables is
   module-wide; a call restores only the scopes); target_pre excludes such
   a root (immutable_root), so its pure case needs nothing. *)
Theorem target_subscript_storage_effectful_case:
  !nocalls ctx func cenv cx bt e nsid.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    target_root bt = TopLevelNameTarget nsid /\
    ~EVERY pure_expr (target_indices (SubscriptTarget bt e)) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED

(* RESIDUAL (a pop in a local target's index): the pop can pop an ancestor
   of the base (x[0][len(x.pop()) - 1] = v).  The compiled pointer then
   points at memory the pop left in place, and the source reads the base
   through read_memory_path's popped history, but no invariant relates the
   popped history to memory yet.  exprSimPopNested's pop_nested_local_sim
   is of the same family. *)
Theorem target_subscript_local_pop_case:
  !nocalls ctx func cenv cx bt e id.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    target_root bt = NameTarget id /\
    supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED
