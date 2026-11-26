(* Restore the same named memory path after popping the body scope. *)
Theory bodyForArrayHeldRestoreMods
Ancestors
  bodyForArraySavedFrameMods bodyForArrayOriginMods
  bodyForArrayHeaderMods bodyForArrayEntryMods
  exprBodyPreProps vyperTypeSystem vyperTypeInvariants vyperInterpreter
  vyperState loweringStateRelDefs finite_map words

val _ = Parse.hide "body";

Theorem for_array_held_restore_mods:
  for_array_header_mods mods DF lo d ctx func c cx env id st0 outer
    (em,sbExpr,saL,u,tu) (xd,dw,cap,aid) vs (op,bw,len_op,idx)
    cond Route H rs es G tn s /\
  for_array_observation_mods c cx lo (sty,bd,LocMemory)
    (em,sbExpr,u,Gu,tu) (op,bw) vs
    ((em,u,Gu,tu,dw,bw,ForArrayHeld name (MAP AttrSubscript attrs ++ tail) av),
     SOME av) H rs es G tn s /\
  place_access p [] = (NameTarget name,attrs) /\ MEM p (expr_places e) /\
  well_typed_expr (extend_local env id fty F) e /\ expr_type e = ArrayT sty bd /\
  type_stmts (extend_local env id fty F) ret_ty body = SOME env' /\
  iterator_unmodified (Array e) body /\
  lookup_scopes name es.scopes = SOME old /\
  evaluate_subscripts old.type old.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
  FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
  not_fresh_at saL root /\ lookup_var root u = SOME rw /\
  bw = rw + n2w delta /\ w2n rw + delta < dimword (:256) /\
  mem_path_offset old.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv bd) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  w2n rw <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= w2n rw + sz /\
  copy_old_operand saL op /\ (!lbl. op <> Label lbl) /\
  push_scope_with_var id dtv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (res,fin) /\
  ee = fin with scopes := TL fin.scopes /\
  for_array_header_mods mods DF lo d ctx func c cx env id st0 outer
    (em,sbExpr,saL,u,tu) (xd,dw,cap,aid) vs (op,bw,len_op,idx)
    cond (\_ _ _ _ _ _. T) hor rest ee G1 tn1 f /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  for_array_observation_mods c cx lo (sty,bd,LocMemory)
    (em,sbExpr,u,Gu,tu) (op,bw) vs
    ((em,u,Gu,tu,dw,bw,ForArrayHeld name (MAP AttrSubscript attrs ++ tail) av),
     SOME av) hor rest ee G1 tn1 f /\
  lookup_var root f = SOME rw /\ ptr_covers G1 tn1 root f sz /\
  (?entry. lookup_scopes name ee.scopes = SOME entry /\ entry.type = old.type /\
    mem_path_offset entry.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv bd) /\
    evaluate_subscripts entry.type entry.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av))
Proof
  PairCases_on `outer` >> strip_tac >>
  qhdtm_x_assum `for_array_observation_mods` (mp_tac) >>
  simp[for_array_observation_mods_def, for_array_entry_route_mods_def,
       for_array_memory_backing_mods_def] >> strip_tac >>
  qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ es G tn s`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee G1 tn1 f`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  `name <> id` by (strip_tac >> gvs[]) >>
  `name IN FDOM (extend_local env id fty F).var_types` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ es`
       (mp_tac o MATCH_MP expr_sim_inv_mods_env) >>
     simp[env_consistent_def,env_scopes_consistent_def,extend_local_def] >>
     disch_then (CONJUNCTS_THEN strip_assume_tac) >>
     qpat_assum `!n entry. lookup_scopes n es.scopes = SOME entry ==> _`
       (qspecl_then [`name`,`old`] mp_tac) >>
     simp[] >> Cases_on `name IN FDOM env.var_types` >> gs[FLOOKUP_DEF]) >>
  `lookup_scopes name (es with gas_obs := []).scopes = SOME old` by simp[] >>
  `eval_operand op u = SOME bw` by simp[] >>
  drule for_array_saved_after_body_mods >>
  disch_then (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
  disch_then (drule_at (Pat `for_array_capture_frame_mods _ _ ee tn1 f`)) >>
  disch_then (drule_at (Pat `eval_operand op u = SOME bw`)) >>
  disch_then (qspecl_then [`tv`,`tn`,`gs`,`G`,`G1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC ORELSE simp[])) >>
  strip_tac >>
  qpat_x_assum `!name attrs p tail old root sz rw delta av e et bd benv ev ret mods env D lo d.
    _ ==> read_result _ (PlaceR (MemoryPlace _ _)) _ = _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `ee = _` SUBST_ALL_TAC >>
  qpat_x_assum `bw = _` SUBST_ALL_TAC >>
  qpat_x_assum `lookup_scopes name (_ with scopes := _).scopes = SOME _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  simp[] >>
  conj_tac
  >- (strip_tac >> qexistsl_tac [`w2n rw`,`sz`] >> simp[local_region_def]) >>
  qpat_assum `old.type = old'.type` (once_rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED
