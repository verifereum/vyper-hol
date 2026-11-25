(* Restore the qualified observation at the popped endpoint, while keeping
   the original immutable address and capture certificate fixed. *)
Theory bodyForArrayImmutableRestoreMods
Ancestors
  bodyForArraySavedFrameMods bodyForArrayEntryMods vyperTypeValues
  bodyFullPostsMods bodyFullPredsMods vyperBareGlobalName vyperState
  vyperValueOperation ptrDiscipline words finite_map list
Libs
  horizonTypeLib

val _ = Parse.hide "body";

Theorem for_array_immutable_restore_mods:
  for_array_entry_route_mods c cx lo (sty,bd,LocCode) (em,sbExpr,u,Gu,tu)
    (op,bw) vs (ForArrayImmutable src name path off itv delta av) h (a::rs) es G tn s /\
  path = MAP AttrSubscript attrs ++ tail /\
  (?old. lookup_immutable cx es src name = SOME (itv,old) /\
         evaluate_subscripts itv old (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
         evaluate_subscripts itv old path = INL (ArrayV av)) /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  loop_iterator_place e = SOME p /\
  place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
  iterator_unmodified (Array e) body /\
  stmt_loop_calls_ok mods (For id fty (Array e) bound body) /\
  off + type_memory_size itv < dimword (:256) /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
  push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  ee = fin with scopes := TL fin.scopes /\
  copy_old_operand saL op /\
  (!lbl. op <> Label lbl) /\
  (!q. not_fresh_at saL q ==>
       FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) /\
  for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) ee tn1 t /\
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env ee /\
  dead_lo_ok_mods H D lo c cx /\ ghost_inv_at_mods D lo d c cx ee G1 tn1 t /\
  immutable_frame_mods func c cx ee t ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocCode) (em,sbExpr,u,Gu,tu)
    (op,bw) vs (ForArrayImmutable src name path off itv delta av) H rs ee G1 tn1 t /\
  (?now. lookup_immutable cx ee src name = SOME (itv,now) /\
         evaluate_subscripts itv now (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
         evaluate_subscripts itv now path = INL (ArrayV av))
Proof
  strip_tac >>
  qpat_x_assum `path = _` SUBST_ALL_TAC >>
  `evaluate_type (get_tenv cx) sty = SOME tv` by
    (drule evaluate_type_ArrayT_cases >> simp[]) >>
  qpat_assum `evaluate_type _ sty = SOME tv` (fn th =>
    qhdtm_x_assum `for_array_entry_route_mods`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [for_array_entry_route_mods_def,th])) >>
  `lookup_immutable cx (es with gas_obs := []) src name = SOME (itv,old)` by
    (qpat_assum `lookup_immutable cx es src name = SOME (itv,old)` mp_tac >>
     simp[NoAsms,lookup_immutable_def]) >>
  drule_all_then strip_assume_tac
    (REWRITE_RULE [] (Q.INST [`st` |-> `eb with gas_obs := gs`, `obs` |-> `gs`]
       (horizonTypeLib.at_horizon_named "H" for_array_saved_after_body_mods))) >>
  qpat_x_assum `!tv. eval_operand _ _ = _ /\ _`
    (qspec_then `tv` strip_assume_tac) >>
  first_assum (drule_at (Pat `loop_iterator_place _ = SOME _`)) >>
  disch_then (drule_all_then strip_assume_tac) >>
  rename1 `lookup_immutable cx ee src name = SOME (itv,new_root)` >>
  reverse conj_tac >- (qexists_tac `new_root` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac [for_array_entry_route_mods_def,for_array_capture_case_def,
                    REFL_CLAUSE,AND_CLAUSES] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  qexists_tac `tv` >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rename1 `lookup_immutable cx em src name = SOME (itv,captured_root)` >>
      qexists_tac `captured_root` >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `new_root` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `op_prov G1 op = NONE` by simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
