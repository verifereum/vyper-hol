(* Replay the selected internal defaults at the post-argument empty scope. *)
Theory bodyIntCallDefaultBracketMods
Ancestors
  bodySelectedLockedCellsMods bodyFullPreds bodyFullPredsMods linkedRuntimeDefaultReplay
  constSubstCorrect constSubstStmts constSubstMods vyperTypeSystem vyperTypeContract
  vyperTypeContractContext vyperTypeContractStaticMaps vyperInterpreter vyperState
  finite_map alist list rich_list

Triviality drop_subst_defaults_mods:
  !n dflts. DROP n (subst_consts_exprs_mods E dflts) =
            subst_consts_exprs_mods E (DROP n dflts)
Proof
  Induct >> simp[] >> Cases >> simp[subst_consts_expr_mods_def]
QED

Triviality selected_defaults_checked:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  frame_maps env art /\
  well_typed_expr env (Call ty (IntCall (src,fn)) es dflt) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  (vis = Deploy ==> cx.in_deploy) ==>
  check_function_body cx.layouts cx.txn.target mods art src vis mut nr args dflts ret ss
Proof
  strip_tac >> irule check_contract_function_body_MEM >>
  conj_tac
  >- (qexists_tac `cx.in_deploy` >> simp[check_function_body_in_mode_def]) >>
  qexistsl_tac [`fn`, `raw`, `tops`] >> simp[] >>
  qpat_x_assum `well_typed_expr _ _`
    (strip_assume_tac o PURE_ONCE_REWRITE_RULE [well_typed_expr_def]) >>
  drule check_contract_artifact_fields >> strip_tac >>
  gvs[frame_maps_def, FLOOKUP_DRESTRICT_SOME]
QED

Theorem selected_defaults_bracket_mods:
  body_const_cells_agree mods cx env st /\
  well_typed_expr env (Call ty (IntCall (src,fn)) es dflt) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  (vis = Deploy ==> cx.in_deploy) /\
  eval_exprs cx es st = (INL vs,st') ==>
  let p = cx with stk updated_by CONS (src,fn) in
  let n = LENGTH dflts - (LENGTH args - LENGTH es) in
    finally
      (ignore_bind (set_scopes [FEMPTY])
        (eval_exprs p (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))))
      (set_scopes st'.scopes) st' =
    finally
      (ignore_bind (set_scopes [FEMPTY]) (eval_exprs p (DROP n dflts)))
      (set_scopes st'.scopes) st'
Proof
  strip_tac >> simp[LET_THM, drop_subst_defaults_mods] >>
  qmatch_goalsub_abbrev_tac `eval_exprs p (DROP n _)` >>
  `?art. check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
         frame_maps env art /\ env.type_defs = get_tenv cx` by
    (qpat_assum `body_const_cells_agree _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
     qexists_tac `art` >> simp[]) >>
  rename1 `frame_maps env art` >>
  drule_all selected_defaults_checked >> strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_runtime_namespaces >> simp[contract_namespaces_ok_def]) >>
  qabbrev_tac `entry = function_entry_env art mods src vis args` >>
  `body_const_cells_agree mods p entry st` by
    (simp[Abbr `p`, Abbr `entry`] >> irule selected_locked_const_cells_mods >>
     simp[] >> qexistsl_tac [`st`, `mut`, `F`, `env`] >>
     simp[lock_if_nr_def, return_def]) >>
  qpat_x_assum `body_const_cells_agree mods p entry st`
    (qx_choosel_then [`roots`, `art'`, `imms`] strip_assume_tac o
      PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
  `art' = art` by gvs[Abbr `p`] >>
  qpat_x_assum `art' = art` SUBST_ALL_TAC >>
  `const_subst_context roots cx env [] mods art` by
    (simp[const_subst_context_def, ALOOKUP_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!addr src id tv root. MEM _ roots ==> checked_frame_context p _ _ _ _ _`
       (drule_then mp_tac) >> simp[Abbr `p`, checked_frame_context_def] >>
     fs[]) >>
  `well_typed_exprs env es` by
    (qpat_assum `well_typed_expr _ _`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [well_typed_expr_def]) >>
     first_assum ACCEPT_TAC) >>
  `const_cells_agree roots (st' with scopes := [FEMPTY])` by
    (simp[const_cells_agree_scopes] >> drule_all const_subst_context_exprs_frame >> simp[]) >>
  `EVERY (runtime_constant_expr mods) (DROP n dflts) /\
   well_typed_exprs (defaults_env entry) (DROP n dflts)` by
    (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [check_function_body_def, LET_THM]) >>
     simp[Abbr `entry`, EVERY_DROP, frame_well_typed_exprs_slices]) >>
  `eval_exprs p (subst_consts_exprs_mods (consts_env_mods mods) (DROP n dflts))
     (st' with scopes := [FEMPTY]) = eval_exprs p (DROP n dflts) (st' with scopes := [FEMPTY])` by
    (irule (cj 1 (REWRITE_RULE [IMP_CONJ_THM] const_subst_runtime_default_exprs_mods)) >>
     qexistsl_tac [`art`,`defaults_env entry`,`mods`,`roots`] >>
     simp[defaults_env_def, GSYM IMP_CONJ_THM] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!src id r. ALOOKUP (consts_env_mods _) _ = _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  simp[finally_def, ignore_bind_apply, set_scopes_def, return_def]
QED
