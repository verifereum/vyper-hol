(* Static guards for the ranked callback at the selected callee. *)
Theory bodySelectedCalleeGuardsMods
Ancestors
  bodyLoopCalls bodyStorageCases constSubstMods
  vyperTypeCallGraphSoundness vyperTypeCallGraph vyperTypeContract vyperAST
  alist list

Triviality selected_callee_calls_live:
  MEM (src,fn) (linked_live_functions mods exps) /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  MEM key (function_int_calls dflts ss) ==>
  MEM key (linked_live_functions mods exps)
Proof
  strip_tac >>
  `call_edge_rel (contract_call_edges mods) (src,fn) key` by
    (simp[call_edge_rel_def] >> drule_all contract_call_edges_function >> simp[]) >>
  qpat_x_assum `MEM (src,fn) (linked_live_functions _ _)` mp_tac >>
  pure_rewrite_tac[linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
  BETA_TAC >> strip_tac >>
  irule (cj 2 call_closure_from_roots) >>
  qexists_tac `(src,fn)` >> asm_rewrite_tac[]
QED

Triviality subst_defaults_calls_live:
  (!e. int_calls_expr (subst_consts_expr_mods env e) = int_calls_expr e) ==>
  !es. EVERY P (int_calls_exprs es) ==>
    EVERY P (int_calls_exprs (subst_consts_exprs_mods env es))
Proof
  strip_tac >> Induct >> simp[subst_consts_expr_mods_def, int_calls_expr_def, EVERY_APPEND]
QED

(* The linked tops producer supplies the checked body-entry and expression
   call-preservation implications; keep them explicit at this boundary. *)
Theorem selected_callee_live_guards_mods:
  check_contract mode layouts addr mods = SOME artifact /\
  MEM (src,fn) (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
  (check_contract mode layouts addr mods = SOME artifact /\
   MEM (src,tops) mods /\
   MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops /\
   MEM (src,fn) (linked_live_functions mods exps) ==>
   EVERY (\k. MEM k (linked_live_functions mods exps))
     (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss))) /\
  (check_contract mode layouts addr mods = SOME artifact ==>
   !e. int_calls_expr (subst_consts_expr_mods (consts_env_mods mods) e) = int_calls_expr e) /\
  (!src' tops' vis' mut' nr' raw' fn' args' dflts' ret' ss'.
     ALOOKUP mods src' = SOME tops' /\
     MEM (FunctionDecl vis' mut' nr' raw' fn' args' dflts' ret' ss') tops' ==>
     stmts_loop_calls_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss')) ==>
  EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  stmts_loop_calls_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss) /\
  (!n. EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_exprs (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))))
Proof
  strip_tac >>
  `MEM (src,tops) mods` by (drule ALOOKUP_MEM >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- (first_x_assum drule_all >> simp[]) >>
  `EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs dflts)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM key (int_calls_exprs dflts)` >>
     `MEM key (function_int_calls dflts ss)` by simp[function_int_calls_def] >>
     drule_all selected_callee_calls_live >> simp[]) >>
  gen_tac >> irule int_calls_exprs_DROP_EVERY >>
  irule subst_defaults_calls_live >> simp[]
QED
