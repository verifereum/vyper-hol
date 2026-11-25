(* Linked If case for the evaluator induction. *)
Theory bodyIfBranchCaseMods
Ancestors
  bodyFullPredsMods bodyIfSourceEntryMods bodyIfCountedFragmentMods
  bodyFullIfExpReach

Theorem if_stmt_full_ok_mods:
  !mods exps cx e yes no.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
       body_stmts_full_ok_mods mods exps cx yes) /\
    (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
       body_stmts_full_ok_mods mods exps cx no) /\
    body_expr_full_ok_mods mods exps cx e ==>
    body_stmt_full_ok_mods mods exps cx (If e yes no)
Proof
  rpt gen_tac >> disch_tac >> strip_tac >> rw[body_stmt_full_ok_mods_def] >>
  `expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es` by
    (irule if_condition_pre_mods >> simp[] >> conj_tac
     >- (qexistsl_tac [`ctx`, `exps`] >> simp[] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bindings`, `env'`, `no`, `ret_ty`, `src`, `tops`, `yes`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule compile_if_stmt_frag_full_mods >> simp[] >>
  rpt conj_tac
  >~ [`expr_sim_full_mods _ _ _ _ _ _`]
  >- (
    qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
      (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM] o
       ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
    qpat_assum `!df lo d pg src tops ctx sh fn shfn ce env ty es. _ ==>
                  expr_sim_full_mods _ _ _ _ _ _` irule >>
    simp[] >> conj_tac >- (qexistsl_tac [`src`, `tops`] >> simp[]) >>
    qexists_tac `env` >> simp[])
  >- (match_mp_tac (GEN_ALL if_selected_fragment_mods) >>
      qexistsl_tac [`tops`, `src`, `mods`, `exps`, `env'`, `env`, `bindings`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[]
QED
