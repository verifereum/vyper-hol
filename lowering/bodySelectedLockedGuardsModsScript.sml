(* Specialize the checked immutable-guard rule at the locked callee frame. *)
Theory bodySelectedLockedGuardsMods
Ancestors
  bodyFullPredsMods bodyInvSplit constSubstCorrect constSubstMods
  exprSimHypsDefs supportedExprTraverse vyperSubscriptOverlap
  vyperTypeContract finite_map alist list option

(* The guard callback is supplied by the shared checked-body layer.  The raw
   ownership premise belongs to the combined main and export roots. *)
Theorem selected_locked_immutable_guards_mods:
  let b = subst_consts_stmts_mods (consts_env_mods mods) ss in
  let guards =
    (~supported_stmts_expr_exists (unallocated_bare_global_root body_ce env) b /\
     (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts b) /\
            IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
            IS_SOME (FLOOKUP body_ce.ce_module_vars key)))
  in
    MEM (src,name) (linked_live_functions mods exps) /\
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
    body_const_cells_agree_mods mods p env locked /\
    contract_inv mods exps ctx body_ce p /\
    check_linked_state_ownership p.layouts p.txn.target mods
      (linked_live_functions mods exps) /\
    (!art.
       check_contract p.in_deploy p.layouts p.txn.target mods = SOME art /\
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
       MEM (src,name) (linked_live_functions mods exps) /\
       check_linked_state_ownership p.layouts p.txn.target mods
         (linked_live_functions mods exps) /\
       env.bare_globals = art.cta_bare_globals /\
       env.bare_global_assignable = art.cta_bare_global_assignable /\
       (!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==>
                   accesses_expr r = []) /\
       immutable_section_layout_mods mods body_ce ==>
       guards) ==>
    guards
Proof
  SIMP_TAC bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  drule contract_inv_immutable_section_layout >> strip_tac >>
  qpat_x_assum `frame_maps _ _`
    (strip_assume_tac o REWRITE_RULE [frame_maps_def]) >>
  `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==>
              accesses_expr r = []` by
    (rpt strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods _) _ = _ ==> _`
       (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!art. check_contract _ _ _ _ = SOME art /\ _ ==> _`
    (qspec_then `art` mp_tac) >>
  asm_rewrite_tac[]
QED
