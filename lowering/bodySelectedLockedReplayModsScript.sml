Theory bodySelectedLockedReplayMods
Ancestors
  bodyFullPredsMods linkedConstReplay constSubstCorrect constSubstMods
  vyperCreate vyperInterpreter vyperState vyperTypeSystem list

(* The offset premise is supplied by the shared blueprint-offset producer. *)
Theorem selected_locked_replay_mods_with_offset:
  (!art. ALOOKUP p.sources p.txn.target = SOME mods /\
         check_contract p.in_deploy p.layouts p.txn.target mods = SOME art ==>
         !salt es.
           blueprint_literal_offset p salt
             (subst_consts_exprs_mods (consts_env_mods mods) es) =
           blueprint_literal_offset p salt es) /\
  body_const_cells_agree_mods mods p env locked /\
  ALL_DISTINCT (MAP FST mods) /\ IS_SOME (type_stmts env ret ss) ==>
  !gs. eval_stmts p (subst_consts_stmts_mods (consts_env_mods mods) ss)
         (locked with gas_obs := gs) =
       eval_stmts p ss (locked with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  irule linkedConstReplayTheory.const_subst_eval_stmts_mods >>
  conj_tac
  >- (qpat_assum `!art. _ ==> !salt es. _` (drule_all_then ACCEPT_TAC)) >>
  qexistsl_tac [`art`, `env`, `mods`, `ret`, `roots`] >>
  `const_cells_agree roots (locked with gas_obs := gs)` by
    fs[const_cells_agree_def] >>
  asm_rewrite_tac[]
QED
