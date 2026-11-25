(* Normalize the reached expression replay at the source prefix. *)
Theory bodyForArrayCaptureReplayMods
Ancestors
  bodyForArrayExprRunMods bodyForArrayHeaderMods
  bodyFullPredsMods bodyFullPostsMods exprSimHypsDefs
  vyperState vyperStorageTrace vyperStorageFootprint
  exprSimSource exprSimProps vyperTypeInvariants
  compileEnv loweringPosts finite_map list words arithmetic

Libs monadsyntax

Theorem for_array_capture_replay_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
      (INL raw,em with gas_obs := tail)) /\
  em.gas_obs = [] ==>
  expr_body_pre_mods mods cenv cx env e (es with gas_obs := prefix) /\
  em.gas_obs = [] /\
  eval_expr cx e (es with gas_obs := prefix) =
    (INL raw,em with gas_obs := [])
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ es` mp_tac >>
      rewrite_tac[expr_body_pre_mods_def,expr_sim_inv_mods_def,env_consistent_def,
                  env_scopes_consistent_def,env_immutables_consistent_def,
                  state_well_typed_def] >>
      CONV_TAC (RATOR_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [])) THENC
                RAND_CONV (SIMP_CONV (srw_ss()) [])) >>
      disch_then ACCEPT_TAC)
  >- (conj_tac
      >- first_assum ACCEPT_TAC
      >- (qpat_assum `!tail. eval_expr _ _ _ = _`
            (qspec_then `[]` (fn th =>
              assume_tac (REWRITE_RULE [APPEND_NIL] th))) >>
           first_assum ACCEPT_TAC))
QED
