Theory linkedTypedBodySupport
Ancestors
  whitelistLinkedBodyStmts whitelistLinkedBodyExprs
  whitelistLinkedBodyStmtForms whitelistLinkedBodyRange whitelistLinkedBodyEnv
  constSubstMods vyperTypeContract vyperImportRefs supportedProgram
  vyperTypeSystem vyperAST finite_map list pair

Theorem checked_linked_typed_body_supported:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  (src = NONE ==> !name. ~MEM (StructDecl name []) tops) /\
  linked_body_env tops src (type_env_all_modules mods) env /\
  (src = NONE \/ imported_stmts_refs_ok ss) /\
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  type_stmts env ret ss = SOME out /\
  IS_SOME (type_stmts env ret (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  custom_errors_stmts_ok mods ss ==>
  supported_function_body tops vis args ss
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!env0 e. linked_body_env tops src (type_env_all_modules mods) env0 /\
      (src = NONE \/ imported_expr_refs_ok e) /\ well_typed_expr env0 e ==>
      supported_pure_expr tops e` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `src = NONE ==> !name. ~MEM (StructDecl name []) tops`
       (fn structs =>
         mp_tac (MATCH_MP (Q.INST [`tenv` |-> `type_env_all_modules mods`]
           (INST_TYPE [``:'a`` |-> ``:num``] linked_well_typed_expr_supported)) structs)) >>
     disch_then (qspecl_then [`env0`,`e`] mp_tac o cj 1) >>
     asm_rewrite_tac[] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `!env0 ret0 x ty0 a b n lbody out0 ta i tb j.
      (src = NONE \/ imported_expr_refs_ok a /\ imported_expr_refs_ok b) /\
      type_stmt env0 ret0 (For x ty0 (Range a b) n lbody) = SOME out0 /\
      IS_SOME (type_stmt env0 ret0
        (subst_consts_stmt_mods (consts_env_mods mods)
          (For x ty0 (Range a b) n lbody))) /\
      subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
      subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
      i <= j /\ n = Num (j - i)` by
    (rpt gen_tac >>
     rewrite_tac[constSubstModsTheory.subst_consts_stmt_mods_def,
                 constSubstModsTheory.subst_consts_iter_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all linked_checked_range_literals >> simp[]) >>
  `!env0 ret0 s out0.
      linked_body_env tops src (type_env_all_modules mods) env0 /\
      (src = NONE \/ imported_stmt_refs_ok s) /\
      FDOM env0.var_types SUBSET
        set (MAP FST (args ++ supported_stmts_bindings T ss ++
                      supported_stmts_bindings F ss)) /\
      custom_errors_stmt_ok mods s /\
      type_stmt env0 ret0 s = SOME out0 /\
      (!c yes no. s <> If c yes no) /\
      (!x ty0 it n b. s <> For x ty0 it n b) ==>
      supported_stmt tops
        (args ++ supported_stmts_bindings T ss ++
         supported_stmts_bindings F ss) s` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule linked_stmt_leaf_supported >> simp[] >>
     qexistsl_tac [`env0`, `out0`, `mods`, `ret0`, `src`,
                   `type_env_all_modules mods`] >>
     simp[] >>
     rpt conj_tac
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         drule linked_well_typed_expr_supported >>
         disch_then (qspec_then `type_env_all_modules mods`
           (map_every assume_tac o CONJUNCTS)) >>
         qpat_assum `!env tgt. IS_SOME (type_place_target env tgt) ==> _`
           (qspecl_then [`env0`, `bt`] mp_tac) >> simp[])
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!en e. linked_body_env _ _ _ en /\ _ ==> supported_pure_expr _ e`
           (qspecl_then [`env0`, `e`] mp_tac) >> simp[])
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         drule linked_well_typed_expr_supported >>
         disch_then (qspec_then `type_env_all_modules mods`
           (map_every assume_tac o CONJUNCTS)) >>
         qpat_assum `!env es. well_typed_exprs env es ==> _`
           (qspecl_then [`env0`, `es`] mp_tac) >> simp[]) >>
     fs[linked_body_env_def]) >>
  MATCH_MP_TAC (Q.INST [`env` |-> `env`, `mods` |-> `mods`, `out` |-> `out`,
      `ret` |-> `ret`, `src` |-> `src`, `tenv` |-> `type_env_all_modules mods`]
    (INST_TYPE [``:'a`` |-> ``:num``] linked_typed_body_supported)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
