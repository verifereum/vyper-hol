(* Exclude the two source exemptions while evaluating omitted checked defaults. *)
Theory linkedDefaultError
Ancestors
  runtimeDefaultErrorDescent groupedRejectSourceError sourceExemptMods e2eDefs
  supportedProgram supportedExprTraverse whitelistCheckerConsts constSubst
  vyperABI vyperAST vyperInterpreter contractABI list

Theorem runtime_constant_defaults_no_exempt_mods:
  EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds /\
  eval_exprs cx ds st = (INR (Error err),ee) ==>
  ~unspecified_behaviour_exempt_mods mods err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  strip_tac >>
  `?tops. unspecified_behaviour_exempt tops err` by
    (qpat_assum `unspecified_behaviour_exempt_mods _ _`
       (strip_assume_tac o REWRITE_RULE [unspecified_behaviour_exempt_mods_def])
     >- (qexists_tac `[FunctionDecl External Pure F F "witness" []
          [TypeBuiltin (BaseT (StringT 1)) (AbiDecode F) (BaseT (StringT 1)) []]
          NoneT []]` >>
         simp[unspecified_behaviour_exempt_def, occurs_abi_decode_target_def,
              declaration_abi_decode_target_def, supported_expr_exists_def,
              expr_abi_decode_target_root_def] >>
         qexists_tac `BaseT (StringT 1)` >> simp[])
     >- (qexists_tac `[]` >> simp[unspecified_behaviour_exempt_def])) >>
  `!st ee. eval_exprs cx ds st <> (INR (Error err),ee)` by
    (irule default_eval_error_if_descent >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `mods` >> simp[] >>
     qx_genl_tac [`ds'`,`st'`,`ee'`] >> strip_tac >>
     mp_tac (Q.INST [`ds` |-> `ds'`,`st` |-> `st'`,`ee` |-> `ee'`]
       (SPEC_ALL grouped_default_error_descent)) >>
     asm_rewrite_tac[]) >>
  qpat_assum `!st ee. eval_exprs cx ds st <> _`
    (qspecl_then [`st`,`ee`] (fn excluded =>
       qpat_assum `eval_exprs cx ds st = (INR (Error err),ee)`
         (ACCEPT_TAC o MP (NOT_ELIM excluded))))
QED
