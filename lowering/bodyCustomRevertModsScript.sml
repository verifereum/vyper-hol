(* The custom-error descriptor selects its owner in the linked unit. *)
Theory bodyCustomRevertMods
Ancestors
  bodyInvCodeProps bodyQualifiedStmtSupport vyperTypeContract vyperInterpreter
  vyperAST vyperABI vyperEvent vyperState list pair

Theorem custom_error_order_keeps_exprs_mods[local]:
  order_custom_error_args params err = SOME args ==>
  args = custom_error_exprs err
Proof
  Cases_on `err` >>
  simp[order_custom_error_args_def, custom_error_exprs_def, AllCaseEqs()] >>
  strip_tac >> gvs[NULL_EQ] >>
  drule order_custom_error_kwargs_SOME >> simp[]
QED

Theorem custom_error_raise_source_mods:
  contract_inv mods exps ctx cenv cx /\
  qualified_stmt_decls_ok mods (Raise (RaiseCustomError err)) ==>
  ?id pos kw error_tops params args.
    err = CustomError id pos kw /\
    get_module_code cx (FST id) = SOME error_tops /\
    lookup_custom_error_args_in (SND id) error_tops = SOME params /\
    order_custom_error_args params err = SOME args /\
    args = custom_error_exprs err /\
    MAP expr_type args = MAP SND params /\
    eval_stmt cx (Raise (RaiseCustomError err)) =
      bind (eval_exprs cx args) (\vs. bind
        (lift_option (build_custom_error_data (get_tenv cx) (SND id)
          (MAP SND params) vs) "custom error encoding")
        (\data. raise (Error (RevertData data))))
Proof
  Cases_on `err` >> PairCases_on `p` >> strip_tac >>
  drule_then assume_tac contract_inv_module_codes >>
  fs[qualified_stmt_decls_ok_def, qualified_custom_error_ok_def,
     custom_error_resolved_def] >>
  Cases_on `ALOOKUP mods p0` >> gvs[] >>
  rename1 `ALOOKUP mods _ = SOME ts` >>
  Cases_on `lookup_custom_error_args_in p1 ts` >> gvs[] >>
  rename1 `lookup_custom_error_args_in _ _ = SOME ps` >>
  Cases_on `order_custom_error_args ps (CustomError (p0,p1) l l0)` >> gvs[] >>
  drule custom_error_order_keeps_exprs_mods >> strip_tac >>
  gvs[Once evaluate_def]
QED
