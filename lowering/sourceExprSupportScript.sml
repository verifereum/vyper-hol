(* #543: transparent expression remainder. Only the builtin MethodId/Exp
   gates differ from supportedExprs; in particular local tuple bases remain
   excluded. Original whitelist definitions are unchanged. *)
Theory sourceExprSupport
Ancestors
  sourceBuiltinSupport supportedExprs supportedExprForms supportedTypes
  supportedDecls vyperTypeSystem vyperAST list pair

Definition source_pure_expr_remainder_def:
  source_pure_expr_remainder tops (Name ty name) = T /\
  source_pure_expr_remainder tops (Literal ty lit) = T /\
  source_pure_expr_remainder tops (TopLevelName ty id) =
    supported_storage_scalar tops id ty /\
  source_pure_expr_remainder tops (FlagMember ty id member) = F /\
  source_pure_expr_remainder tops (IfExp ty c a b) =
    (supported_value_type tops ty /\ ~supported_tuple_type ty /\
     source_pure_expr_remainder tops c /\
     source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops b) /\
  source_pure_expr_remainder tops (StructLit ty id fields) =
    (supported_main_nsid id /\ supported_value_type tops ty /\
     source_pure_fields_remainder tops fields) /\
  source_pure_expr_remainder tops (Subscript ty base key) =
    ((case base of
        TopLevelName bt id => supported_subscript_base tops id
      | _ => F) /\ source_pure_expr_remainder tops key) /\
  source_pure_expr_remainder tops (Attribute ty base field) =
    (case base of
       TopLevelName bt id => supported_storage_field_read tops id field
     | _ => F) /\
  source_pure_expr_remainder tops (Builtin ty blt es) =
    (source_builtin_remainder tops ty blt es /\
     source_pure_exprs_remainder tops es) /\
  source_pure_expr_remainder tops (TypeBuiltin ty blt target es) =
    (supported_type_builtin_form tops ty blt target es /\
     source_pure_exprs_remainder tops es) /\
  source_pure_expr_remainder tops (Pop ty target) = F /\
  source_pure_expr_remainder tops (Call ty target es default) = F /\
  source_pure_exprs_remainder tops [] = T /\
  source_pure_exprs_remainder tops (e::es) =
    (source_pure_expr_remainder tops e /\ source_pure_exprs_remainder tops es) /\
  source_pure_fields_remainder tops [] = T /\
  source_pure_fields_remainder tops ((name,e)::fields) =
    (source_pure_expr_remainder tops e /\ source_pure_fields_remainder tops fields)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (INL (_, es)) => expr4_size es
    | INR (INR (_, fields)) => expr1_size fields)` >>
  simp[expr_size_def] >>
  qsuff_tac
    `(!es. expr4_size es = list_size expr_size es) /\
     (!fields. expr1_size fields =
       list_size (pair_size (list_size char_size) expr_size) fields)`
  >- (strip_tac >> asm_rewrite_tac[] >> DECIDE_TAC) >>
  conj_tac >> Induct >>
  simp[expr_size_def, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  Cases >> simp[expr_size_def, basicSizeTheory.pair_size_def]
End

Theorem checked_pure_remainder:
  (!tops e. !env. well_typed_expr env e ==>
    (source_pure_expr_remainder tops e <=> supported_pure_expr tops e)) /\
  (!tops es. !env. well_typed_exprs env es ==>
    (source_pure_exprs_remainder tops es <=> supported_pure_exprs tops es)) /\
  (!tops fields. !env. well_typed_named_exprs env fields ==>
    (source_pure_fields_remainder tops fields <=> supported_pure_fields tops fields))
Proof
  ho_match_mp_tac source_pure_expr_remainder_ind >> rw[] >>
  TRY (drule typed_builtin_remainder >> strip_tac) >>
  fs[source_pure_expr_remainder_def, supported_pure_expr_def,
     Once well_typed_expr_def] >> metis_tac[]
QED

Definition source_effect_expr_remainder_def:
  source_effect_expr_remainder tops e <=>
    case e of
      Call ty (IntCall id) args NONE =>
        IS_SOME (supported_function_decl tops id Internal) /\
        source_pure_exprs_remainder tops args
    | Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args NONE =>
        EVERY supported_word_type arg_types /\
        supported_external_return_type tops ret /\
        ALL_DISTINCT opts /\ (static_call ==> ~MEM EKValue opts) /\
        LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
        source_pure_exprs_remainder tops args
    | Call NoneT (Send F) [a; v] NONE =>
        source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops v
    | Call NoneT (Send T) [a; v; g] NONE =>
        source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops v /\
        source_pure_expr_remainder tops g
    | Pop ty (TopLevelNameTarget id) => supported_storage_dynamic_array tops id
    | _ => F
End

Definition source_expr_remainder_def:
  source_expr_remainder tops e <=>
    source_pure_expr_remainder tops e \/ source_effect_expr_remainder tops e
End

Theorem checked_effect_remainder:
  well_typed_expr env e ==>
  (source_effect_expr_remainder tops e <=> supported_effect_expr tops e)
Proof
  Cases_on `e` >>
  simp[source_effect_expr_remainder_def, supported_effect_expr_def] >>
  rename1 `Call ty target args default` >>
  Cases_on `default` >> simp[] >>
  Cases_on `target` >> simp[] >>
  TRY (rename1 `IntCall nsid` >> Cases_on `nsid` >> simp[]) >>
  TRY (rename1 `ExtCall static_call skip signature opts` >>
       PairCases_on `signature` >> simp[]) >>
  strip_tac >> fs[Once well_typed_expr_def] >>
  imp_res_tac checked_pure_remainder >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> fs[well_typed_expr_def]) >>
  imp_res_tac checked_pure_remainder >> simp[]
QED

Theorem checked_expr_remainder:
  well_typed_expr env e ==>
  (source_expr_remainder tops e <=> supported_expr tops e)
Proof
  simp[source_expr_remainder_def, supported_expr_def] >>
  metis_tac[checked_pure_remainder, checked_effect_remainder]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source expression support kernel audit: " ^ name) end)
  (DB.thms "sourceExprSupport");
