Theory sourceMeaningConst
Ancestors
  sourceConstEval sourceConstEvalProps sourceConstEnvProps sourceConstEnv list alist

(* Independent syntax-directed staged constant semantics. The scalar operator
   algebra is the pinned mathematical source algebra, NOT runtime arithmetic.
   No elaborator, reifier, runtime expression or source_const_eval occurs in
   these rules. All children are visited, including unselected Boolean arms. *)
Definition source_meaning_const_def:
  source_meaning_const rho (SCE_Literal l) = source_const_literal l /\
  source_meaning_const rho (SCE_Name p) = source_const_lookup rho p /\
  source_meaning_const rho SCE_Dynamic = SC_NotConstant /\
  source_meaning_const rho (SCE_BytesType fixed e) =
    source_const_then (source_meaning_const rho e) (source_const_bytes_type fixed) /\
  source_meaning_const rho (SCE_Unary op e) =
    source_const_then (source_meaning_const rho e) (source_const_unary op) /\
  source_meaning_const rho (SCE_Binary op l r) =
    source_const_combine (source_const_binary op)
      (source_meaning_const rho l) (source_meaning_const rho r) /\
  source_meaning_const rho (SCE_Boolean op es) =
    source_const_then (source_const_collect (MAP (source_meaning_const rho) es))
      (source_const_boolean op) /\
  source_meaning_const rho (SCE_Compare op l r) =
    source_const_combine (source_const_compare op)
      (source_meaning_const rho l) (source_meaning_const rho r) /\
  source_meaning_const rho (SCE_List es) =
    source_const_then (source_const_collect (MAP (source_meaning_const rho) es))
      (\vs. SC_Value (SCV_List vs)) /\
  source_meaning_const rho (SCE_Tuple es) =
    source_const_then (source_const_collect (MAP (source_meaning_const rho) es))
      source_const_tuple /\
  source_meaning_const rho (SCE_Subscript e i) =
    source_const_combine source_const_subscript
      (source_meaning_const rho e) (source_meaning_const rho i) /\
  source_meaning_const rho (SCE_Builtin b args kws) =
    source_const_builtin_result b
      (source_const_combine
        (\vs ks. source_const_checked_builtin b vs (ZIP (MAP FST kws,ks)))
        (source_const_collect (MAP (source_meaning_const rho) args))
        (source_const_collect (MAP (\kw. source_meaning_const rho (SND kw)) kws))) /\
  source_meaning_const rho (SCE_Call callee args kws) =
    source_const_unimplemented SCS_Call
      (source_meaning_const rho callee ::
       (MAP (source_meaning_const rho) args ++
        MAP (\kw. source_meaning_const rho (SND kw)) kws)) /\
  source_meaning_const rho (SCE_Unsupported tag es) =
    source_const_unimplemented (SCS_Syntax tag) (MAP (source_meaning_const rho) es)
End

(* Frozen evaluator/meaning contract: equality includes all four outcomes,
   not merely successful values. This is a structural source theorem. *)
Theorem source_meaning_const_correct:
  !rho e. source_const_eval rho e = source_meaning_const rho e
Proof
  ho_match_mp_tac source_const_eval_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  fs[GSYM MAP_EQ_f] >>
  simp[Once source_const_eval_def, Once source_meaning_const_def]
QED

Theorem source_meaning_const_value_ok:
  !rho e v. source_meaning_const rho e = SC_Value v ==> source_const_value_ok v
Proof
  metis_tac[source_meaning_const_correct, source_const_eval_value_ok]
QED

Theorem source_meaning_const_unbounded_add:
  !rho a b. source_meaning_const rho
    (SCE_Binary SCB_Add (SCE_Literal (SCL_Int a)) (SCE_Literal (SCL_Int b))) =
  SC_Value (SCV_Int (a + b))
Proof
  simp[source_meaning_const_def, source_const_literal_def,
       source_const_combine_def, source_const_binary_def,
       source_const_integer_binary_def]
QED

Theorem source_meaning_const_transport:
  !rho e. !rho'.
  (!p. MEM p (source_const_names e) ==> ALOOKUP rho p = ALOOKUP rho' p) ==>
  source_meaning_const rho e = source_meaning_const rho' e
Proof
  simp[GSYM source_meaning_const_correct, source_const_eval_name_congruence]
QED
