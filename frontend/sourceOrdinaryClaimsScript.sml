Theory sourceOrdinaryClaims
Ancestors
  sourceSyntax jsonAST jsonNominalSources list pair

(* Syntax/claim pairing ONLY: neither constant evaluation, residual policy nor
   source typing. Children follow source order, including call designators and
   keyword values. A path is an occurrence, not source-expression equality. *)
Datatype:
  source_claims = SourceClaims source_expr json_expr (source_claims list)
End

Datatype:
  source_program_claims = SourceProgramClaims source_program
    ((num list # source_claims) list)
End

Definition source_claims_source_def:
  source_claims_source (SourceClaims original legacy children) = original
End

Definition source_claims_legacy_def:
  source_claims_legacy (SourceClaims original legacy children) = legacy
End

Definition source_claims_children_def:
  source_claims_children (SourceClaims original legacy children) = children
End

Definition source_claims_at_def:
  source_claims_at [] claims = SOME claims /\
  source_claims_at (n::ns) (SourceClaims original legacy children) =
    if n < LENGTH children then source_claims_at ns (EL n children) else NONE
End

Definition source_claims_source_children_def:
  (source_claims_source_children (SX_Literal lit) = []) /\
  (source_claims_source_children (SX_Name name) = []) /\
  (source_claims_source_children (SX_Attribute e name) = [e]) /\
  (source_claims_source_children (SX_Subscript e i) = [e;i]) /\
  (source_claims_source_children (SX_Unary oper e) = [e]) /\
  (source_claims_source_children (SX_Binary oper l r) = [l;r]) /\
  (source_claims_source_children (SX_Compare oper l r) = [l;r]) /\
  (source_claims_source_children (SX_Boolean oper es) = es) /\
  (source_claims_source_children (SX_List es) = es) /\
  (source_claims_source_children (SX_Tuple es) = es) /\
  (source_claims_source_children (SX_Dict entries) =
    FLAT (MAP (\(k,v). [k;v]) entries)) /\
  (source_claims_source_children (SX_Call callee args kwargs) =
    callee::(args ++ MAP SND kwargs)) /\
  (source_claims_source_children (SX_ExtCall e) = [e]) /\
  (source_claims_source_children (SX_StaticCall e) = [e]) /\
  (source_claims_source_children (SX_IfExp c t e) = [c;t;e]) /\
  (source_claims_source_children (SX_NamedExpr target value) = [target;value]) /\
  (source_claims_source_children SX_Ellipsis = [])
End

(* Folded syntax is excluded even inside a legacy dispatch/signature claim. *)
Definition source_legacy_unfolded_def:
  (source_legacy_unfolded (JE_Folded original replacement) = F) /\
  (source_legacy_unfolded (JE_Attribute e attr tc btn btc src ty) =
    source_legacy_unfolded e) /\
  (source_legacy_unfolded (JE_Subscript e i ty) =
    (source_legacy_unfolded e /\ source_legacy_unfolded i)) /\
  (source_legacy_unfolded (JE_NamedExpr target value) =
    (source_legacy_unfolded target /\ source_legacy_unfolded value)) /\
  (source_legacy_unfolded (JE_BinOp l oper r ty) =
    (source_legacy_unfolded l /\ source_legacy_unfolded r)) /\
  (source_legacy_unfolded (JE_Compare l oper r) =
    (source_legacy_unfolded l /\ source_legacy_unfolded r)) /\
  (source_legacy_unfolded (JE_BoolOp oper es) = EVERY source_legacy_unfolded es) /\
  (source_legacy_unfolded (JE_UnaryOp oper e ty) = source_legacy_unfolded e) /\
  (source_legacy_unfolded (JE_IfExp c t e ty) =
    (source_legacy_unfolded c /\ source_legacy_unfolded t /\ source_legacy_unfolded e)) /\
  (source_legacy_unfolded (JE_Tuple es) = EVERY source_legacy_unfolded es) /\
  (source_legacy_unfolded (JE_List es ty) = EVERY source_legacy_unfolded es) /\
  (source_legacy_unfolded (JE_Call callee args kwargs ty src) =
    (source_legacy_unfolded callee /\ EVERY source_legacy_unfolded args /\
     EVERY (\kw. case kw of JKeyword name value => source_legacy_unfolded value) kwargs)) /\
  (source_legacy_unfolded (JE_ExtCall name src argtys retty target args kwargs) =
    (source_legacy_unfolded target /\ EVERY source_legacy_unfolded args /\
     EVERY (\kw. case kw of JKeyword name value => source_legacy_unfolded value) kwargs)) /\
  (source_legacy_unfolded (JE_StaticCall name src argtys retty target args kwargs) =
    (source_legacy_unfolded target /\ EVERY source_legacy_unfolded args /\
     EVERY (\kw. case kw of JKeyword name value => source_legacy_unfolded value) kwargs)) /\
  (source_legacy_unfolded (JE_Int value ty) = T) /\
  (source_legacy_unfolded (JE_Decimal value) = T) /\
  (source_legacy_unfolded (JE_Str len value) = T) /\
  (source_legacy_unfolded (JE_GenericStr value) = T) /\
  (source_legacy_unfolded (JE_Bytes len value) = T) /\
  (source_legacy_unfolded (JE_Hex value ty) = T) /\
  (source_legacy_unfolded (JE_Bool value) = T) /\
  (source_legacy_unfolded (JE_Name name tc src ty) = T) /\
  (source_legacy_unfolded JE_Ellipsis = T)
End

(* This checks mirror coverage and fold exclusion, not authenticity/typing of
   legacy claims. ML separately compares both source-only decoded projections. *)
Definition source_claims_shape_def:
  source_claims_shape (SourceClaims original legacy children) =
    (source_legacy_unfolded legacy /\
     MAP source_claims_source children = source_claims_source_children original /\
     EVERY source_claims_shape children)
End

Definition source_program_claims_source_def:
  source_program_claims_source (SourceProgramClaims original roots) = original
End

Definition source_program_claims_roots_def:
  source_program_claims_roots (SourceProgramClaims original roots) = roots
End

Definition source_program_claims_shape_def:
  source_program_claims_shape (SourceProgramClaims original roots) =
    (ALL_DISTINCT (MAP FST roots) /\ EVERY (source_claims_shape o SND) roots)
End

Theorem source_claims_child_coverage:
  source_claims_shape claims ==>
  MAP source_claims_source (source_claims_children claims) =
  source_claims_source_children (source_claims_source claims)
Proof
  Cases_on `claims` >> simp[source_claims_shape_def,
    source_claims_source_def, source_claims_children_def]
QED

Theorem source_claims_legacy_has_no_folds:
  source_claims_shape claims ==> source_legacy_unfolded (source_claims_legacy claims)
Proof
  Cases_on `claims` >> simp[source_claims_shape_def, source_claims_legacy_def]
QED

Theorem source_claims_occurrence_root:
  source_claims_at [] claims = SOME claims
Proof
  simp[source_claims_at_def]
QED

Theorem source_program_claims_retained:
  retained_source (SourceRetained original claims) = original /\
  retained_executable (SourceRetained original claims) = claims
Proof
  simp[retained_source_def, retained_executable_def]
QED
