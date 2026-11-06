Theory emptyStructAssignableProbe
Ancestors
  supportedTypes vyperTypeSystem vyperContext vyperValue finite_map

Theorem empty_struct_assignability_counterexample:
  supported_nested_type supported_scalar_type 1 [StructDecl "Empty" []]
    (StructT (NONE,"Empty")) /\
  type_env [StructDecl "Empty" []] SUBMAP type_env [StructDecl "Empty" []] /\
  well_formed_type (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty")) /\
  ~assignable_type (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty"))
Proof
  EVAL_TAC >> simp[]
QED
