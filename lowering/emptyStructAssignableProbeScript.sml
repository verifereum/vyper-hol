Theory emptyStructAssignableProbe
Ancestors
  supportedTypes vyperTypeSystem vyperContext vyperValue finite_map

Theorem empty_struct_unsupported:
  ~supported_nested_type supported_scalar_type 1 [StructDecl "Empty" []]
    (StructT (NONE,"Empty"))
Proof
  EVAL_TAC
QED
