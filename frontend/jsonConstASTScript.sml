Theory jsonConstAST
Ancestors
  jsonAST

(* Pre-evaluation annotations retain their bound expressions. This initial
   frontend fragment has integer constants and pure, single-return functions. *)
Datatype:
  const_annotation = CA_Integer num bool
                   | CA_Array const_annotation json_expr
End

Datatype:
  const_declaration = CD_Constant string const_annotation json_expr
                    | CD_Function string ((string # const_annotation) list)
                        const_annotation json_expr
End
