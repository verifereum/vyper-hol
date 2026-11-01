(* TOP-LEVEL: supported_program (on tops ALONE), supported_function_body,
   supported_declaration_body; occurs_abi_decode_target for PLAN 5.5/D9.
   Whitelist assembly, NOT check_contract/source_typing_ok or correctness.
   Every non-function body branch is explicit and header admission is separate. *)
Theory supportedProgram
Ancestors
  supportedStmts supportedStmtTraverse supportedExprTraverse supportedNames
  supportedDecls supportedTypes vyperAST list

(* Return lowering copies using the declared return layout. Equal nested
   aggregate layouts are admitted; differing aggregate subtype layouts still
   require the independent #560 repair. *)
Definition supported_return_layout_def:
  supported_return_layout ret (Return (SOME e)) =
    supported_copy_types ret (expr_type e) /\
  supported_return_layout ret (If c yes no) =
    (supported_return_layouts ret yes /\ supported_return_layouts ret no) /\
  supported_return_layout ret (For name ty iter n loop_body) =
    supported_return_layouts ret loop_body /\
  supported_return_layout ret stmt = T /\
  supported_return_layouts ret [] = T /\
  supported_return_layouts ret (s::ss) =
    (supported_return_layout ret s /\ supported_return_layouts ret ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

Definition supported_function_body_def:
  supported_function_body tops vis args body <=>
    let locals = supported_stmts_bindings T body;
        loops = supported_stmts_bindings F body;
        bindings = args ++ locals ++ loops
    in supported_function_bindings tops args (MAP FST locals) (MAP FST loops) /\
       supported_stmts tops bindings body /\
       ~supported_stmts_expr_exists expr_nonmain_type_root body /\
       (vis = Internal ==>
         ~supported_stmts_expr_exists expr_internal_call_root body)
End

Definition supported_declaration_body_def:
  supported_declaration_body tops (FunctionDecl vis mut nr rr name args defaults ret body) =
    (supported_function_body tops vis args body /\
     supported_return_layouts ret body) /\
  supported_declaration_body tops (VariableDecl vis mut name ty slot) = T /\
  supported_declaration_body tops (HashMapDecl vis trans name kt vt slot) = T /\
  supported_declaration_body tops (StructDecl name fields) = T /\
  supported_declaration_body tops (EventDecl name fields) = T /\
  supported_declaration_body tops (InterfaceDecl name methods) = T /\
  supported_declaration_body tops (FlagDecl name members) = F
End

Definition supported_program_def:
  supported_program tops <=>
    supported_declaration_headers tops /\ supported_declaration_names tops /\
    EVERY (supported_declaration_body tops) tops
End

(* Exact target-type occurrence (not just a dynamic boolean): needed by the
   existential in decode_strictness_exempt. Traverse unsupported expressions,
   targets, iterators and reasons too. Only FUNCTION BODIES, as PLAN 5.5 says;
   defaults/constants are not bodies and are excluded by supported_program. *)
Definition expr_abi_decode_target_root_def:
  expr_abi_decode_target_root target
    (TypeBuiltin ty (AbiDecode unwrap) decoded es) = (decoded = target) /\
  expr_abi_decode_target_root target _ = F
End

Definition declaration_abi_decode_target_def:
  declaration_abi_decode_target target
    (FunctionDecl vis mut nr rr name args defaults ret body) =
      supported_stmts_expr_exists (expr_abi_decode_target_root target) body /\
  declaration_abi_decode_target target (VariableDecl vis mut name ty slot) = F /\
  declaration_abi_decode_target target (HashMapDecl vis trans name kt vt slot) = F /\
  declaration_abi_decode_target target (StructDecl name fields) = F /\
  declaration_abi_decode_target target (EventDecl name fields) = F /\
  declaration_abi_decode_target target (InterfaceDecl name methods) = F /\
  declaration_abi_decode_target target (FlagDecl name members) = F
End

Definition occurs_abi_decode_target_def:
  occurs_abi_decode_target target tops <=>
    EXISTS (declaration_abi_decode_target target) tops
End

(* ===== Boundary contracts ===== *)

Theorem supported_program_declaration:
  supported_program tops /\ MEM top tops ==>
    supported_declaration_header tops top /\ supported_declaration_body tops top
Proof
  simp[supported_program_def, supported_declaration_headers_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem supported_program_function:
  supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
    supported_function_body tops vis args stmts
Proof
  strip_tac >> drule_all supported_program_declaration >>
  simp[supported_declaration_body_def]
QED

Theorem supported_internal_body_contract:
  supported_function_body tops Internal args stmts ==>
    ~supported_stmts_expr_exists expr_internal_call_root stmts
Proof
  simp[supported_function_body_def]
QED

Theorem supported_function_body_binding_contract:
  supported_function_body tops vis args stmts ==>
    supported_function_bindings tops args
      (MAP FST (supported_stmts_bindings T stmts))
      (MAP FST (supported_stmts_bindings F stmts))
Proof
  simp[supported_function_body_def]
QED

Theorem supported_program_names:
  supported_program tops ==> supported_declaration_names tops
Proof
  simp[supported_program_def]
QED

Theorem occurs_abi_decode_target_function:
  occurs_abi_decode_target target
    [FunctionDecl vis mut nr rr name args defaults ret stmts] <=>
  supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts
Proof
  simp[occurs_abi_decode_target_def, declaration_abi_decode_target_def]
QED

Theorem occurs_abi_decode_target_append:
  occurs_abi_decode_target target (xs ++ ys) <=>
    occurs_abi_decode_target target xs \/ occurs_abi_decode_target target ys
Proof
  simp[occurs_abi_decode_target_def, EXISTS_APPEND]
QED
