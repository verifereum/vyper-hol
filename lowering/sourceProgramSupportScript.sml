(* #543 TOP-LEVEL: source_program_remainder, checked_program_remainder.
   This transparent whitelist differs ONLY in MethodId/Exp expression gates
   and Exp AugAssign's literal gate. All headers, names, effects, widths,
   nested-place types, return layouts, loop and binding restrictions are retained. Defaults
   are still excluded by the unchanged declaration headers; their checked
   typing/remainder fact is nevertheless exposed below.
   This is a gate-redundancy certificate only, independent of the extracted
   optional checked-Exp execution/simulation certificates. The existing
   whole-compiler wrapper still inherits lower_vyper_runtime_unit_correct's
   unrelated admissions and is not a new compiler-semantics theorem. *)
Theory sourceProgramSupport
Ancestors
  sourceStmtSupport sourceExprSupport supportedProgram supportedStmts
  supportedStmtTraverse supportedExprTraverse supportedNames supportedDecls
  supportedTypes vyperTypeContract vyperTypeSystem vyperAST list option

Definition source_function_body_remainder_def:
  source_function_body_remainder tops vis args stmts <=>
    let locals = supported_stmts_bindings T stmts;
        loops = supported_stmts_bindings F stmts;
        bindings = args ++ locals ++ loops
    in supported_function_bindings tops args (MAP FST locals) (MAP FST loops) /\
       source_stmts_remainder tops bindings stmts /\
       ~supported_stmts_expr_exists expr_nonmain_type_root stmts /\
       (vis = Internal ==>
         ~supported_stmts_expr_exists expr_internal_call_root stmts)
End

Definition source_declaration_body_remainder_def:
  source_declaration_body_remainder tops (FunctionDecl vis mut nr rr name args defaults ret stmts) =
    (source_function_body_remainder tops vis args stmts /\
     supported_return_layouts ret stmts) /\
  source_declaration_body_remainder tops (VariableDecl vis mut name ty slot) = T /\
  source_declaration_body_remainder tops (HashMapDecl vis trans name kt vt slot) = T /\
  source_declaration_body_remainder tops (StructDecl name fields) = T /\
  source_declaration_body_remainder tops (EventDecl name fields) = T /\
  source_declaration_body_remainder tops (InterfaceDecl name methods) = T /\
  source_declaration_body_remainder tops (FlagDecl name members) = F /\
  source_declaration_body_remainder tops (ErrorDecl name fields) = F
End

Definition source_program_remainder_def:
  source_program_remainder tops <=>
    supported_declaration_headers tops /\ supported_declaration_names tops /\
    EVERY (source_declaration_body_remainder tops) tops
End

(* Genuine checker environment, including the sequentially extended local
   environments inside type_stmts and the separate defaults environment. *)
Theorem checked_function_body_and_defaults:
  check_contract T layouts address mods = SOME art /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
  IS_SOME (type_stmts (function_entry_env art mods src args) ret stmts) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src args)) defaults
Proof
  strip_tac >> gvs[check_contract_def] >>
  `check_module T layouts address mods
     (build_contract_type_artifact T mods) (src,tops)` by fs[EVERY_MEM] >>
  fs[check_module_def, EVERY_MEM] >>
  `check_toplevel_body T layouts address mods
     (build_contract_type_artifact T mods) src
     (FunctionDecl vis mut nr rr name args defaults ret stmts)` by metis_tac[] >>
  fs[check_toplevel_body_def, check_function_body_in_mode_def,
     check_function_body_def]
QED

Theorem checked_function_defaults_remainder:
  check_contract T layouts address mods = SOME art /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
  (source_pure_exprs_remainder tops defaults <=> supported_pure_exprs tops defaults)
Proof
  strip_tac >> drule_all checked_function_body_and_defaults >> strip_tac >>
  drule (CONJUNCT1 (CONJUNCT2 checked_pure_remainder)) >> simp[]
QED

Theorem checked_function_body_remainder:
  IS_SOME (type_stmts env ret stmts) ==>
  (source_function_body_remainder tops vis args stmts <=>
   supported_function_body tops vis args stmts)
Proof
  strip_tac >> drule (CONJUNCT2 checked_stmt_remainder) >> strip_tac >>
  simp[source_function_body_remainder_def, supported_function_body_def]
QED

(* Restrict this body-only comparison to admitted headers. In particular,
   ErrorDecl is rejected by both program predicates' shared header gate;
   supported_declaration_body has no equation for that constructor. *)
Theorem checked_declaration_body_remainder:
  check_contract T layouts address mods = SOME art /\
  MEM (src,tops) mods /\ MEM top tops /\
  supported_declaration_header tops top ==>
  (source_declaration_body_remainder tops top <=> supported_declaration_body tops top)
Proof
  Cases_on `top` >>
  simp[source_declaration_body_remainder_def, supported_declaration_body_def,
       supported_declaration_header_def] >>
  strip_tac >> drule_all checked_function_body_and_defaults >> strip_tac >>
  drule checked_function_body_remainder >> simp[]
QED

Theorem checked_program_remainder:
  check_contract T layouts address mods = SOME art /\ MEM (src,tops) mods ==>
  (source_program_remainder tops <=> supported_program tops)
Proof
  strip_tac >>
  simp[source_program_remainder_def, supported_program_def,
       supported_declaration_headers_def, EVERY_MEM] >>
  `!top. MEM top tops /\ supported_declaration_header tops top ==>
    (source_declaration_body_remainder tops top <=> supported_declaration_body tops top)`
    by (rpt strip_tac >> irule checked_declaration_body_remainder >>
        metis_tac[]) >>
  metis_tac[]
QED

Theorem checked_remainder_supported_program:
  check_contract T layouts address [(NONE,tops)] = SOME art /\
  source_program_remainder tops ==> supported_program tops
Proof
  metis_tac[checked_program_remainder, MEM]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source program support kernel audit: " ^ name) end)
  (DB.thms "sourceProgramSupport");
