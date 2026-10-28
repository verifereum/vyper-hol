Theory sourceMeaningProgramDefs
Ancestors
  sourceMeaningStmtDefs sourceMeaningEnv sourceMeaningConst sourceModuleDecl sourceModuleEnv
  sourceResolveModules sourceResolve sourceSyntax sourceConstEnv vyperState alist list

(* Program constant denotation is specified from ORIGINAL declarations and
   original initializer syntax. It does not run dependency elaboration. *)
Definition source_meaning_constants_def:
  source_meaning_constants registry constants <=>
    (?declarations. source_resolve_registry_declarations registry = SOME declarations /\
      source_meaning_declarations [] declarations constants) /\
    !owner syntax path original.
      MEM (owner,syntax) registry /\
      MEM (path,original) (source_resolve_initializers owner syntax) ==>
      ?resolved value.
        source_resolve_candidate
          [source_resolve_module_scope owner syntax; source_resolve_prelude_scope]
          (source_resolve_table registry) original = SOME resolved /\
        ALOOKUP constants path = SOME (SC_Constant value) /\
        source_meaning_const constants resolved = SC_Value value
End

(* A named source entry is selected from source declarations, not from emitted
   code. Source annotations/defaults/decorators remain retained. This partial
   execution starts at body entry with parameter cells already installed; it
   does NOT model dispatch, ABI decoding, call-value checks or default staging.
   Deploy declarations are selectable by the same rules, without asserting
   whole-contract deployment/storage-initializer correctness. *)
Definition source_meaning_entry_def:
  source_meaning_entry program keys registry owner syntax declaration ctx types ret ms <=>
    source_resolve_program_registry program keys = SOME registry /\
    MEM (owner,syntax) registry /\
    MEM declaration (source_module_declarations syntax) /\
    ctx.sm_owner = owner /\
    ctx.sm_scopes = source_module_scopes owner syntax /\
    ctx.sm_table = source_resolve_table registry ++ source_module_extra_prelude /\
    source_meaning_constants registry ctx.sm_constants /\
    ?name decorators args defaults annotation body params next_types next.
      declaration = SD_Function name decorators args defaults annotation body /\
      source_module_args ctx args = SM_Ok params /\
      source_module_return_type ctx annotation = SM_Ok ret /\
      source_meaning_bodies types (source_module_function_context ctx name args params)
        ret body ms next_types next
End

Definition source_meaning_execute_def:
  source_meaning_execute cx ms =
    source_meaning_runs cx (\path. source_meaning_local (LAST path)) ms
End
