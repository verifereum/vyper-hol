(* Exhaustive syntax audit at compile_stmt's tuple staging boundary.
   This theory does not infer ownership from a false staging flag. *)
Theory tupleAssignImmutableDeployOrigins
Ancestors
  tupleAssignImmutableDeployAliasProbe supportedExprForms stmtLowering
  vyperAST vyperTypeSystem supportedExprs supportedStmts

(* Branch premises are kept at the supported-expression interface. In
   particular supported_scalar_type includes strings and dynamic bytes. *)
Theorem tuple_immutable_rhs_origins:
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_type e = TupleT tys /\ well_typed_expr env e ==>
  ((is_memory_view e /\
    ((?name. e = Name (TupleT tys) name) \/
     (?id. e = TopLevelName (TupleT tys) id /\
       (supported_storage_value tops id (TupleT tys) \/
        supported_immutable_type tops id = SOME (TupleT tys))) \/
     (?base key. e = Subscript (TupleT tys) base key /\
       supported_place_type tops (TupleT tys) /\
       supported_subscript_place tops base /\
       ((supported_place_expr tops base /\ supported_expr tops key) \/
        (supported_effect_place_expr tops base /\ supported_expr tops key))) \/
     (?base field. e = Attribute (TupleT tys) base field /\
       supported_place_type tops (TupleT tys) /\
       supported_field_place tops (expr_type base) field /\
       (supported_place_expr tops base \/ supported_effect_place_expr tops base)))) \/
   (~is_memory_view e /\
    ((?blt args. e = Builtin (TupleT tys) blt args /\
       supported_builtin_form tops (TupleT tys) blt args /\
       supported_pure_exprs tops args) \/
     (?blt target args. e = TypeBuiltin (TupleT tys) blt target args /\
       supported_type_builtin_form tops (TupleT tys) blt target args /\
       supported_pure_exprs tops args) \/
     (?id. e = Pop (TupleT tys) (TopLevelNameTarget id) /\
       supported_storage_dynamic_array tops id) \/
     (?target args. e = Call (TupleT tys) target args NONE /\
       supported_effect_expr tops (Call (TupleT tys) target args NONE)))))
Proof
  Cases_on `e` >>
  simp[expr_type_def] >> strip_tac >> gvs[]
  >~ [`supported_stmt tops bindings (Assign (TupleTarget gs) (IfExp _ _ _ _))`]
    >- metis_tac[tuple_immutable_alias_ifexp_excluded]
  >~ [`well_typed_expr env (Literal _ lit)`]
    >- (Cases_on `lit` >>
        gvs[well_typed_expr_def, well_typed_literal_def]) >>
  gvs[supportedStmtsTheory.supported_stmt_def,
      supportedStmtsTheory.supported_assignment_def,
      supportedExprsTheory.supported_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def,
      supported_struct_elements_def,
      stmtLoweringTheory.is_memory_view_def]
  >~ [`supported_effect_expr tops (Pop _ bt)`]
    >- (Cases_on `bt` >> gvs[supported_effect_expr_def]) >>
  rename1 `supported_effect_expr tops (Call _ target args default)` >>
  Cases_on `default` >> gvs[supported_call_default_rejected] >>
  Cases_on `target` >> gvs[supported_effect_expr_def]
QED

(* Source typing removes every scalar/array-returning builtin, including EC
   points (arrays, not tuples). This says nothing about word-only fields. *)
Theorem tuple_immutable_builtin_origin:
  well_typed_builtin_app (TupleT tys) blt ts ==>
  ?bd. blt = MakeArray NONE bd /\ tys = ts /\
       compatible_bound bd (LENGTH ts)
Proof
  Cases_on `blt` >> simp[well_typed_builtin_app_def] >>
  strip_tac >> gvs[]
  >~ [`well_typed_builtin_app _ (MakeArray elem bd) _`]
    >- (Cases_on `elem` >> gvs[well_typed_builtin_app_def])
  >~ [`well_typed_binop _ op _ _`]
    >- (Cases_on `op` >> gvs[well_typed_binop_def])
  >~ [`_ = env_item_type item`]
    >- (Cases_on `item` >> gvs[env_item_type_def]) >>
  Cases_on `a` >> gvs[account_item_type_def]
QED

Theorem tuple_immutable_call_origins:
  supportedExprs$supported_expr tops (Call (TupleT tys) target args default) ==>
  default = NONE /\
  ((?id. target = IntCall id /\
      IS_SOME (supported_function_decl tops id Internal) /\
      supported_pure_exprs tops args) \/
   (?static skip name argtys ret opts.
      target = ExtCall static skip (name,argtys,ret) opts /\
      EVERY supported_word_type argtys /\
      supported_external_return_type tops ret /\
      ALL_DISTINCT opts /\ (static ==> ~MEM EKValue opts) /\
      LENGTH args = 1 + LENGTH argtys + LENGTH opts /\
      supported_pure_exprs tops args))
Proof
  Cases_on `target` >> Cases_on `default` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
  >~ [`Send has_gas`]
    >- (Cases_on `has_gas` >>
        namedCases_on `args` ["", "a rest"] >> simp[supported_effect_expr_def] >>
        namedCases_on `rest` ["", "v rest2"] >> simp[supported_effect_expr_def] >>
        namedCases_on `rest2` ["", "g rest3"] >> simp[supported_effect_expr_def] >>
        Cases_on `rest3` >> simp[supported_effect_expr_def]) >>
  qmatch_goalsub_rename_tac `ExtCall static_call skip_check desc opts` >>
  PairCases_on `desc` >>
  simp[supported_effect_expr_def]
QED

Theorem tuple_immutable_type_builtin_origins:
  supported_type_builtin_form tops (TupleT tys) blt target args /\
  well_typed_expr env (TypeBuiltin (TupleT tys) blt target args) ==>
  blt = Empty \/ blt = AbiDecode F
Proof
  Cases_on `blt` >>
  gvs[supported_type_builtin_form_def, AllCaseEqs(),
      supported_numeric_type_def, supportedTypesTheory.supported_integer_type_def,
      well_typed_expr_def, type_builtin_result_ok_def, valid_conversion_def] >>
  namedCases_on `args` ["", "a rest"] >> simp[] >>
  Cases_on `rest` >> gvs[]
QED

(* Producer ledger for the checked syntax partition above.

   Actual staging guard (stmtLowering, compile_stmt TupleTarget) is
     is_memory_view e /\ vv_location src_vv = SOME LocMemory,
   after compile_expr and unwrap_value, not merely is_memory_view e.

   View cases: Name, TopLevelName, Subscript, Attribute.
     Memory results take the copying/staging path. The checked
     tuplePlaceSnapshot.tuple_place_stage_owned_probe establishes an owned
     snapshot for the allocation+MCOPY producer, subject to its explicit
     runtime, size, code-prefix and pointer premises. Connecting that probe
     to the actual caller and gas prefix is still required. Nonmemory
     locations go through unwrap_value; their copying/ownership connection
     must likewise be retained, not inferred from the view flag alone.

   Nonview cases (the guard is false regardless of vv_location):
   - Builtin: tuple_immutable_builtin_origin restricts typed results to
     MakeArray NONE. compile_builtin_dispatch_body allocates the sum of
     element sizes, then compile_make_tuple stores the heterogeneous fields
     into that buffer (exprLowering 3471-3479, 2223-2233).
   - TypeBuiltin: tuple_immutable_type_builtin_origins leaves Empty and
     AbiDecode F. Empty uses compile_builtin_empty_complex and returns its
     buffer (3526-3533). AbiDecode uses lower_abi_decode and returns a
     LocMemory pointer (3580-3590).
   - Call: tuple_immutable_call_origins leaves IntCall and ExtCall, with
     supported branch premises. IntCall allocates a return buffer when its
     function info requests one and returns that buffer (2778-2819).
     ExtCall uses compile_external_call_kwargs and returns its decoded
     memory result for a non-None return type (2820-2870).
   - Pop: the syntax partition conservatively retains a top-level storage
     dynamic-array pop. Its producer returns the element's location
     (3190-3207), not an owned allocation. Support restricts the declared
     array element to a fullword type. Excluding a tuple annotation here
     requires connecting source typing with that declaration using the full
     caller invariants; this audit has not proved that connection.

   Interface limitation, common to the nonview allocation cases:
   loweringPosts.expr_post gives expr_val_at, with expr_val_own only under
   post_value_type cenv e <> expr_type e (464-481). vv_post similarly gives
   vv_at and only conditional vv_own (652-670). Thus their same-layout
   instances do NOT supply the ownership theorem needed for pending tuple
   values. Compiler allocation paths above are implementation evidence,
   not substitute producer theorems. A producer ownership boundary, or an
   alternative pending-value preservation argument, remains necessary.
   Scalar tuple fields may include strings/dynamic bytes; no word-only
   shortcut is used. No reachable borrowed counterexample is established.
*)
