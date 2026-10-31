(*
 * Assignment-target context and assignment-operation bridge lemmas.
 *)

Theory vyperTypeAssignContext
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeGlobalLookupSoundness
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib


Theorem well_typed_expr_Pop_dynamic_target:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n)))
Proof
  simp[Once well_typed_expr_def] >> metis_tac[]
QED

Theorem well_typed_expr_Pop_dynamic_target_assignable:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n))) /\
        assignable_type env.type_defs (ArrayT ty (Dynamic n))
Proof
  simp[Once well_typed_expr_def]
QED
