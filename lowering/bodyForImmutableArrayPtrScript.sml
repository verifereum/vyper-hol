Theory bodyForImmutableArrayPtr
Ancestors forPtrArrayFrag bodyPtrPreds bodyPtrDefs bodySimDeclCases
  stmtSimForArray exprSimHypsDefs exprSimHyps bodySim bodyExprPreFacts
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues
  supportedStmts supportedStmtTraverse allocLimits compileVyper
  vyperTypeCallGraph exprLoweringProps finite_map list vyperTypeCallStackSoundness
  whitelistForIterImmSource whitelistForIterImmLoop whitelistForIterImmFrame immutableLoadPtr immutableCopyWordsPtr
Libs monadsyntax

val _ = Parse.hide "body";

Theorem body_for_immutable_array_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name))) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_ptr_ok cx (Array (TopLevelName (ArrayT typ bd) (src,name)))) ==>
  body_stmt_ptr_ok cx (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n body)
Proof
  rw[body_stmt_ptr_ok_def]
QED

