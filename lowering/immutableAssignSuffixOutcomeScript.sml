(* Compiler and statement outcome interfaces for ordinary immutable assignment. *)
Theory immutableAssignSuffixOutcome
Ancestors
  immutableAssignWordMem immutableAssignBytesMem immutableAssignFixedMem
  immutableAssignNormalizedMem immutableAssignState bodyImmutableAssignFacts
  stmtLowering exprLowering compileEnv context
Libs monadsyntax

Theorem immutable_assign_ordinary_code[local]:
  FLOOKUP ce.ce_module_vars nsid = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type nsid = SOME ity /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  compile_stmt ce lc ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
    (do vv <- compile_expr ce (expr_type e) e;
        op <- unwrap_value ce vv;
        compile_assign_value ce (Lit (n2w off)) LocCode op
          (is_word_type ity) (vv_location vv) ity (lowered_value_type ce e)
          (case ity of ArrayT elem (Dynamic _) =>
             SOME ((type_memory_bytes ce elem + 31) DIV 32,type_memory_bytes ce elem)
           | _ => NONE) (type_memory_bytes ce ity)
     od)
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  `!st. compile_get_target_ptr compile_expr ce (TopLevelNameTarget nsid) st =
    ((Lit (n2w off),SOME LocCode,SOME (ValPT ity)),st)` by
    (gen_tac >> irule immutable_assignment_target_lowering >> simp[]) >>
  simp[Once compile_stmt_def,expr_can_mutate_def,target_to_expr_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> simp[]
QED
