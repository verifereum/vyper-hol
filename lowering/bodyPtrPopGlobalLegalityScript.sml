Theory bodyPtrPopGlobalLegality
Ancestors
  bodyPtrPopStructLegality supportedProgram vyperTypeContract vyperValue

(* Diagnostic source program: global B supplies the replacement without
   relying on a nonexistent local binding in the zero-argument callee. *)
Definition pop_global_body_def:
  pop_global_body =
    [Assign (BaseTarget pop_struct_root) (TopLevelName pop_struct_ty (NONE,"B"));
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End
Definition pop_global_tops_def:
  pop_global_tops =
    [StructDecl "Box" pop_struct_fields;
     VariableDecl Private Storage "A" pop_struct_ty (SOME 0);
     VariableDecl Private Storage "B" pop_struct_ty (SOME 4);
     FunctionDecl Internal Nonpayable F F "replace" [] []
       (BaseT (UintT 256)) pop_global_body]
End
Definition pop_global_mods_def:
  pop_global_mods = [(NONE,pop_global_tops)]
End
Definition pop_global_art_def:
  pop_global_art = build_contract_type_artifact F pop_global_mods
End
Definition pop_global_env_def:
  pop_global_env = function_entry_env pop_global_art pop_global_mods NONE Internal []
End

Theorem pop_global_body_typing:
  IS_SOME (type_stmts pop_global_env (BaseT (UintT 256)) pop_global_body)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_callable_typing:
  !layouts addr.
  check_function_body layouts addr pop_global_mods pop_global_art NONE
    Internal Nonpayable F [] [] (BaseT (UintT 256)) pop_global_body
Proof
  rpt gen_tac >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_supported:
  supported_program pop_global_tops
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_mutability:
  function_mutability_ok pop_global_mods Internal Nonpayable F [] pop_global_body
Proof
  EVAL_TAC
QED

(* The selected expression pops the innermost dynamic array. *)
Definition pop_global_target_def:
  pop_global_target =
    SubscriptTarget
      (SubscriptTarget pop_struct_field (Literal (BaseT (UintT 256)) (IntL 0)))
      (Call (BaseT (UintT 256)) (IntCall (NONE,"replace")) [] NONE)
End

Theorem pop_global_expr_typing:
  well_typed_expr pop_global_env
    (Pop (BaseT (UintT 256)) pop_global_target)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >>
  qexists_tac `1` >> EVAL_TAC
QED

(* Current supported_expr only admits Pop on a top-level target. *)
Theorem pop_global_expr_unsupported:
  ~supported_expr pop_global_tops
    (Pop (BaseT (UintT 256)) pop_global_target)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED
