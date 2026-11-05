Theory bodyPtrBytestringBuiltinsOperands
Ancestors
  bodyPtrBytestringBuiltinsInterfaces bodyPtrEnvBuiltins exprSimPtr
  exprSimSource vyperTypeCallGraph bodyPtrPreds

(* Uses the inherited leaf_expr_sim_ptr and env_builtin_expr_ptr_ok
   admissions, independently of all Slice case theorems. *)
Theorem bytestring_leaf_body_ptr:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_ptr_ok cx e
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env e es` by
    (simp[expr_sim_pre_body] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[int_calls_expr_def]) >>
  metis_tac[leaf_expr_sim_ptr]
QED

Theorem order_probe_operands_ptr:
  !cx. body_exprs_ptr_ok cx
    [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
       [Pop (BaseT AddressT) (NameTarget "arr")];
     Builtin (BaseT (UintT 256)) Len
       [Name (ArrayT (BaseT AddressT) (Dynamic 2)) "arr"];
     Literal (BaseT (UintT 256)) (IntL 1)]
Proof
  gen_tac >>
  simp[body_exprs_ptr_ok_def, acc_code_body_ptr_vacuous] >>
  rpt strip_tac
  >- (irule env_builtin_expr_ptr_ok >> simp[] >> rpt strip_tac >>
      irule bytestring_leaf_body_ptr >> simp[]) >>
  irule bytestring_leaf_body_ptr >> simp[]
QED

Theorem order_probe_slice_arity:
  builtin_args_length_ok (Slice 1) 3
Proof
  EVAL_TAC
QED
