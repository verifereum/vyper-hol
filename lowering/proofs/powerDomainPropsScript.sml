(* Power lowering domain follows from genuine typing, not supported forms or
   frontend provenance. The unchecked lowering fallback remains unchanged.
   TOP-LEVEL: well_typed_power_lowering_literal/no_dynamic_fallback,
   well_typed_power_supported_operands/form, checked exponent bounds for
   expressions and AugAssign, and checker counterexamples for shifts.
   This theory has no execution/simulation certificate dependency. Whole-program
   simulation now states its optional power certification premise explicitly. *)
Theory powerDomainProps
Ancestors
  vyperTypeSystem exprLowering supportedExprForms
  vyperValueOperation vyperValue vyperAST words integer_word intBits
Libs
  wordsLib

Theorem expr_int_literal_some:
  expr_int_literal e = SOME n <=> ?ty. e = Literal ty (IntL n)
Proof
  Cases_on `e` >> simp[expr_int_literal_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >> simp[expr_int_literal_def]
QED

Theorem well_typed_power_lowering_literal:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  IS_SOME (expr_int_literal base_e) \/ IS_SOME (expr_int_literal exponent)
Proof
  strip_tac >> drule well_typed_power_has_integer_literal >>
  rw[] >> simp[expr_int_literal_def]
QED

(* The whitelist's power operand condition is a consequence of checking.
   This fact alone does not certify the arithmetic simulation. *)
Theorem well_typed_power_supported_operands:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  supported_integer_literal base_e \/ supported_nonnegative_literal exponent
Proof
  strip_tac >> drule well_typed_power_operands >>
  simp[power_operands_ok_def, integer_literal_expr_cases,
       power_exponent_ok_cases] >>
  rw[] >> simp[supported_integer_literal_def, supported_nonnegative_literal_def]
QED

Theorem well_typed_power_supported_form:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  (supported_builtin_form tops ty (Bop Exp) [base_e; exponent] <=>
   supported_integer_type (expr_type base_e))
Proof
  strip_tac >> drule well_typed_power_supported_operands >>
  simp[supported_builtin_form_def, supported_binop_def]
QED

Theorem well_typed_power_no_dynamic_fallback:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  ~(expr_int_literal base_e = NONE /\ expr_int_literal exponent = NONE)
Proof
  strip_tac >> drule well_typed_power_lowering_literal >>
  Cases_on `expr_int_literal base_e` >> Cases_on `expr_int_literal exponent` >> simp[]
QED

Theorem well_typed_power_lowering_exponent_nonnegative:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) /\
  expr_int_literal exponent = SOME n ==> 0 <= n
Proof
  simp[expr_int_literal_some] >> rpt strip_tac >> gvs[] >>
  drule well_typed_power_literal_exponent_nonnegative >> simp[]
QED

(* Shifts are not covered by the power checker repair.  In particular it
   would be unsound to remove their width/nonnegative-count gates. *)
Theorem checker_admits_negative_shift:
  well_typed_expr env (Builtin (BaseT (IntT 256)) (Bop ShL)
    [Literal (BaseT (IntT 256)) (IntL 1);
     Literal (BaseT (IntT 256)) (IntL (-1))]) /\
  evaluate_binop (Signed 256) tv ShL (IntV 1) (IntV (-1)) =
    INR (RuntimeError "ShL0") /\
  ~supported_binop ShL (BaseT (IntT 256)) (BaseT (IntT 256)) F F
Proof
  rpt conj_tac >>
  simp[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
       evaluate_type_def, well_typed_builtin_app_def, well_typed_binop_def,
       builtin_operands_ok_def, within_int_bound_def, expr_type_def,
       evaluate_binop_def, supported_binop_def, supported_unsigned_type_def]
QED

Theorem checker_admits_untruncated_narrow_shift:
  well_typed_expr env (Builtin (BaseT (UintT 8)) (Bop ShL)
    [Literal (BaseT (UintT 8)) (IntL 128);
     Literal (BaseT (UintT 8)) (IntL 1)]) /\
  evaluate_binop (Unsigned 8) tv ShL (IntV 128) (IntV 1) = INL (IntV 0) /\
  compile_binop ShL x y (BaseT (UintT 8)) NONE NONE = emit_op SHL [y; x] /\
  word_lsl (128w : bytes32) 1 = 256w /\
  ~supported_binop ShL (BaseT (UintT 8)) (BaseT (UintT 8)) F F
Proof
  rpt conj_tac >>
  simp[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
       evaluate_type_def, well_typed_builtin_app_def, well_typed_binop_def,
       builtin_operands_ok_def, within_int_bound_def, expr_type_def,
       evaluate_binop_def, supported_binop_def, compile_binop_def,
       word_lsl_n2w]
  >- (mp_tac (Q.SPECL [`1`, `128`]
        (INST_TYPE [alpha |-> ``:8``] i2w_int_shift_left)) >>
      disch_then (mp_tac o AP_TERM ``\w:word8. &w2n w : int``) >>
      simp[w2n_i2w, i2w_pos, word_lsl_n2w, w2n_n2w,
           dimword_def, EVAL ``dimindex (:8)``]) >>
  simp[EVAL ``dimindex (:256)``]
QED

Theorem well_typed_power_lowering_bounded_exponent:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) /\
  expr_int_literal base_e = NONE ==>
  ?n. expr_int_literal exponent = SOME n /\
      0 <= n /\ Num n <= integer_value_bits ty
Proof
  strip_tac >>
  `~integer_literal_expr base_e` by
    (simp[integer_literal_expr_cases] >> rpt strip_tac >> gvs[expr_int_literal_def]) >>
  drule_all well_typed_power_nonliteral_base_exponent >>
  rw[] >> simp[expr_int_literal_def]
QED

Theorem well_typed_unsigned_power_info:
  well_typed_expr env (Builtin (BaseT (UintT bits)) (Bop Exp) [base_e; exponent]) ==>
  expr_type base_e = BaseT (UintT bits) /\
  expr_type exponent = BaseT (UintT bits) /\ 0 < bits /\ bits <= 256
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def, well_typed_binop_def,
       well_formed_type_def, evaluate_type_def] >>
  Cases_on `0 < bits /\ bits <= 256` >> simp[]
QED

(* Checking constrains a dynamic signed exponent's TYPE, not its value.
   In particular, it cannot justify a nonnegative runtime premise. *)
Theorem checker_admits_negative_runtime_power:
  FLOOKUP env.var_types "y" = SOME (BaseT (IntT 8)) ==>
  well_typed_expr env (Builtin (BaseT (IntT 8)) (Bop Exp)
    [Literal (BaseT (IntT 8)) (IntL 2); Name (BaseT (IntT 8)) "y"]) /\
  evaluate_binop (Signed 8) tv Exp (IntV 2) (IntV (-1)) =
    INR (RuntimeError "Exp~")
Proof
  simp[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
       evaluate_type_def, well_typed_builtin_app_def, well_typed_binop_def,
       builtin_operands_ok_def, power_operands_ok_def, integer_literal_expr_def,
       expr_type_def, within_int_bound_def, evaluate_binop_def]
QED

Theorem type_stmt_power_supported_exponent:
  type_stmt env ret_ty (AugAssign ty target Exp rhs) = SOME env' ==>
  supported_nonnegative_literal rhs
Proof
  strip_tac >> drule type_stmt_power_augassign_exponent >>
  rw[] >> simp[supported_nonnegative_literal_def]
QED

Theorem type_stmt_power_lowering_exponent:
  type_stmt env ret_ty (AugAssign ty target Exp rhs) = SOME env' ==>
  ?n. expr_int_literal rhs = SOME n /\
      0 <= n /\ Num n <= integer_value_bits ty
Proof
  strip_tac >> drule type_stmt_power_augassign_exponent >>
  rw[] >> simp[expr_int_literal_def]
QED

(* Audit only these independent domain/gate certificates. *)
val () = List.app (fn thy =>
  List.app (fn (name, th) =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail ("power proof audit failed: " ^ thy ^ "." ^ name)
    end) (DB.thms thy))
  ["powerDomainProps"];
