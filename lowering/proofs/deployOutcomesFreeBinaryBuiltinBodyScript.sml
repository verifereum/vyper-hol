Theory deployOutcomesFreeBinaryBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list

Theorem outcomes_free_builtin_keccak:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_bytes v st))) /\
  (!v m st. Q st ==> Q (SND (compile_keccak256_bytesm v m st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_word v st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty Keccak256 (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty Keccak256 args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `is_bytestring_type (expr_type (HD args))`
  >- (simp[] >> pairarg_tac >> simp[outcomes_free_as_stack_val] >>
      metis_tac[pairTheory.SND]) >>
  simp[] >> Cases_on `expr_type (HD args)` >>
  simp[] >> rpt (CASE_TAC >> simp[]) >>
  pairarg_tac >> simp[outcomes_free_as_stack_val] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_literal_or_hash:
  (!st. Q st ==> Q (SND (lower_value f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_hash v st))) /\ Q s ==>
  Q (SND (case bytestring_literal_hash e of
    SOME h => (Lit h, s)
  | NONE => (\(m, st). compile_bytestring_hash m st)
              (lower_value f ce ity e s)))
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e` >> simp[] >>
  pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_builtin_binary:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!es st. EVERY (\e. well_typed_expr env e /\
      ~supported_expr_exists constructor_call_root e) es /\ Q st ==>
      Q (SND (compile_multi_exprs f ce es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_in v es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_notin v es st))) /\
  (!v arr ity flag st. Q st ==>
      Q (SND (compile_var_array_membership ce v arr ity flag st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_hash v st))) /\
  (!ops st. Q st ==> Q (SND (emit_op EQ ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))) /\
  (!op v w ity a b st. Q st ==> Q (SND (compile_binop op v w ity a b st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty (Bop op) (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty (Bop op) args s))
Proof
  strip_tac >>
  `EVERY (\e. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e) args` by
    metis_tac[outcomes_free_typed_children] >>
  drule_all outcomes_free_binary_selectors >> strip_tac >>
  `!e ity st. (e = HD args \/ e = HD (TL args)) /\ Q st ==>
    Q (SND (lower_value f ce ity e st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >>
     gvs[]) >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
  >- (simp[] >> pairarg_tac >> simp[] >>
      `Q st1` by metis_tac[pairTheory.SND] >>
      Cases_on `HD (TL args)` >> simp[]
      >~ [`HD (TL args) = Builtin bty b es`]
      >- (Cases_on `b` >> simp[]
          >~ [`MakeArray a n`] >-
            (`EVERY (\e. well_typed_expr env e /\
                ~supported_expr_exists constructor_call_root e) es` by
               (gvs[] >> metis_tac[outcomes_free_make_array_children]) >>
             pairarg_tac >> simp[] >>
             `Q st2` by metis_tac[pairTheory.SND] >>
             Cases_on `op = In` >> simp[outcomes_free_as_stack_val]) >>
          pairarg_tac >> simp[outcomes_free_as_stack_val] >>
          fs[] >> metis_tac[pairTheory.SND]) >>
      pairarg_tac >> simp[outcomes_free_as_stack_val] >>
      fs[] >> metis_tac[pairTheory.SND]) >>
  simp[] >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)`
  >- (`!e ity st. (e = HD args \/ e = HD (TL args)) /\ Q st ==>
        Q (SND (case bytestring_literal_hash e of
          SOME h => (Lit h, st)
        | NONE => (\(m, st'). compile_bytestring_hash m st')
                    (lower_value f ce ity e st)))` by
        (rpt strip_tac >> irule outcomes_free_literal_or_hash >> simp[]) >>
      simp[] >> pairarg_tac >> simp[] >>
      `Q st2` by metis_tac[pairTheory.SND] >>
      pairarg_tac >> simp[] >>
      `Q st4` by metis_tac[pairTheory.SND] >>
      Cases_on `op = Eq` >> simp[outcomes_free_as_stack_val] >>
      pairarg_tac >> simp[outcomes_free_as_stack_val] >>
      metis_tac[pairTheory.SND]) >>
  simp[] >> ntac 2 (pairarg_tac >> simp[outcomes_free_as_stack_val]) >>
  metis_tac[pairTheory.SND]
QED
