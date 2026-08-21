Theory vyperSmallStepApplyValOld
Ancestors
  arithmetic combin pair list While
  vyperMisc vyperValue vyperContext vyperState vyperInterpreter vyperABI
  vyperSmallStep
Libs

Definition apply_val_old_fr_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx (BoolV T) st (AssertK _ k) = apply cx st k ∧
  apply_val cx (BoolV F) st (AssertK AssertBare k) =
    apply_exc cx (AssertException "") st k ∧
  apply_val cx (BoolV F) st (AssertK AssertUnreachable k) =
    apply_exc cx (AssertException "UNREACHABLE") st k ∧
  apply_val cx (BoolV F) st (AssertK (AssertReason se) k) =
    eval_expr_cps cx se st (RaiseK k) ∧
  apply_val cx _ st (AssertK _ k) = apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val cx (StringV str) st (RaiseK k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val cx _ st (RaiseK k) =
    apply_exc cx (Error (TypeError "not StringV")) st k ∧
  apply_val cx v st (AnnAssignK id tyv k) =
    liftk cx (K Apply) (new_variable id tyv v st) k ∧
  apply_val cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val cx v st (AugAssignK1 ty (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st) k ∧
  apply_val cx v st (AppendK1 (loc, sbs) k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (AppendOp v) st) k ∧
  apply_val cx v st (ArrayK arr_typ k) =
    (case evaluate_type (get_tenv cx) arr_typ of
     | SOME arr_tv =>
         liftk cx ApplyVals
           (lift_option_type (extract_elements arr_tv v) "For not ArrayV" st) k
     | NONE => AK cx (ApplyExc (Error (TypeError "For array type"))) st k) ∧
  apply_val cx v st (RangeK1 e k) = eval_expr_cps cx e st (RangeK2 v k) ∧
  apply_val cx v2 st (RangeK2 v1 k) =
    (case do rl <- lift_sum $ get_range_limits v1 v2;
             n1 <<- FST rl; n2 <<- SND rl;
             return $ GENLIST (λn. IntV (n1 + &n)) n2
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k) ∧
  apply_val cx v st (SubscriptTargetK1 (loc, sbs) k) =
    AK cx (ApplyBaseTarget (loc, ValueSubscript v :: sbs)) st k ∧
  apply_val cx (BoolV T) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e2 st k ∧
  apply_val cx (BoolV F) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e3 st k ∧
  apply_val cx v st (IfExpK _ _ k) =
    apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val cx v2 st (SubscriptK1 arr_typ tv1 k) =
    liftk cx ApplyTv (do
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv arr_typ)
                  "Subscript array type";
      check_array_bounds cx tv1 v2;
      res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
       case res of INL v => return v | INR (is_transient, slot, tv) => do
         v <- read_storage_slot cx is_transient slot tv;
         return $ Value v
       od
    od st) k ∧
  apply_val cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val cx v st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_val k")) st DoneK
End

(* ===== Legacy apply_val definition and equivalence proof =====

   TOP-LEVEL API:
     apply_val_old_def        - the pre-restructure clause structure
     apply_val_old_eq         - apply_val_old = apply_val (pointwise)

   apply_val in vyperSmallStepTheory was restructured for build speed:
   - top-level patterns now appear only on the continuation argument; the
     value dispatch (BoolV T/F, StringV str) moved into nested case
     expressions (AssertK / RaiseK / IfExpK clauses),
   - the ArrayK / RangeK2 / SubscriptK1 do-blocks were extracted into the
     helpers apply_val_array / apply_val_range2 / apply_val_subscript.

   This theory preserves the original multi-argument-pattern definition as
   apply_val_old and proves it extensionally equal to the current apply_val.
   Helper: apply_val_old_<constructor>_eq for the three nested-case clauses. *)

Definition apply_val_old_def:
  apply_val_old cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val_old cx (BoolV T) st (AssertK _ k) = apply cx st k ∧
  apply_val_old cx (BoolV F) st (AssertK AssertBare k) =
    apply_exc cx (AssertException "") st k ∧
  apply_val_old cx (BoolV F) st (AssertK AssertUnreachable k) =
    apply_exc cx (AssertException "UNREACHABLE") st k ∧
  apply_val_old cx (BoolV F) st (AssertK (AssertReason se) k) =
    eval_expr_cps cx se st (RaiseK k) ∧
  apply_val_old cx _ st (AssertK _ k) =
    apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val_old cx (StringV str) st (RaiseK k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val_old cx _ st (RaiseK k) =
    apply_exc cx (Error (TypeError "not StringV")) st k ∧
  apply_val_old cx v st (AnnAssignK id tyv k) =
    liftk cx (K Apply) (new_variable id tyv v st) k ∧
  apply_val_old cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val_old cx v st (AugAssignK1 ty (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st) k ∧
  apply_val_old cx v st (AppendK1 (loc, sbs) k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (AppendOp v) st) k ∧
  apply_val_old cx v st (ArrayK arr_typ k) =
    (case evaluate_type (get_tenv cx) arr_typ of
     | SOME arr_tv =>
         liftk cx ApplyVals
           (lift_option_type (extract_elements arr_tv v) "For not ArrayV" st) k
     | NONE => AK cx (ApplyExc (Error (TypeError "For array type"))) st k) ∧
  apply_val_old cx v st (RangeK1 e k) = eval_expr_cps cx e st (RangeK2 v k) ∧
  apply_val_old cx v2 st (RangeK2 v1 k) =
    (case do rl <- lift_sum $ get_range_limits v1 v2;
             n1 <<- FST rl; n2 <<- SND rl;
             return $ GENLIST (λn. IntV (n1 + &n)) n2
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k) ∧
  apply_val_old cx v st (SubscriptTargetK1 (loc, sbs) k) =
    AK cx (ApplyBaseTarget (loc, ValueSubscript v :: sbs)) st k ∧
  apply_val_old cx (BoolV T) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e2 st k ∧
  apply_val_old cx (BoolV F) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e3 st k ∧
  apply_val_old cx v st (IfExpK _ _ k) =
    apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val_old cx v2 st (SubscriptK1 arr_typ tv1 k) =
    liftk cx ApplyTv (do
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv arr_typ)
                  "Subscript array type";
      check_array_bounds cx tv1 v2;
      res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
       case res of INL v => return v | INR (is_transient, slot, tv) => do
         v <- read_storage_slot cx is_transient slot tv;
         return $ Value v
       od
    od st) k ∧
  apply_val_old cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val_old cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val_old cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val_old cx v st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_val k")) st DoneK
End

(* Helper: AssertK clause - value dispatch agrees with nested case *)
Theorem apply_val_old_AssertK_eq:
  ∀cx v st r k.
    apply_val_old cx v st (AssertK r k) = apply_val cx v st (AssertK r k)
Proof
  rpt gen_tac
  \\ Cases_on `v` \\ TRY (rename1 `BoolV b` \\ Cases_on `b`)
  \\ Cases_on `r`
  \\ fs[apply_val_def, apply_val_old_def]
QED

(* Helper: RaiseK clause - value dispatch agrees with nested case *)
Theorem apply_val_old_RaiseK_eq:
  ∀cx v st k.
    apply_val_old cx v st (RaiseK k) = apply_val cx v st (RaiseK k)
Proof
  rpt gen_tac \\ Cases_on `v`
  \\ fs[apply_val_def, apply_val_old_def]
QED

(* Helper: IfExpK clause - value dispatch agrees with nested case *)
Theorem apply_val_old_IfExpK_eq:
  ∀cx v st e2 e3 k.
    apply_val_old cx v st (IfExpK e2 e3 k) = apply_val cx v st (IfExpK e2 e3 k)
Proof
  rpt gen_tac
  \\ Cases_on `v` \\ TRY (rename1 `BoolV b` \\ Cases_on `b`)
  \\ fs[apply_val_def, apply_val_old_def]
QED

(* KEY LEMMA: the legacy definition equals the restructured definition *)
Theorem apply_val_old_eq:
  ∀cx v st k. apply_val_old cx v st k = apply_val cx v st k
Proof
  rpt gen_tac \\ Cases_on `k`
  (* split the pair-typed continuation payloads so the (loc, sbs)
     pattern clauses of both definitions can fire *)
  \\ TRY (qmatch_goalsub_rename_tac `AppendK1 pr e` \\ Cases_on `pr`)
  \\ TRY (qmatch_goalsub_rename_tac `AugAssignK1 tyv pr b e` \\ Cases_on `pr`)
  \\ TRY (qmatch_goalsub_rename_tac `SubscriptTargetK1 pr e` \\ Cases_on `pr`)
  \\ rw[apply_val_old_AssertK_eq, apply_val_old_RaiseK_eq, apply_val_old_IfExpK_eq]
  \\ rw[apply_val_old_def, apply_val_def,
        apply_val_array_def, apply_val_range2_def, apply_val_subscript_def]
QED
