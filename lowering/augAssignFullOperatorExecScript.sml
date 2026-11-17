(* Actual typed AugAssign operator execution, at the supplied machine state. *)
Theory augAssignFullOperatorExec
Ancestors
  bodyPtrBopScalarRun augAssignFullOperatorIntegerExec
  augAssignFullOperatorPowerExec augAssignFullOperatorWordExec
  exprBopBytes exprSimSource exprSimProps loweringPosts valueEncoding
  exprSimHypsDefs vyperTypeSystem exprSimBinopFrag

Theorem augassign_numeric_execution:
  !cx ty bop t2 bl el tys v1 v2 es tv1 tv2 x y sa sb op s.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
    type_bits ty MOD 8 = 0 /\
    (bop = Exp ==>
      (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
      (!n. bl = SOME n ==> v1 = IntV n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    word_value_type ty /\ word_value_type t2 /\
    evaluate_type (get_tenv cx) ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ty bop tys v1 v2 es) /\
    compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
    (!z. x = Var z ==> not_fresh_at sa z) /\
    (!z. y = Var z ==> not_fresh_at sa z) /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ty bop tys v1 v2 es = INL v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\ expr_val_rel cx ty v op t) \/
    (?m t. bop_result cx ty bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_word_typed_run >> strip_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >>
      qexists_tac `v` >> simp[expr_val_rel_def, typed_val_to_w256_word_value,
                             word_value_type_word]) >>
  disj2_tac >> metis_tac[]
QED

Theorem augassign_typed_execution:
  !cx ty bop t2 bl el tys v1 v2 es tv1 tv2 x y sa sb op s.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
    type_bits ty MOD 8 = 0 /\
    (bop = Exp ==>
      (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
      (!n. bl = SOME n ==> v1 = IntV n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==>
      (?i. v2 = IntV i /\ 0 <= i) \/
      (ty = BaseT (BytesT (Fixed 32)) /\ ?bs. v2 = BytesV bs /\ LENGTH bs = 32)) /\
    evaluate_type (get_tenv cx) ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ty bop tys v1 v2 es) /\
    compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
    (!z. x = Var z ==> not_fresh_at sa z) /\
    (!z. y = Var z ==> not_fresh_at sa z) /\
    eval_operand x s = SOME (typed_val_to_w256 tv1 v1) /\
    eval_operand y s = SOME (typed_val_to_w256 tv2 v2) ==>
    (?v t. bop_result cx ty bop tys v1 v2 es = INL v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\ expr_val_rel cx ty v op t) \/
    (?m t. bop_result cx ty bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all well_typed_binop_augassign_word >> strip_tac
  >- (`word_value v1 /\ word_value v2` by metis_tac[word_value_type_typed] >>
      `eval_operand x s = SOME (val_to_w256 v1) /\
       eval_operand y s = SOME (val_to_w256 v2)` by
        gvs[typed_val_to_w256_word_value] >>
      `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
        (rpt strip_tac >> gvs[word_value_type_def]) >>
      drule_all augassign_numeric_execution >> simp[]) >>
  qpat_x_assum `ty = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
  `(bop = ShL \/ bop = ShR ==> (?i. v2 = IntV i /\ 0 <= i) \/
     t2 = BaseT (BytesT (Fixed 32)))` by
    (rpt strip_tac >> (Cases_on `t2 = BaseT (BytesT (Fixed 32))` >- simp[] >>
     `is_int_type t2` by gvs[well_typed_binop_def] >>
     drule_all int_type_value >> strip_tac >> gvs[])) >>
  disj1_tac >> drule_all compile_bytes_binop_run >> simp[]
QED
