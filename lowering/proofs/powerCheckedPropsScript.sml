(* Checked-AST provenance and complete safe_pow execution. No supported-form
   gate or literal normalisation premise is assumed by the public theorem. *)
Theory powerCheckedProps
Ancestors
  powerPositiveRunProps powerTypedRunProps powerRunProps
  exprLowering compileEnv emitHelperProps venomExecSemantics venomState
  vyperTypeSystem vyperInterpreter vyperState vyperValueOperation vyperValue vyperAST
  words integer_word integer arithmetic
Libs
  wordsLib

Theorem power_literal_value:
  expr_int_literal e = SOME n /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL (IntV a),es') ==> a = n
Proof
  Cases_on `e` >> simp[expr_int_literal_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >>
  simp[expr_int_literal_def, Once evaluate_def, return_def, evaluate_literal_def,
       bind_def, read_result_def] >> rw[]
QED

Theorem power_checked_integer_info:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  expr_type base_e = ty /\ expr_type exponent = ty /\
  ?signed bits. ty = (if signed then BaseT (IntT bits) else BaseT (UintT bits)) /\
               (if signed then 1 < bits else 0 < bits) /\ bits <= 256
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def, well_typed_binop_def] >>
  strip_tac >> Cases_on `ty` >> gvs[is_int_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_int_type_def, well_formed_type_def, evaluate_type_def] >>
  FIRST [
    qmatch_goalsub_rename_tac `UintT width` >>
    qexistsl_tac [`F`, `width`] >> simp[] >>
    Cases_on `0 < width /\ width <= 256` >> gvs[],
    qmatch_goalsub_rename_tac `IntT width` >>
    qexistsl_tac [`T`, `width`] >> simp[] >>
    Cases_on `1 < width /\ width <= 256` >> gvs[]]
QED

Theorem power_typed_run:
  compile_safe_pow x y (if signed then BaseT (IntT bits) else BaseT (UintT bits))
    bl el st = (op,st') /\
  (if signed then 1 < bits else 0 < bits) /\ bits <= 256 /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a /\
  within_int_bound (if signed then Signed bits else Unsigned bits) e /\
  (bl = SOME a \/ (bl = NONE /\ el = SOME e /\ 0 <= e)) /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (i2w e) /\
  fresh_vars_wrt st ss ==>
  (0 <= e /\ within_int_bound (if signed then Signed bits else Unsigned bits)
      (a ** Num e) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w (a ** Num e))) /\
  (e < 0 \/ ~within_int_bound (if signed then Signed bits else Unsigned bits)
      (a ** Num e) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `0 <= e`
  >- (`?n. e = &n` by (irule NUM_POSINT_EXISTS >> simp[]) >> gvs[i2w_pos] >>
      `n < dimword (:256)` by
        (mp_tac (Q.INST [`signed` |-> `signed`, `bits` |-> `bits`, `e` |-> `&n`]
          power_nonnegative_word_bound) >> simp[]) >>
      (
        `n < dimword (:256)` by simp[dimword_def, EVAL ``dimindex (:256)``] >>
        FIRST [drule_all compile_safe_pow_typed_base_run,
               drule_all compile_safe_pow_typed_exponent_run] >>
        simp[] >> metis_tac[])) >>
  `e < 0` by fs[INT_NOT_LE] >>
  `signed` by (Cases_on `signed` >> gvs[within_int_bound_def]) >>
  `bl = SOME a` by (qpat_x_assum `bl = SOME a \/ _` strip_assume_tac >> gvs[]) >>
  gvs[] >> drule_all compile_safe_pow_negative_run >> simp[]
QED

(* All literal options are extracted from the SAME checked expression that
   supplied the forced operand evaluations (including reads of places).
   Operand bounds are ordinary runtime
   typing, not additional restrictions on source programs. *)
Theorem checked_power_run:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) /\
  (do r <- eval_expr cx base_e; read_result cx r od) es = (INL (IntV a),es1) /\
  (do r <- eval_expr cx exponent; read_result cx r od) es1 = (INL (IntV e),es2) /\
  within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                    else Unsigned (type_bits ty)) a /\
  within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                    else Unsigned (type_bits ty)) e /\
  compile_binop Exp x y (expr_type base_e)
    (expr_int_literal base_e) (expr_int_literal exponent) st = (op,st') /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (i2w e) /\
  fresh_vars_wrt st ss ==>
  let u = if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty) in
  evaluate_binop u tv Exp (IntV a) (IntV e) =
    (if e < 0 then INR (RuntimeError "Exp~")
     else if within_int_bound u (a ** Num e) then INL (IntV (a ** Num e))
     else INR (RuntimeError "bounded_int_op bound")) /\
  (0 <= e /\ within_int_bound u (a ** Num e) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (i2w (a ** Num e))) /\
  (e < 0 \/ ~within_int_bound u (a ** Num e) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> drule power_checked_integer_info >> strip_tac >>
  `expr_int_literal base_e = SOME a \/
    (expr_int_literal base_e = NONE /\ expr_int_literal exponent = SOME e /\ 0 <= e)` by
    (Cases_on `expr_int_literal base_e`
     >- (drule well_typed_power_has_integer_literal >> strip_tac >>
         gvs[expr_int_literal_def, Once evaluate_def, return_def,
             evaluate_literal_def, bind_def, read_result_def] >>
         drule well_typed_power_literal_exponent_nonnegative >> simp[]) >>
     drule_all power_literal_value >> simp[]) >>
  simp[evaluate_binop_def, bounded_int_op_def] >>
  mp_tac (Q.INST [`bl` |-> `expr_int_literal base_e`,
                   `el` |-> `expr_int_literal exponent`] power_typed_run) >>
  Cases_on `signed` >>
  gvs[compile_binop_def, type_bits_def, is_signed_type_def] >> metis_tac[]
QED

val () = List.app (fn thy => List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null (Thm.hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("power certificate audit: " ^ thy ^ "." ^ name) end)
  (DB.thms thy))
  ["powerGuardProps", "powerSignedExponentProps", "powerSmallProps",
   "powerEndpointProps", "powerTypedRunProps", "powerPositiveRunProps", "powerCheckedProps"];
