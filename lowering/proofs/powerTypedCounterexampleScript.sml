(* Regression for the repaired signed literal-exponent lower bound.
   IntT 9 remains in the raw checked domain: (-16)^2 must overflow. *)
Theory powerTypedCounterexample
Ancestors
  powerBoundProps exprLowering compileEnv emitHelper vyperTypeSystem
  vyperValueOperation vyperValue vyperAST venomExecSemantics venomState venomInst
  words integer_word finite_map list
Libs
  wordsLib

Theorem power_int9_square_bound:
  largest_pow_base 2 9 T = 15
Proof
  `15 <= largest_pow_base 2 9 T` by simp[largest_pow_base_characterisation] >>
  `~(16 <= largest_pow_base 2 9 T)` by simp[largest_pow_base_characterisation] >>
  decide_tac
QED

Theorem power_int9_square_typed_overflow:
  FLOOKUP env.var_types "x" = SOME (BaseT (IntT 9)) ==>
  well_typed_expr env (Builtin (BaseT (IntT 9)) (Bop Exp)
    [Name (BaseT (IntT 9)) "x"; Literal (BaseT (IntT 9)) (IntL 2)]) /\
  within_int_bound (Signed 9) (-16) /\
  evaluate_binop (Signed 9) tv Exp (IntV (-16)) (IntV 2) =
    INR (RuntimeError "bounded_int_op bound")
Proof
  simp[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
       evaluate_type_def, well_typed_builtin_app_def, well_typed_binop_def,
       builtin_operands_ok_def, power_operands_ok_def, power_exponent_ok_def,
       integer_literal_expr_def, integer_value_bits_def, expr_type_def,
       within_int_bound_def, evaluate_binop_def, bounded_int_op_def,
       integerTheory.INT_EXP_CALCULATE] >> simp[arithmeticTheory.NUMERAL_DEF]
QED

Definition power_probe_state_def:
  power_probe_state = (ARB : compile_state) with
    <|cs_current_insts := []; cs_next_id := 0; cs_next_var := 0|>
End

(* The literal options are exactly those extracted from the checked AST. *)
Definition power_int9_compilation_def:
  power_int9_compilation =
    compile_binop Exp (Lit (i2w (-16))) (Lit 2w) (BaseT (IntT 9))
      (expr_int_literal (Name (BaseT (IntT 9)) "x"))
      (expr_int_literal (Literal (BaseT (IntT 9)) (IntL 2))) power_probe_state
End

Theorem power_int9_square_generated_block_reverts:
  let (out, st') = power_int9_compilation in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 7 JMP [Label "done"] []]|> in
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = Abort Revert_abort ss'
Proof
  simp[power_int9_compilation_def, compile_binop_def, compile_safe_pow_def,
       expr_int_literal_def, type_bits_def, is_signed_type_def,
       power_int9_square_bound, power_probe_state_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def,
       i2w_def] >>
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem power_int256_endpoint_bounds:
  largest_pow_base 255 256 T = 1 /\ largest_pow_exponent 2 256 T = 254
Proof
  `1 <= largest_pow_base 255 256 T` by simp[largest_pow_base_characterisation] >>
  `~(2 <= largest_pow_base 255 256 T)` by simp[largest_pow_base_characterisation] >>
  `254 <= largest_pow_exponent 2 256 T` by
    simp[largest_pow_exponent_characterisation] >>
  `~(255 <= largest_pow_exponent 2 256 T)` by
    simp[largest_pow_exponent_characterisation] >> decide_tac
QED

Theorem power_int256_endpoint_source_result:
  evaluate_binop (Signed 256) tv Exp (IntV (-2)) (IntV 255) =
    INL (IntV (-&(2 ** 255)))
Proof
  simp[evaluate_binop_def, bounded_int_op_def, within_int_bound_def,
       integerTheory.INT_EXP_CALCULATE] >> simp[arithmeticTheory.NUMERAL_DEF]
QED

(* Exercise BOTH actual literal branches at the valid negative endpoint. *)
Theorem power_int256_endpoint_generated_blocks:
  let (out, st') = compile_binop Exp (Lit (i2w (-2))) (Lit 255w)
    (BaseT (IntT 256)) (if literal_base then SOME (-2) else NONE)
    (SOME 255) power_probe_state in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 7 JMP [Label "done"] []]|> in
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = OK ss' /\
        eval_operand out ss' = SOME (i2w (-&(2 ** 255)))
Proof
  Cases_on `literal_base` >>
  simp[compile_binop_def, compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_int256_endpoint_bounds, power_probe_state_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def, i2w_def] >>
  EVAL_TAC >> simp[FLOOKUP_UPDATE]
QED

(* The corresponding POSITIVE endpoint is out of range in BOTH branches. *)
Theorem power_int256_positive_endpoint_generated_blocks:
  let (out, st') = compile_binop Exp (Lit 2w) (Lit 255w)
    (BaseT (IntT 256)) (if literal_base then SOME 2 else NONE)
    (SOME 255) power_probe_state in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 7 JMP [Label "done"] []]|> in
  evaluate_binop (Signed 256) tv Exp (IntV 2) (IntV 255) =
    INR (RuntimeError "bounded_int_op bound") /\
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = Abort Revert_abort ss'
Proof
  Cases_on `literal_base` >>
  simp[compile_binop_def, compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_int256_endpoint_bounds, power_probe_state_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def, i2w_def,
       evaluate_binop_def, bounded_int_op_def, within_int_bound_def,
       integerTheory.INT_EXP] >>
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  simp[FLOOKUP_UPDATE]
QED

(* Explicit 0**0 witness: +1, not zero, in every checked signed/unsigned width,
   using both literal selections and the actual generated Venom block. *)
Theorem power_zero_zero_generated_blocks:
  (if signed then 1 < bits else 0 < bits) ==>
  let ty = if signed then BaseT (IntT bits) else BaseT (UintT bits) in
  let (out, st') = compile_binop Exp (Lit 0w) (Lit 0w) ty
    (if literal_base then SOME 0 else NONE) (SOME 0) power_probe_state in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 7 JMP [Label "done"] []]|> in
  evaluate_binop (if signed then Signed bits else Unsigned bits) tv Exp
    (IntV 0) (IntV 0) = INL (IntV 1) /\
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = OK ss' /\
        eval_operand out ss' = SOME 1w
Proof
  Cases_on `signed` >> Cases_on `literal_base` >> simp[] >> strip_tac >>
  `bits <> 1 \/ 0 < bits` by decide_tac >>
  simp[compile_binop_def, compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_probe_state_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def, evaluate_binop_def, bounded_int_op_def,
       within_int_bound_def, integerTheory.int_exp] >>
  EVAL_TAC >> simp[FLOOKUP_UPDATE]
QED

(* The primitive exponent branches really emit ASSERT; EXP and preserve the
   base at exponent one (including its signed two's-complement encoding). *)
Theorem power_primitive_exponent_generated_blocks:
  (n = 0 \/ n = 1) /\ (~signed \/ bits <> 1) ==>
  let ty = if signed then BaseT (IntT bits) else BaseT (UintT bits) in
  let (out, st') = compile_binop Exp (Lit w) (Lit (n2w n)) ty
    NONE (SOME (&n)) power_probe_state in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 2 JMP [Label "done"] []]|> in
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = OK ss' /\
        eval_operand out ss' = SOME (if n = 0 then 1w else w)
Proof
  strip_tac >> Cases_on `signed` >> gvs[] >>
  simp[compile_binop_def, compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_probe_state_def, comp_bind_def, comp_ignore_bind_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  EVAL_TAC >> simp[FLOOKUP_UPDATE]
QED

Theorem power_primitive_exponent_source_result:
  (n = 0 \/ n = 1) /\ (if signed then 1 < bits else 0 < bits) /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a ==>
  evaluate_binop (if signed then Signed bits else Unsigned bits) tv Exp
    (IntV a) (IntV (&n)) = INL (IntV (if n = 0 then 1 else a))
Proof
  `a ** 1 = a` by
    (CONV_TAC (LAND_CONV (RAND_CONV numLib.num_CONV)) >>
     PURE_REWRITE_TAC [integerTheory.int_exp, integerTheory.INT_MUL_RID] >>
     REFL_TAC) >>
  strip_tac >> Cases_on `signed` >> gvs[] >>
  `0 < bits` by decide_tac >>
  fs[evaluate_binop_def, bounded_int_op_def, integerTheory.int_exp,
     within_int_bound_def]
QED

(* Exact source/actual-block agreement for BOTH primitive exponent branches,
   at every raw valid width, not just the Python byte-aligned types. *)
Theorem power_primitive_exponent_source_block:
  (n = 0 \/ n = 1) /\ (if signed then 1 < bits else 0 < bits) /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a ==>
  evaluate_binop (if signed then Signed bits else Unsigned bits) tv Exp
    (IntV a) (IntV (&n)) = INL (IntV (if n = 0 then 1 else a)) /\
  (let ty = if signed then BaseT (IntT bits) else BaseT (UintT bits) in
   let (out, st') = compile_binop Exp (Lit (i2w a)) (Lit (n2w n)) ty
     NONE (SOME (&n)) power_probe_state in
   let bb = <|bb_label := "power";
              bb_instructions := st'.cs_current_insts ++
                [mk_inst 2 JMP [Label "done"] []]|> in
   ?ss'. run_block fuel ctx bb (init_venom_state "power") = OK ss' /\
         eval_operand out ss' = SOME (i2w (if n = 0 then 1 else a)))
Proof
  disch_tac >> conj_tac
  >- (irule power_primitive_exponent_source_result >> fs[]) >>
  `~signed \/ bits <> 1` by (Cases_on `signed` >> gvs[]) >>
  mp_tac (Q.INST [`w` |-> `i2w a`]
    (SPEC_ALL power_primitive_exponent_generated_blocks)) >>
  (impl_tac >- fs[]) >> Cases_on `n = 0` >> simp[i2w_pos]
QED

(* IntT 1 is rejected even by raw checking. The total compiler nevertheless
   rejects its out-of-range +1 result; no checker restriction is added here. *)
Theorem power_int1_zero_exponent_rejected_type:
  ~well_typed_expr env (Builtin (BaseT (IntT 1)) (Bop Exp)
    [Literal (BaseT (IntT 1)) (IntL (-1));
     Literal (BaseT (IntT 1)) (IntL 0)]) /\
  evaluate_binop (Signed 1) tv Exp (IntV (-1)) (IntV 0) =
    INR (RuntimeError "bounded_int_op bound")
Proof
  EVAL_TAC >> simp[integerTheory.int_exp]
QED

Theorem power_int1_zero_exponent_generated_blocks:
  b = -1 \/ b = 0 ==>
  let (out, st') = compile_binop Exp (Lit (i2w b)) (Lit 0w)
    (BaseT (IntT 1)) (if literal_base then SOME b else NONE)
    (SOME 0) power_probe_state in
  let bb = <|bb_label := "power";
             bb_instructions := st'.cs_current_insts ++
               [mk_inst 9 JMP [Label "done"] []]|> in
  ?ss'. run_block fuel ctx bb (init_venom_state "power") = Abort Revert_abort ss'
Proof
  strip_tac >> Cases_on `literal_base` >> gvs[] >>
  simp[compile_binop_def, compile_safe_pow_def, compile_clamp_def,
       clamp_and_return_def, type_bounds_def, type_bits_def, is_signed_type_def,
       power_probe_state_def, comp_bind_def, comp_ignore_bind_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def,
       i2w_def] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[FLOOKUP_UPDATE]
QED
