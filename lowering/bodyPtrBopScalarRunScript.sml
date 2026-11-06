(* Concrete semantic suffix runs, before pointer-path packaging. *)
Theory bodyPtrBopScalarRun
Ancestors exprSimArith exprSimBinopFrag exprBopSimDefs exprLowering
  freshWrites compileEnv valueEncoding vyperInterpreter loweringSlice
  vyperContext vyperValueOperation varsExt appendStorageStageTransportPtr
  fragGasFresh list arithmeticProps builtinProps

Theorem bop_checked_fresh_run:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else
                      if bop = Sub then i1 - i2 else i1 * i2` >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
    if within_int_bound u rr then INL (IntV rr)
    else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (Cases_on `bop` >>
     gvs[Abbr `rr`, bop_result_def, evaluate_builtin_def,
         evaluate_binop_def, bounded_int_op_def] >> rw[]) >>
  asm_rewrite_tac[] >>
  `((within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (i2w rr)) /\
    (~within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t))` by
    (gvs[Abbr `rr`, compile_binop_def]
     >- (drule_all compile_safe_add_run >> simp[])
     >- (drule_all compile_safe_sub_run >> simp[]) >>
     drule_all compile_safe_mul_run >> simp[]) >>
  Cases_on `within_int_bound u rr` >>
  gvs[word_value_def, val_to_w256_def] >> metis_tac[]
QED

Theorem bop_run_drop_fresh_transport:
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_ext_call_op i.inst_opcode) code /\
  ((?v t. res = INL v /\ word_value v /\
      run_inst_seq code (drop_fresh sa s) = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. res = INR (Error (RuntimeError m)) /\
      run_inst_seq code (drop_fresh sa s) = Abort Revert_abort t)) ==>
  (?v t. res = INL v /\ word_value v /\
      run_inst_seq code s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. res = INR (Error (RuntimeError m)) /\
      run_inst_seq code s = Abort Revert_abort t)
Proof
  strip_tac >>
  `vars_ext_result (run_inst_seq code (drop_fresh sa s))
                   (run_inst_seq code s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> metis_tac[vars_ext_eval_operand]
QED

Theorem bop_checked_run:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        (gvs[compile_binop_def] >> simp[straight_fresh_checked]) >>
      `writes_fresh sa (emitted_insts sa sb)` by
        metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> irule bop_checked_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_divmod_fresh_run:
  MEM bop [Div; Mod] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_assum `type_to_int_bound ty = _` (strip_assume_tac o MATCH_MP type_to_int_bound_bits) >>
  `math_val ty (i2w i1 : bytes32) = i1 /\
   math_val ty (i2w i2 : bytes32) = i2` by gvs[math_val_i2w] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >- (strip_tac >> simp[integer_wordTheory.i2w_0]) >>
     metis_tac[i2w_eq_0_within]) >>
  `((i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                 i1 = -&(2 ** (type_bits ty - 1)) /\ i2 = -1)) ==>
     ?m. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
           INR (Error (RuntimeError m))) /\
   (~(i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                  i1 = -&(2 ** (type_bits ty - 1)) /\ i2 = -1)) ==>
     ?z. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL (IntV z) /\
       (i2w z : bytes32) =
         (if bop = Div then (if is_signed_type ty then safe_sdiv else safe_div)
          else (if is_signed_type ty then safe_smod else safe_mod))
           (i2w i1) (i2w i2))` by
    (irule bop_result_divmod >> simp[] >> metis_tac[]) >>
  qpat_assum `~_ ==> ?z. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `~BAD ==> _` >> strip_tac >>
  Cases_on `BAD`
  >- (qpat_x_assum `~BAD ==> _` kall_tac >>
      qpat_x_assum `_ ==> ?m. _` mp_tac >> simp[] >> strip_tac >>
      disj2_tac >> qexists_tac `m` >> simp[] >>
      gvs[markerTheory.Abbrev_def, compile_binop_def]
      >- metis_tac[compile_safe_div_by_zero]
      >- (gvs[math_val_def] >> irule compile_safe_div_overflow >>
          simp[] >> metis_tac[]) >>
      metis_tac[compile_safe_mod_by_zero]) >>
  qpat_x_assum `~BAD ==> _` mp_tac >> simp[] >> strip_tac >>
  disj1_tac >> qexists_tac `IntV z` >>
  simp[word_value_def, val_to_w256_def] >>
  `in_type_range ty i1` by gvs[in_type_range_within] >>
  gvs[markerTheory.Abbrev_def, compile_binop_def]
  >- (drule_at (Pat `compile_safe_div _ _ _ _ = _`) compile_safe_div_ok >>
      Cases_on `is_signed_type ty` >> gvs[math_val_def]) >>
  drule_all compile_safe_mod_correct >> Cases_on `is_signed_type ty` >> simp[]
QED

Theorem bop_divmod_run:
  MEM bop [Div; Mod] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_assum `type_to_int_bound ty = _` (strip_assume_tac o MATCH_MP type_to_int_bound_bits) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        (gvs[compile_binop_def] >> simp[straight_fresh_checked]) >>
      `writes_fresh sa (emitted_insts sa sb)` by
        metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> irule bop_divmod_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_unsafe_run:
  MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
  type_to_int_bound ann =
    SOME (if is_signed_type ty then Signed (type_bits ty)
          else Unsigned (type_bits ty)) /\
  0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
  within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                   else Unsigned (type_bits ty)) i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  ?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `?v. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\ val_to_w256 v =
         truncate_to_bits (type_bits ty) (is_signed_type ty)
           (unsafe_word_op bop ty (i2w i1) (i2w i2))` by
    (simp[GSYM val_to_w256_def] >> irule bop_result_unsafe >> simp[]) >>
  qexists_tac `v` >> simp[] >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  simp[] >> rpt strip_tac >> irule step_unsafe_opcode >> simp[]
QED
