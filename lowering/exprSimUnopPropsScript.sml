(* Unary lowering, source evaluation and instruction properties. *)
Theory exprSimUnopProps
Ancestors
  builtinProps arithmeticProps vyperArith vyperTypeSystem
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping
Libs
  intLib pairLib

(* ===== The builtin's fragment ===== *)

(* The source result of bi on one value, as eval_expr gives it for
   Builtin ann bi [e1] once e1 is evaluated to v1 in the state es; tys is
   [expr_type e1]. *)
Definition unop_result_def:
  unop_result cx ann bi tys v1 (es:evaluation_state) =
    case evaluate_builtin cx es.accounts ann bi tys [v1] of
      INL v => INL v
    | INR e => INR (Error e)
End

(* The builtin's fragment f, from the operand x holding the word w1 in a
   state related at es0, the source state after the operand: on a value it
   reaches its end with op holding the result as a value of type t,
   keeping the variables handed out before it, the allocations and the
   memory; on an error it exits as expr_exit allows. *)


(* ===== Evaluating a one-operand builtin ===== *)

Theorem eval_expr_unop_cases:
  !cx ann bi e1 es res es'.
    (do r <- eval_expr cx (Builtin ann bi [e1]); read_result cx r od) es = (res, es') /\ bi <> Len /\
    ~precompile_builtin bi /\ builtin_args_length_ok bi 1 ==>
    (?exc. (do r <- eval_expr cx e1; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
    ?v1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1, es') /\
         res = unop_result cx ann bi [expr_type e1] v1 es'
Proof
  rpt gen_tac >> strip_tac >>
  `bi <> Bop In /\ bi <> Bop NotIn` by
    (rpt strip_tac >> gvs[builtin_args_length_ok_def]) >>
  `bi <> Env MsgGas` by (strip_tac >> gvs[builtin_args_length_ok_def]) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  ASM_REWRITE_TAC [] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  simp[get_accounts_def, lift_sum_def, unop_result_def, read_result_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >>
  gvs[AllCaseEqs(), return_def, raise_def, read_result_def] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  qmatch_asmsub_abbrev_tac `evaluate_builtin cx ac ann bi ts vs` >>
  Cases_on `evaluate_builtin cx ac ann bi ts vs` >>
  gvs[return_def, raise_def, Abbr `ac`, Abbr `ts`, Abbr `vs`]
QED

(* Source action boundary for the three recursive numeric/Boolean builtins. *)
Theorem eval_expr_unop_action:
  (bi = Not \/ bi = Abs \/ bi = Neg) ==>
  (bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. (unop_result cx ann bi [expr_type e] v es, es)))
Proof
  strip_tac >>
  `bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1` by
    (gvs[builtin_args_length_ok_def, precompile_builtin_def]) >>
  pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) x` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_unop_cases) >>
  strip_tac >> gvs[bind_def]
QED

Theorem expr_post_unop:
  !func cenv cx ann bi e1 es es' sa s1 sb s0 t0 ss x op v1 v ctx.
    expr_post ctx func cenv cx e1 es sa s1 s0 es' v1 x t0 /\
    stmt_state_rel ctx func cenv cx es' ss /\
    expr_val_rel cx ann v op ss /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
           lookup_var z ss = SOME w) /\
    (!aid b. FLOOKUP t0.vs_allocas aid = SOME b ==>
             FLOOKUP ss.vs_allocas aid = SOME b) /\
    ss.vs_memory = t0.vs_memory /\
    is_word_type ann /\ sa.cs_next_var <= s1.cs_next_var ==>
    expr_post ctx func cenv cx (Builtin ann bi [e1]) es sa sb s0 es' v op ss
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  `locals_kept cenv es s0 ss` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  `~expr_has_effect (Builtin ann bi [e1]) ==> pure_frame cenv func es sa s0 ss` by
    (simp[expr_has_effect_thm] >> strip_tac >>
     `pure_frame cenv func es sa s0 t0` by
       (qpat_x_assum `_ ==> pure_frame _ _ _ _ _ t0` irule >>
        first_assum ACCEPT_TAC) >>
     drule_all pure_frame_mem_tail >> disch_then ACCEPT_TAC) >>
  simp[expr_val_at_def, vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s1 z /\ lookup_var z t0 = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

(* expr_sim of a one-operand builtin from expr_sim of its operand, lowered
   at ty1, and unop_frag. *)
(* unop_frag from the run facts of the builtin's straight-line code. *)


(* ===== Lowering of not and abs ===== *)

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* not and abs dispatch to compile_builtin_dispatch whatever their
   arguments. *)
Theorem compile_expr_body_not_abs:
  !f g h cenv ty ann bi args st.
    (bi = Not \/ bi = Abs) ==>
    compile_expr_body f g h cenv ty (Builtin ann bi args) st =
    g cenv (expr_type (Builtin ann bi args)) ty bi args st
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> simp[compile_expr_body_def] >>
  Cases_on `args` >> simp[] >> rename1 `Builtin _ _ (a1::r1)` >>
  Cases_on `a1` >> simp[] >> Cases_on `r1` >> simp[] >>
  rename1 `Builtin _ _ (_::a2::r2)` >>
  Cases_on `a2` >> simp[] >> Cases_on `r2` >> simp[] >>
  rename1 `Builtin _ _ (_::_::a3::r3)` >>
  Cases_on `a3` >> simp[] >> Cases_on `r3` >> simp[]
QED

Theorem compile_expr_not_abs:
  !cenv ty ann bi args st.
    (bi = Not \/ bi = Abs) ==>
    compile_expr cenv ty (Builtin ann bi args) st =
    compile_builtin_dispatch cenv (expr_type (Builtin ann bi args)) ty bi
      args st
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_not_abs] >>
  simp expr_sizes
QED

(* not: the operand at its own type, then ISZERO on bool and
   compile_invert otherwise. *)
Theorem lower_value_not:
  !cenv ty ann e1 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Not [e1]) sa = (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e1) e1 sa = (x, s1) /\
      (if expr_type e1 = BaseT BoolT then emit_op ISZERO [x]
       else compile_invert x (expr_type e1) cenv) s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_not_abs] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  Cases_on `expr_type e1 = BaseT BoolT` >>
  gvs[unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qexistsl [`v`, `st1`] >> simp[]
QED

(* abs: the operand at the type compile_expr threads, then
   compile_builtin_abs. *)
Theorem lower_value_abs:
  !cenv ty ann e1 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Abs [e1]) sa = (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv ty e1 sa = (x, s1) /\
      compile_builtin_abs x s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_not_abs] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qexistsl [`v`, `st1`] >> simp[]
QED

(* not and abs are lowered to a StackValue, whatever their arguments. *)
Theorem compile_not_abs_stack:
  !cenv ty ann args sa.
    (?t op sb. compile_expr cenv ty (Builtin ann Not args) sa =
               (StackValue t op, sb)) /\
    (?t op sb. compile_expr cenv ty (Builtin ann Abs args) sa =
               (StackValue t op, sb))
Proof
  rpt gen_tac >> simp[compile_expr_not_abs] >> conj_tac >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  simp[as_stack_val_pair, pairTheory.UNCURRY] >> rw[]
QED

(* ===== not ===== *)

(* On a flag of m members, the source's NOT masked to the members is the
   XOR with the members' mask that the lowering emits. *)
Theorem flag_not_xor:
  !k m. k < 2 ** m /\ m <= 256 ==>
    word_xor (n2w k) (n2w (2 ** m - 1)) =
    word_and (word_1comp (n2w k)) (word_1comp (word_lsl (word_1comp 0w) m))
      : bytes32
Proof
  rw[fcpTheory.CART_EQ, word_xor_def, word_and_def, word_1comp_def,
     word_lsl_def, fcpTheory.FCP_BETA, word_index, word_0] >>
  rename1 `i < 256` >>
  Cases_on `i < m` >> simp[bitTheory.BIT_EXP_SUB1] >>
  `2 ** m <= 2 ** i` by simp[] >>
  `~BIT i k` by (irule bitTheory.NOT_BIT_GT_TWOEXP >> decide_tac) >>
  simp[]
QED

Theorem word_of_bytes_be_to_bytes:
  !w : bytes32. word_of_bytes_be (word_to_bytes_be w) = w
Proof
  simp[word_to_bytes_be_def, word_of_bytes_be_def, word_of_bytes_word_to_bytes]
QED

Theorem length_word_to_bytes_be:
  !w : bytes32. LENGTH (word_to_bytes_be w) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

val sf_step = FIRST [
  irule straight_fresh_bind >> conj_tac,
  irule straight_fresh_ignore_bind >> conj_tac,
  gen_tac >> BETA_TAC,
  irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
  irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
  MATCH_ACCEPT_TAC straight_fresh_return,
  IF_CASES_TAC];

(* The compile-state shape of a straight_fresh action. *)
Theorem straight_fresh_cs_extends:
  !m sa x sb. straight_fresh m /\ m sa = (x, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >> fs[straight_fresh_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem straight_fresh_not:
  !t cenv x.
    straight_fresh (if t = BaseT BoolT then emit_op ISZERO [x]
                    else compile_invert x t cenv)
Proof
  rpt gen_tac >> IF_CASES_TAC
  >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  Cases_on `t` >> simp[compile_invert_def, LET_THM] >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

(* The word types not takes. *)
Theorem not_type_cases:
  !t. is_bool_type t \/ is_uint256_type t \/ is_bytes32_type t \/
      is_flag_type t ==>
      t = BaseT BoolT \/ t = BaseT (UintT 256) \/
      t = BaseT (BytesT (Fixed 32)) \/ ?nsid. t = FlagT nsid
Proof
  Cases >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[]
QED

(* not on its four operand types; the flag case reads the members' count
   from ce_flag_n_members. *)


(* ===== abs ===== *)

(* An int256's word is MIN_INT exactly for MIN_INT, and its absolute
   value's word is what compile_builtin_abs computes. *)
Theorem abs_i2w:
  !i. INT_MIN (:256) <= i /\ i <= INT_MAX (:256) ==>
      (i2w i = (INT_MINw : bytes32) <=> i = INT_MIN (:256)) /\
      i2w (ABS i) : bytes32 =
        if word_msb (i2w i : bytes32) then 0w - i2w i else i2w i
Proof
  rpt strip_tac
  >- (eq_tac >> strip_tac
      >- (`w2i (i2w i : bytes32) = i` by
            (irule integer_wordTheory.w2i_i2w >> asm_rewrite_tac[]) >>
          gvs[integer_wordTheory.w2i_INT_MINw]) >>
      pop_assum SUBST1_TAC >> MATCH_ACCEPT_TAC integer_wordTheory.i2w_INT_MIN) >>
  `~(ABS i < 0)` by simp[integerTheory.INT_NOT_LT, integerTheory.INT_ABS_POS] >>
  `i2w (ABS i) : bytes32 = word_abs (i2w i)` by
    simp[integer_wordTheory.word_abs_i2w, integer_wordTheory.i2w_def] >>
  simp[word_abs_def, word_msb_neg, WORD_SUB_LZERO]
QED

(* An int256 is within the word's range, and its absolute value is an
   int256 except for MIN_INT. *)
Theorem int256_abs_bound:
  !i. within_int_bound (Signed 256) i ==>
      INT_MIN (:256) <= i /\ i <= INT_MAX (:256) /\
      (within_int_bound (Signed 256) (ABS i) <=> i <> INT_MIN (:256))
Proof
  gen_tac >>
  `INT_MIN (:256) = -&(2 ** 255) /\ INT_MAX (:256) = &(2 ** 255) - 1` by
    simp[integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
         wordsTheory.INT_MAX_def, venomMemPropsTheory.dimindex_256] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  qspec_then `i` strip_assume_tac integerTheory.INT_NUM_CASES >>
  simp[within_int_bound_def] >> intLib.COOPER_TAC
QED

Theorem straight_fresh_abs:
  !x. straight_fresh (compile_builtin_abs x)
Proof
  rw[compile_builtin_abs_def, compile_select_def] >> rpt sf_step
QED





Theorem compile_expr_body_neg:
  !f g h cenv ty ann args st.
    compile_expr_body f g h cenv ty (Builtin ann Neg args) st =
    g cenv (expr_type (Builtin ann Neg args)) ty Neg args st
Proof
  rpt gen_tac >> simp[compile_expr_body_def] >>
  Cases_on `args` >> simp[] >> rename1 `Builtin _ _ (a1::r1)` >>
  Cases_on `a1` >> simp[] >> Cases_on `r1` >> simp[] >>
  rename1 `Builtin _ _ (_::a2::r2)` >>
  Cases_on `a2` >> simp[] >> Cases_on `r2` >> simp[] >>
  rename1 `Builtin _ _ (_::_::a3::r3)` >>
  Cases_on `a3` >> simp[] >> Cases_on `r3` >> simp[]
QED

Theorem compile_expr_neg:
  !cenv ty ann args st.
    compile_expr cenv ty (Builtin ann Neg args) st =
    compile_builtin_dispatch cenv (expr_type (Builtin ann Neg args)) ty Neg
      args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_neg] >>
  simp expr_sizes
QED

Theorem lower_value_neg:
  !cenv ty ann e1 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Neg [e1]) sa = (op,sb) ==>
    ?x s1. lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
      compile_neg x (expr_type e1) s1 = (op,sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_neg] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qexistsl [`v`, `st1`] >> simp[]
QED

Theorem compile_neg_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann Neg args) sa =
      (StackValue t op,sb)
Proof
  rpt gen_tac >> simp[compile_expr_neg] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  simp[as_stack_val_pair, pairTheory.UNCURRY]
QED

Theorem straight_fresh_neg:
  !x ty. straight_fresh (\s. compile_neg x ty s)
Proof
  rpt gen_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule straight_fresh_bind >> reverse conj_tac
  >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  gen_tac >> BETA_TAC >> irule straight_fresh_ignore_bind >> conj_tac
  >- (irule straight_fresh_emit_void >> simp[fresh_write_op_def]) >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

Theorem signed_neg_bound:
  !n i. 0 < n /\ within_int_bound (Signed n) i ==>
    (within_int_bound (Signed n) (-i) <=> -&(2 ** (n-1)) < i)
Proof
  rpt gen_tac >> simp[within_int_bound_def] >>
  rpt strip_tac >> Cases_on `i < 0` >>
  Cases_on `0 < i` >> gvs[] >> intLib.ARITH_TAC
QED

Theorem signed_neg_word_test:
  !n i. 0 < n /\ n <= 256 /\ within_int_bound (Signed n) i ==>
    (w2i (i2w (-&(2 ** (n-1))) : bytes32) <
       w2i (i2w i : bytes32) <=> within_int_bound (Signed n) (-i))
Proof
  rpt strip_tac >>
  `w2i (i2w i : bytes32) = i` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `n - 1 <= 255` by decide_tac >>
  drule w2i_i2w_neg_pow2 >>
  drule_all signed_neg_bound >> simp[]
QED

Theorem neg_int_source:
  !cx n i es.
    0 < n /\ within_int_bound (Signed n) i ==>
    unop_result cx (BaseT (IntT n)) Neg [BaseT (IntT n)] (IntV i) es =
      if -&(2 ** (n-1)) < i then INL (IntV (-i))
      else INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  rpt strip_tac >> drule_all signed_neg_bound >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, bounded_int_op_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem neg_decimal_source:
  !cx i es.
    within_int_bound (Signed 168) i ==>
    unop_result cx (BaseT DecimalT) Neg [BaseT DecimalT] (DecimalV i) es =
      if -&(2 ** 167) < i then INL (DecimalV (-i))
      else INR (Error (RuntimeError "bounded_decimal_op"))
Proof
  rpt strip_tac >>
  `within_int_bound (Signed 168) (-i) <=> -&(2 ** 167) < i` by
    (qspec_then `168` mp_tac signed_neg_bound >> simp[]) >>
  simp[unop_result_def, evaluate_builtin_def, bounded_decimal_op_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem neg_typed_source:
  !cx t tv v es.
    is_numeric_type t /\ ~is_uint_type t /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v ==>
    (if w2i (FST (type_bounds t)) < w2i (typed_val_to_w256 tv v) then
       ?v'. unop_result cx t Neg [t] v es = INL v' /\
         typed_val_to_w256 tv v' = 0w - typed_val_to_w256 tv v
     else ?m. unop_result cx t Neg [t] v es =
                INR (Error (RuntimeError m)))
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. t = BaseT (IntT n)) \/ t = BaseT DecimalT` by
    (Cases_on `t` >> gvs[is_numeric_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >> gvs[]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  simp[type_bounds_def, type_bits_def, is_signed_type_def,
       typed_val_to_w256_def, val_to_w256_def]
  >- (`0 < n` by decide_tac >>
      drule_all neg_int_source >> strip_tac >>
      drule_all signed_neg_word_test >>
      drule_all signed_neg_bound >> rpt strip_tac >>
      simp[] >> strip_tac >>
      simp[typed_val_to_w256_def, val_to_w256_def,
           GSYM integer_wordTheory.MULT_MINUS_ONE, WORD_SUB_LZERO,
           WORD_SUB_INTRO]) >>
  drule neg_decimal_source >> strip_tac >>
  `w2i (i2w i : bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists `168` >> simp[]) >>
  qspec_then `167` mp_tac w2i_i2w_neg_pow2 >> simp[] >> strip_tac >>
  simp[] >> strip_tac >>
  simp[typed_val_to_w256_def, val_to_w256_def,
       GSYM integer_wordTheory.MULT_MINUS_ONE, WORD_SUB_LZERO,
       WORD_SUB_INTRO]
QED

Theorem compile_neg_run:
  !x ty sa op sb ss w.
    compile_neg x ty sa = (op, sb) /\ fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME w ==>
    (w2i (FST (type_bounds ty)) < w2i w ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (0w - w)) /\
    (~(w2i (FST (type_bounds ty)) < w2i w) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >>
  simp[compile_neg_def, LET_THM] >>
  pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule emit_op_SGT_correct >>
  disch_then drule >> simp[eval_operand_def] >>
  strip_tac >>
  `eval_operand x ss' = SOME w` by metis_tac[] >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  conj_tac
  >- (strip_tac >>
      `eval_operand ok ss' = SOME 1w` by
        gvs[integer_wordTheory.WORD_GTi, integerTheory.int_gt, bool_to_word_def] >>
      `(1w : bytes32) <> 0w` by simp[] >>
      drule_all emit_void_ASSERT_ok >> strip_tac >>
      imp_res_tac fresh_vars_wrt_emit_void >>
      drule emit_op_SUB_correct >> simp[eval_operand_def] >>
      disch_then drule >> disch_then drule >> strip_tac >>
      qspecl_then [`cs'`, `cs''`, `sb`] mp_tac run_inst_seq_chain >>
      simp[] >> disch_then drule >> strip_tac >>
      qspecl_then [`sa`, `cs'`, `sb`] mp_tac run_inst_seq_chain >>
      simp[] >> disch_then drule >> strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  strip_tac >>
  `eval_operand ok ss' = SOME 0w` by
    gvs[integer_wordTheory.WORD_GTi, integerTheory.int_gt, bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `!s. run_inst_seq (emitted_insts sa cs'') ss <> OK s` by simp[] >>
  drule_all run_inst_seq_chain_err >> strip_tac >>
  qexists `ss''` >> simp[]
QED
