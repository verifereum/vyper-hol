(*
 * Expression simulation for the comparisons and min/max (#636, part 2)
 *
 * Lt, Gt, Eq, NotEq, LtE and GtE on two word values of one type lower to
 * compile_compare, one or two instructions.  binop_frag for them comes
 * from arithmeticProps' compile_compare_correct through
 * frag_exec_writes_fresh.  The source compares the values; the lowering
 * compares their words, unsigned for uint256 and signed otherwise, which
 * agree on values of the type (value_has_type).  Eq and NotEq on two
 * address or two bytesN values, which are BytesV, compare their typed
 * words (typed_val_to_w256) the same way, and those are equal just when
 * the bytes are.
 *
 * Min and Max compare the same way and pick an operand branchlessly
 * (compile_select).
 *
 * TOP-LEVEL:
 *   bop_result_compare   — the source result is eval_compare on the words
 *   compile_compare_words_sim — binop_frag_words for the comparisons, when
 *                          the source result is eval_compare on the words
 *   compile_compare_sim  — binop_frag for the comparisons
 *   compile_compare_bytes_sim — binop_frag_words for == and != on address
 *                          and bytesN, whose values are BytesV in their
 *                          typed words
 *   compile_minmax_sim   — binop_frag for Min and Max
 *
 * Helpers: int_word_cmp, compile_compare_shape, typed_val_to_w256_bytes_11,
 *   bop_result_minmax, straight_fresh_minmax, compile_minmax_correct
 *)

Theory exprSimCompare
Ancestors
  list rich_list
  fragExec varsExt exprSim freshWrites exprSimOps loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps arithmeticProps
  compileEnv vyperInterpreter vyperContext vyperValue vyperValueOperation
  vyperTyping
  vyperArith valueEncoding venomExecSemantics venomInst venomState
  builtinSimple builtinProps
  integer integer_word words
Libs
  intLib pairLib

(* A comparison of two words read back as the integers they hold, or their
   equality: the equality goals carry an i2w equation, the others go to
   COOPER_TAC. *)
val word_eq_tac =
  eq_tac >> rw[] >>
  qpat_x_assum `i2w _ = i2w _` (fn th =>
    assume_tac (AP_TERM ``w2i : bytes32 -> int`` th) >>
    assume_tac (AP_TERM ``\w:bytes32. (&w2n w):int`` th)) >>
  fs[];

val word_ord_tac =
  rpt (qpat_x_assum `&w2n _ = _` mp_tac) >>
  rpt (qpat_x_assum `w2i _ = _` mp_tac) >> COOPER_TAC;

fun word_cmp_tac (g as (_, w)) =
  let val is_word_eq =
        can (match_term ``(i2w (a:int) : bytes32) = i2w b``)
  in (if can (find_term is_word_eq) w then word_eq_tac else word_ord_tac) g
  end;

(* ===== The source ===== *)

(* The word of an integer of the type reads back as the integer: unsigned
   for uint256, signed otherwise. *)
Theorem int_word_cmp:
  !ty tv n.
    value_has_type tv (IntV n) /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    (is_uint256 ty ==> &w2n (i2w n : bytes32) = n) /\
    (~is_uint256 ty ==> w2i (i2w n : bytes32) = n)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> gvs[value_has_type_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> gvs[value_has_type_def] >> rw[]
  >- (`?m. n = &m` by metis_tac[NUM_POSINT_EXISTS] >>
      gvs[i2w_pos, w2n_n2w, dimword_def])
  >- (rename1 `Num n < 2 ** w` >>
      `Num n < 2 ** 255` by
        (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** w` >>
         simp[]) >>
      `~(n < 0)` by ARITH_TAC >>
      irule w2i_i2w_within_signed >> qexists_tac `256` >>
      fs[within_int_bound_def])
  >> rename1 `within_int_bound (Signed w) n` >>
  irule w2i_i2w_within_signed >> qexists_tac `w` >> simp[]
QED

(* The source result of a comparison of two word values of one type is
   eval_compare on their words. *)
Theorem bop_result_compare:
  !cx ann bop ty tv v1 v2 es.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    bop_result cx ann bop tys v1 v2 es =
      INL (BoolV
        (eval_compare bop ty (val_to_w256 v1) (val_to_w256 v2)))
Proof
  rpt gen_tac >> strip_tac >> fs[word_value_def] >> gvs[]
  (* one kind of v1 at a time, so that each unfolding of evaluate_binop
     covers a quarter of the value pairs *)
  >>~- ([`value_has_type _ (IntV _)`],
        Cases_on `v2` >>
        gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
            expr_res_ok_def, binop_negate_def] >>
        qspecl_then [`ty`, `tv`, `n`] mp_tac int_word_cmp >>
        (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
        qspecl_then [`ty`, `tv`, `i`] mp_tac int_word_cmp >>
        (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
        Cases_on `is_uint256 ty` >> fs[eval_compare_def, val_to_w256_def] >>
        word_cmp_tac)
  >>~- ([`value_has_type _ (DecimalV _)`],
        Cases_on `v2` >>
        gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
            expr_res_ok_def, binop_negate_def] >>
        Cases_on `tv` >> gvs[value_has_type_def] >>
        rename1 `BaseTV bt` >> Cases_on `bt` >> gvs[value_has_type_def] >>
        `w2i (i2w n : bytes32) = n /\ w2i (i2w i : bytes32) = i` by
          (rw[] >> irule w2i_i2w_within_signed >> qexists_tac `168` >>
           simp[]) >>
        fs[eval_compare_def, val_to_w256_def] >> word_cmp_tac)
  >>~- ([`value_has_type _ (FlagV _)`],
        Cases_on `v2` >>
        gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
            expr_res_ok_def, binop_negate_def] >>
        Cases_on `tv` >> gvs[value_has_type_def] >>
        `k < 2 ** 256 /\ n < 2 ** 256` by
          (rename1 `k < 2 ** m` >> `2 ** m <= 2 ** 256` by simp[] >>
           conj_tac >>
           irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m` >>
           asm_rewrite_tac[]) >>
        fs[eval_compare_def, val_to_w256_def, n2w_11, dimword_def,
           arithmeticTheory.LESS_MOD]) >>
  (* booleans *)
  Cases_on `v2` >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      expr_res_ok_def, binop_negate_def] >>
  rw[eval_compare_def, val_to_w256_def]
QED

(* ===== The lowering ===== *)

val wfe = REWRITE_RULE [GSYM AND_IMP_INTRO] writes_fresh_emit_op;

Theorem compile_compare_shape:
  !cmp x y ty st op st'.
    compile_compare cmp x y ty st = (op, st') /\
    MEM cmp [Lt; Gt; Eq; NotEq; LtE; GtE] ==>
    writes_fresh st (emitted_insts st st') /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_compare_def, LET_THM] >>
  Cases_on `is_uint256 ty` >> fs[comp_bind_def] >>
  FIRST [
    (* one instruction *)
    imp_res_tac emit_op_extends >> imp_res_tac writes_fresh_emit_op >>
    fs[same_blocks_def, fresh_write_op_def] >>
    qpat_x_assum `_.cs_current_insts = _ ++ _`
      (fn th => ONCE_REWRITE_TAC [th]) >>
    simp[rich_listTheory.IS_PREFIX_APPEND3] >> NO_TAC,
    (* two *)
    pairarg_tac >> gvs[] >>
    rename1 `emit_op _ _ mid = (op, st')` >>
    qpat_assum `emit_op _ _ st = _` (fn th1 =>
      qpat_assum `emit_op _ _ mid = _` (fn th2 =>
        strip_assume_tac (MATCH_MP emit_op_extends th1) >>
        strip_assume_tac (MATCH_MP emit_op_extends th2) >>
        strip_assume_tac (MATCH_MP emitted_insts_emit_op th1) >>
        mp_tac (MATCH_MP wfe th1) >> mp_tac (MATCH_MP wfe th2))) >>
    simp_tac (srw_ss()) [fresh_write_op_def] >> rpt strip_tac >>
    `emitted_insts st st' = emitted_insts st mid ++ emitted_insts mid st'` by
       (irule emitted_insts_append >> simp[]) >>
    `writes_fresh st (emitted_insts mid st')` by
       (irule writes_fresh_mono >> qexists_tac `mid` >> simp[]) >>
    qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
    asm_rewrite_tac [writes_fresh_append] >>
    fs[same_blocks_def] >>
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC,
                 rich_listTheory.IS_PREFIX_APPEND3]]
QED

(* binop_frag_words for the comparisons, when the source result is
   eval_compare on the operands' words: compile_compare compares them. *)
Theorem compile_compare_words_sim:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     bop_result cx ann bop tys v1 v2 es0 =
       INL (BoolV (eval_compare bop ty w1 w2))) ==>
    binop_frag_words ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[binop_frag_words_def] >>
  rpt strip_tac >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac >>
  `compile_compare bop x y ty sa = (op, sb)` by
    (qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >> fs[] >>
     rw[compile_binop_def]) >>
  drule_all compile_compare_shape >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `sa`, `sb`, `op`,
     `bool_to_word (eval_compare bop ty w1 w2)`,
     `\ss. eval_operand x ss = SOME w1 /\ eval_operand y ss = SOME w2`,
     `\a. F`, `\r. F`, `s0`] mp_tac frag_exec_writes_fresh >>
  (impl_tac
   >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac >>
      FIRST [
        qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
        qspecl_then [`y`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
        asm_simp_tac bool_ss [] >> NO_TAC,
        qspecl_then [`bop`, `x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`,
                     `w1`, `w2`] mp_tac compile_compare_correct >>
        simp[]])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  simp[] >> rpt strip_tac >>
  Cases_on `eval_compare bop ty w1 w2` >>
  gvs[val_to_w256_def, word_value_def, bool_to_word_def]
QED

(* binop_frag for the comparisons, on two word values of one type. *)
Theorem compile_compare_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[binop_frag_def] >>
  irule compile_compare_words_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `tv`, `v1`, `v2`, `es0`] mp_tac
    bop_result_compare >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC
QED

(* ===== Equality on address and bytesN ===== *)

(* The typed words of two address values, or of two bytesN values of one
   width, are equal just when their bytes are: an address is the low 20
   bytes of its word, a bytesN the high N bytes. *)
Theorem typed_val_to_w256_bytes_11:
  !tv b1 b2.
    (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32) /\
    value_has_type tv (BytesV b1) /\ value_has_type tv (BytesV b2) ==>
    (typed_val_to_w256 tv (BytesV b1) = typed_val_to_w256 tv (BytesV b2) <=>
     b1 = b2)
Proof
  rpt strip_tac >> eq_tac >> simp[] >>
  gvs[value_has_type_def, typed_val_to_w256_def] >> strip_tac
  >- (`DROP 12 (word_to_bytes_be
                  (word_of_bytes_be (PAD_LEFT 0w 32 b1) : bytes32)) = b1 /\
       DROP 12 (word_to_bytes_be
                  (word_of_bytes_be (PAD_LEFT 0w 32 b2) : bytes32)) = b2` by
        simp[valueEncodingProofsTheory.word_to_bytes_be_pad_left_roundtrip] >>
      metis_tac[]) >>
  fs[valueEncodingProofsTheory.word_of_bytes_be_pad_right] >>
  `TAKE (LENGTH b1) (word_to_bytes_be (word_of_bytes_be b1 : bytes32)) = b1 /\
   TAKE (LENGTH b2) (word_to_bytes_be (word_of_bytes_be b2 : bytes32)) = b2` by
    simp[valueEncodingProofsTheory.TAKE_word_to_bytes_be_word_of_bytes_be] >>
  metis_tac[]
QED

(* binop_frag_words for == and != on two address or two bytesN values of
   one type, held in their typed words: compile_compare's EQ on the words
   is the source's comparison of the bytes. *)
Theorem compile_compare_bytes_sim:
  !ctx func cenv cx bop ty ann bl el tys tv b1 b2 es0.
    (bop = Eq \/ bop = NotEq) /\
    (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32) /\
    value_has_type tv (BytesV b1) /\ value_has_type tv (BytesV b2) ==>
    binop_frag_words ctx func cenv cx bop ty ann bl el tys
      (BytesV b1) (BytesV b2)
      (typed_val_to_w256 tv (BytesV b1)) (typed_val_to_w256 tv (BytesV b2)) es0
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `w1 = typed_val_to_w256 tv (BytesV b1)` >>
  qabbrev_tac `w2 = typed_val_to_w256 tv (BytesV b2)` >>
  `(w1 = w2 <=> b1 = b2)` by
    (unabbrev_all_tac >> irule typed_val_to_w256_bytes_11 >> simp[]) >>
  irule compile_compare_words_sim >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      binop_negate_def, eval_compare_def]
QED

(* ===== Min and Max ===== *)

(* A straight_fresh action built from the combinators. *)
val straight_fresh_tac =
  rpt (FIRST [IF_CASES_TAC,
              irule straight_fresh_bind >> rw[],
              irule straight_fresh_ignore_bind >> rw[],
              irule straight_fresh_emit_op >> simp[fresh_write_op_def],
              irule straight_fresh_emit_void >> simp[fresh_write_op_def],
              irule straight_fresh_return]);

Theorem straight_fresh_minmax:
  !x y ty bl el.
    straight_fresh (compile_binop Min x y ty bl el) /\
    straight_fresh (compile_binop Max x y ty bl el)
Proof
  rw[compile_binop_def, compile_select_def] >> straight_fresh_tac
QED

(* The source result of Min or Max is the operand eval_compare picks. *)
Theorem bop_result_minmax:
  !cx ann mm ty tv v1 v2 es.
    (mm = Min \/ mm = Max) /\
    expr_res_ok (bop_result cx ann mm tys v1 v2 es) /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    ?v. bop_result cx ann mm tys v1 v2 es = INL v /\ word_value v /\
        val_to_w256 v =
          if eval_compare (if mm = Min then Lt else Gt) ty
               (val_to_w256 v1) (val_to_w256 v2)
          then val_to_w256 v1 else val_to_w256 v2
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `ann`, `if mm = Min then Lt else Gt`, `ty`, `tv`, `v1`,
               `v2`, `es`] mp_tac bop_result_compare >>
  fs[word_value_def] >> gvs[] >> Cases_on `v2` >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      expr_res_ok_def] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (fn th => rewrite_tac [GSYM th]) >> rw[word_value_def] >>
  `n = i` by ARITH_TAC >> simp[]
QED

(* The run of the lowered Min or Max from a state with the fresh variables
   unbound. *)
Theorem compile_minmax_correct:
  !mm x y ty bl el st op st' a b ss.
    (mm = Min \/ mm = Max) /\ compile_binop mm x y ty bl el st = (op, st') /\
    eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          eval_operand op ss' =
            SOME (if eval_compare (if mm = Min then Lt else Gt) ty a b
                  then a else b)
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_binop_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> Cases_on `is_uint256 ty` >> fs[] >>
  FIRST (map (fn th => drule_all th >> strip_tac)
    [emit_op_LT_correct_mem, emit_op_SLT_correct, emit_op_GT_correct,
     emit_op_SGT_correct]) >>
  imp_res_tac emit_op_extends >>
  rename1 `run_inst_seq _ ss = OK ss1` >>
  qpat_assum `eval_operand cmp ss1 = SOME (bool_to_word _)` (fn th =>
    let val cc = rand (rand (rhs (concl th))) in
      qspecl_then [`cmp`, `x`, `y`, `bool_to_word ^cc`, `a`, `b`, `^cc`,
                   `ss1`, `cs'`, `op`, `st'`] mp_tac compile_select_correct
    end) >>
  simp[] >> strip_tac >>
  `st'.cs_current_insts = cs'.cs_current_insts ++ emitted_insts cs' st'` by
    (`straight_fresh (compile_select cmp x y)` by
       (rw[compile_select_def] >> straight_fresh_tac) >>
     fs[straight_fresh_def] >> res_tac) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss'` >> simp[eval_compare_def, WORD_LTi, WORD_GTi]
QED

(* binop_frag for Min and Max, on two word values of one type. *)
Theorem compile_minmax_sim:
  !ctx func cenv cx mm ty ann bl el v1 v2 es0 tv.
    (mm = Min \/ mm = Max) /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    binop_frag ctx func cenv cx mm ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> metis_tac[straight_fresh_minmax]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `mm`, `ty`, `tv`, `v1`, `v2`, `es0`] mp_tac
    bop_result_minmax >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> asm_rewrite_tac[] >> rpt strip_tac >>
  qspecl_then [`mm`, `x`, `y`, `ty`, `bl`, `el`, `sa`, `op`, `sb`,
               `val_to_w256 v1`, `val_to_w256 v2`, `ss`] mp_tac
    compile_minmax_correct >>
  asm_simp_tac bool_ss []
QED
