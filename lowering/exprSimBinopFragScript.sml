(*
 * Expression simulation: binary operators on typed word operands (#636,
 * Operators)
 *
 * binop_frag_typed, the fragment of a binary operator on operands of
 * word_value_types that have their types, by the operator's group onto the
 * simulation lemmas of exprSimOps, exprSimCompare and exprSimArith.
 *
 * TOP-LEVEL:
 *   binop_frag_typed      — binop_frag at the operands' types, for
 *                           exprSimOperators' compile_bop_word_sim
 *   binop_frag_word_typed — the same over any typed word operands
 *
 * The power and shift fragments carry operand facts supplied by the
 * checker and evaluator: literal/value agreement and nonnegative shifts.
 * binop_frag_shr_narrow also covers signed and unsigned widths below 256.
 * ExpMod is excluded by well_typed_binop.
 *
 * The unsafe operators are covered at integer widths of whole bytes, the
 * ones Vyper has: binop_frag_typed takes that of the left operand's type,
 * which exprSimHyps' expr_sim_pre gives (byte_widths_expr).
 *)

Theory exprSimBinopFrag
Ancestors
  exprBopBitwise exprBopFlag exprBopShift exprBopSimDefs exprBopStraight
  exprSimHypsDefs list finite_map fragExec exprSimHyps exprSimOps exprSimCompare exprSimArith primeFactor freshWrites
  exprBopLowering loweringSlice
  exprLowering compileEnv exprLoweringProps emitHelperProps arithmeticProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
Libs
  emitTacticsLib

(* Adjacent safe/unsafe endpoints of the finite power search. *)
Theorem pow_search_midpoint[local]:
  !lo hi fuel. lo + 1 < hi /\ hi - lo <= 2 ** SUC fuel ==>
    lo <= (lo + hi) DIV 2 /\ (lo + hi) DIV 2 <= hi /\
    (lo + hi) DIV 2 - lo <= 2 ** fuel /\
    hi - (lo + hi) DIV 2 <= 2 ** fuel
Proof
  cheat
QED

Theorem largest_pow_base_search_bounds[local]:
  !fuel exponent limit lo hi.
    lo ** exponent < limit /\ limit <= hi ** exponent /\
    lo <= hi /\ hi - lo <= 2 ** fuel ==>
    largest_pow_base_search fuel exponent limit lo hi ** exponent < limit /\
    limit <= (largest_pow_base_search fuel exponent limit lo hi + 1) ** exponent
Proof
  cheat
QED

Theorem largest_pow_base_bounds:
  !exponent bits signed.
    0 < exponent ==>
    largest_pow_base exponent bits signed ** exponent < (2 ** (bits - if signed then 1 else 0)) /\
    (2 ** (bits - if signed then 1 else 0)) <= (largest_pow_base exponent bits signed + 1) ** exponent
Proof
  cheat
QED
Theorem largest_pow_base_threshold:
  !exponent bits signed k.
    0 < exponent ==>
    (k <= largest_pow_base exponent bits signed <=>
     k ** exponent < 2 ** (bits - if signed then 1 else 0))
Proof
  cheat
QED

Theorem largest_pow_exponent_search_bounds[local]:
  !fuel base limit exponent.
    base ** exponent < limit /\ limit <= base ** (exponent + fuel + 1) ==>
    base ** largest_pow_exponent_search fuel base limit exponent < limit /\
    limit <= base ** (largest_pow_exponent_search fuel base limit exponent + 1)
Proof
  cheat
QED

Theorem largest_pow_exponent_bounds:
  !b bits signed.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) ==>
    b ** largest_pow_exponent b bits signed <
      2 ** (bits - if signed then 1 else 0) /\
    2 ** (bits - if signed then 1 else 0) <=
      b ** (largest_pow_exponent b bits signed + 1)
Proof
  cheat
QED

Theorem largest_pow_exponent_threshold:
  !b bits signed k.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) ==>
    (k <= largest_pow_exponent b bits signed <=>
     b ** k < 2 ** (bits - if signed then 1 else 0))
Proof
  cheat
QED


(* The first unsafe exponent is the only possible equality endpoint. *)
Theorem largest_pow_exponent_endpoint:
  !b bits signed k.
    2 <= b /\ b < 2 ** (bits - if signed then 1 else 0) /\
    b ** k = 2 ** (bits - if signed then 1 else 0) ==>
    k = largest_pow_exponent b bits signed + 1
Proof
  cheat
QED

Theorem largest_pow_exponent_signed_threshold:
  !b bits neg k.
    2 <= b /\ b < 2 ** (bits - 1) ==>
    (k <= (           if neg /\ ODD ((largest_pow_exponent b bits T) + 1) /\ b ** ((largest_pow_exponent b bits T) + 1) = 2 ** (bits - 1)
           then (largest_pow_exponent b bits T) + 1 else (largest_pow_exponent b bits T)) <=>
     b ** k < 2 ** (bits - 1) \/
     neg /\ ODD k /\ b ** k = 2 ** (bits - 1))
Proof
  cheat
QED

(* The type and the value of a typed operand of a word_value_type. *)
Theorem word_value_type_value_cases:
  !tenv t tv v.
    word_value_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    (?n i. t = BaseT (UintT n) /\ tv = BaseTV (UintT n) /\ v = IntV i /\
           0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i) \/
    (?n i. t = BaseT (IntT n) /\ tv = BaseTV (IntT n) /\ v = IntV i /\
           1 < n /\ n <= 256 /\ within_int_bound (Signed n) i) \/
    (?d. t = BaseT DecimalT /\ tv = BaseTV DecimalT /\ v = DecimalV d /\
         within_int_bound (Signed 168) d) \/
    (?b. t = BaseT BoolT /\ tv = BaseTV BoolT /\ v = BoolV b) \/
    (?nsid m k. t = FlagT nsid /\ tv = FlagTV m /\ v = FlagV k /\ m <= 256)
Proof
  cheat
QED

(* A typed value of an integer type. *)
Theorem int_type_value:
  !tenv ty tv v.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    ?i. v = IntV i /\ 0 < type_bits ty /\ type_bits ty <= 256 /\
        type_to_int_bound ty =
          SOME (if is_signed_type ty then Signed (type_bits ty)
                else Unsigned (type_bits ty)) /\
        within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                          else Unsigned (type_bits ty)) i
Proof
  cheat
QED

(* Modular exponentiation preserves the integer encoding, including
   negative bases.  Induct over the mathematical exponent, not its word. *)
Theorem int_pow_word_encoding:
  !a e. (n2w (w2n (i2w a : bytes32) ** e) : bytes32) = i2w (a ** e)
Proof
  cheat
QED

Theorem word_exp_int_encoding:
  !a b. 0 <= b /\ b < &(dimword (:256)) ==>
    word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)
Proof
  cheat
QED

(* Multiplicity at a prime scales with the exponent. *)
Theorem pow_prime_multiplicity[local]:
  !a e p. 0 < a ==>
    PRIME_FACTORS (a ** e) p = e * PRIME_FACTORS a p
Proof
  cheat
QED

(* An even power cannot equal an odd power of two.  This is the
   asymmetric signed lower endpoint used by the literal-exponent guard. *)
Theorem pow_two_odd_exponent:
  !a e k. 0 < a /\ a ** e = 2 ** k /\ ODD k ==> ODD e
Proof
  cheat
QED

(* The signed lower endpoint is included exactly for negative odd powers. *)
Theorem signed_power_bound:
  !a e bits. 0 < bits ==>
    (within_int_bound (Signed bits) (a ** e) <=>
     Num (ABS a) ** e < 2 ** (bits - 1) \/
     a < 0 /\ ODD e /\ Num (ABS a) ** e = 2 ** (bits - 1))
Proof
  cheat
QED

Theorem unsigned_power_bound:
  !a e bits. 0 <= a ==>
    (within_int_bound (Unsigned bits) (a ** e) <=>
     Num a ** e < 2 ** bits)
Proof
  cheat
QED

(* The ordinary signed literal-base guard, including its negative endpoint. *)
Theorem signed_literal_base_power_guard:
  !a bits k.
    0 < bits /\ 2 <= Num (ABS a) /\
    Num (ABS a) < 2 ** (bits - 1) ==>
    (k <= (           if a < 0 /\ ODD ((largest_pow_exponent (Num (ABS a)) bits T) + 1) /\
              Num (ABS a) ** ((largest_pow_exponent (Num (ABS a)) bits T) + 1) = 2 ** (bits - 1)
           then (largest_pow_exponent (Num (ABS a)) bits T) + 1 else (largest_pow_exponent (Num (ABS a)) bits T)) <=>
     within_int_bound (Signed bits) (a ** k))
Proof
  cheat
QED

Theorem unsigned_literal_base_power_guard:
  !a bits k.
    0 <= a /\ 2 <= Num a /\ Num a < 2 ** bits ==>
    (k <= largest_pow_exponent (Num a) bits F <=>
     within_int_bound (Unsigned bits) (a ** k))
Proof
  cheat
QED

Theorem largest_pow_exponent_at_limit:
  !b bits signed.
    2 <= b /\ 2 ** (bits - if signed then 1 else 0) <= b ==>
    largest_pow_exponent b bits signed = 1
Proof
  cheat
QED

Theorem largest_pow_base_endpoint:
  !e bits signed m.
    0 < e /\ m ** e = 2 ** (bits - if signed then 1 else 0) ==>
    m = largest_pow_base e bits signed + 1
Proof
  cheat
QED

(* Byte alignment makes every exact negative endpoint an odd power. *)
Theorem largest_pow_base_signed_threshold:
  !e bits m. 0 < e /\ ODD (bits - 1) ==>
    (m <= (           if ((largest_pow_base e bits T) + 1) ** e = 2 ** (bits - 1) then (largest_pow_base e bits T) + 1 else (largest_pow_base e bits T)) <=>
     m ** e < 2 ** (bits - 1) \/
     ODD e /\ m ** e = 2 ** (bits - 1))
Proof
  cheat
QED

Theorem signed_literal_exponent_power_guard:
  !a e bits. 0 < e /\ 0 < bits /\ ODD (bits - 1) ==>
    ((-&(if (largest_pow_base e bits T + 1) ** e = 2 ** (bits - 1)
           then largest_pow_base e bits T + 1 else largest_pow_base e bits T) <= a /\ a <= &(largest_pow_base e bits T)) <=>
     within_int_bound (Signed bits) (a ** e))
Proof
  cheat
QED

Theorem unsigned_literal_exponent_power_guard:
  !a e bits. 0 <= a /\ 0 < e ==>
    (a <= &(largest_pow_base e bits F) <=>
     within_int_bound (Unsigned bits) (a ** e))
Proof
  cheat
QED

Theorem byte_width_signed_endpoint_odd:
  !bits. 0 < bits /\ bits MOD 8 = 0 ==> ODD (bits - 1)
Proof
  cheat
QED

(* The signed minimum base is outside the strict safe-start search interface. *)
Theorem signed_minimum_power_guard:
  !bits k. 1 < bits ==>
    (k <= (           if ODD ((largest_pow_exponent (2 ** (bits - 1)) bits T) + 1) /\ (2 ** (bits - 1)) ** ((largest_pow_exponent (2 ** (bits - 1)) bits T) + 1) = (2 ** (bits - 1))
           then (largest_pow_exponent (2 ** (bits - 1)) bits T) + 1 else (largest_pow_exponent (2 ** (bits - 1)) bits T)) <=>
     within_int_bound (Signed bits) ((-&(2 ** (bits - 1))) ** k))
Proof
  cheat
QED

(* The three small literal bases never overflow at Vyper integer widths. *)
Theorem small_literal_base_power_bound:
  !a e bits signed.
    1 < bits /\ (a = -1 \/ a = 0 \/ a = 1) /\
    (~signed ==> 0 <= a) ==>
    within_int_bound (if signed then Signed bits else Unsigned bits) (a ** e)
Proof
  cheat
QED

(* Search outputs fit the comparison literals without modular truncation. *)
Theorem largest_pow_exponent_search_range[local]:
  !fuel b limit e.
    e <= largest_pow_exponent_search fuel b limit e /\
    largest_pow_exponent_search fuel b limit e <= e + fuel
Proof
  cheat
QED

Theorem largest_pow_exponent_le:
  !b bits signed. largest_pow_exponent b bits signed <= bits + 2
Proof
  cheat
QED

Theorem largest_pow_base_lt_limit:
  !e bits signed. 0 < e ==>
    largest_pow_base e bits signed < 2 ** (bits - if signed then 1 else 0)
Proof
  cheat
QED

(* Power's source boundary exposes both negative exponents and overflow. *)
Theorem bop_result_power:
  !cx ann tys a b es u.
    type_to_int_bound ann = SOME u ==>
    bop_result cx ann Exp tys (IntV a) (IntV b) es =
      if b < 0 then INR (Error (RuntimeError "Exp~"))
      else if within_int_bound u (a ** Num b)
           then INL (IntV (a ** Num b))
           else INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  cheat
QED

Theorem straight_fresh_compile_safe_pow:
  !x y ty bl el. straight_fresh (compile_safe_pow x y ty bl el)
Proof
  cheat
QED

(* The unconditional ASSERT/EXP branch used by exponents zero and one. *)
Theorem assert_true_exp_run:
  !x y sa op sb ss va vb.
    (do emit_void ASSERT [Lit 1w]; emit_op Exp [x; y] od) sa = (op, sb) /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (word_exp va vb)
Proof
  cheat
QED

(* ASSERT rejects exactly zero; on acceptance EXP uses the original operands. *)
Theorem assert_exp_run:
  !c x y sa op sb ss cv va vb.
    (do emit_void ASSERT [c]; emit_op Exp [x; y] od) sa = (op, sb) /\
    eval_operand c ss = SOME cv /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (cv <> 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (cv = 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* The unsigned upper guard shared by literal-base and literal-exponent code. *)
Theorem upper_guard_exp_run:
  !z x y upper sa op sb ss vz va vb.
    (do high <- emit_op GT [z; Lit upper];
        ok <- emit_op ISZERO [high];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\ eval_operand z ss = SOME vz /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (w2n vz <= w2n upper ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(w2n vz <= w2n upper) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* The signed interval guard used when only the exponent is literal. *)
Theorem signed_guard_exp_run:
  !x y lower upper sa op sb ss va vb.
    (do below <- emit_op SLT [x; Lit lower];
        ge <- emit_op ISZERO [below];
        above <- emit_op SGT [x; Lit upper];
        le <- emit_op ISZERO [above];
        ok <- emit_op AND [ge; le];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (w2i lower <= w2i va /\ w2i va <= w2i upper ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(w2i lower <= w2i va /\ w2i va <= w2i upper) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* Small signed literal bases need only reject negative exponents. *)
Theorem nonnegative_guard_exp_run:
  !x y sa op sb ss va vb.
    (do negative <- emit_op SLT [y; Lit 0w];
        ok <- emit_op ISZERO [negative];
        emit_void ASSERT [ok]; emit_op Exp [x; y] od) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME va /\ eval_operand y ss = SOME vb ==>
    (0 <= w2i vb ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (word_exp va vb)) /\
    (~(0 <= w2i vb) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* Successful integer type evaluation enforces byte-aligned widths. *)
Theorem int_type_byte_width:
  !tenv ty tv.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv ==>
    type_bits ty MOD 8 = 0
Proof
  cheat
QED

(* Typed nonnegative integers are represented without word truncation. *)
Theorem power_nonnegative_word_bound:
  !bits s z.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if s then Signed bits else Unsigned bits) z /\
    0 <= z ==>
    z < &(dimword (:256)) /\ w2n (i2w z : bytes32) = Num z
Proof
  cheat
QED

Theorem power_upper_word_signed:
  !k. k < 2 ** 255 ==> w2i (n2w k : bytes32) = &k
Proof
  cheat
QED

Theorem power_lower_word_signed:
  !k. k <= 2 ** 255 ==> w2i (i2w (-&k) : bytes32) = -&k
Proof
  cheat
QED

(* An unsigned comparison with a small threshold also rejects signed negatives. *)
Theorem power_exponent_word_guard:
  !bits s z k.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if s then Signed bits else Unsigned bits) z /\
    k < 2 ** 255 ==>
    (w2n (i2w z : bytes32) <= w2n (n2w k : bytes32) <=>
     0 <= z /\ Num z <= k)
Proof
  cheat
QED

(* Extend the literal-base threshold to every typed nonsmall base,
   including the signed minimum endpoint. *)
Theorem typed_literal_base_power_guard:
  !a bits signed k.
    1 < bits /\
    within_int_bound (if signed then Signed bits else Unsigned bits) a /\
    ~(a = -1 \/ a = 0 \/ a = 1) ==>
    (k <= (           if a < 0 /\ ODD ((largest_pow_exponent (Num (ABS a)) bits signed) + 1) /\
              Num (ABS a) ** ((largest_pow_exponent (Num (ABS a)) bits signed) + 1) = 2 ** (bits - if signed then 1 else 0)
           then (largest_pow_exponent (Num (ABS a)) bits signed) + 1 else (largest_pow_exponent (Num (ABS a)) bits signed)) <=>
     within_int_bound (if signed then Signed bits else Unsigned bits) (a ** k))
Proof
  cheat
QED

Theorem compile_safe_pow_base_run:
  !x y ty el a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\
    compile_safe_pow x y ty (SOME a) el sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

Theorem compile_safe_pow_exponent_run:
  !x y ty a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\ 0 <= b /\
    compile_safe_pow x y ty NONE (SOME b) sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

Theorem compile_safe_pow_run:
  !x y ty bl el a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> a = n) /\ (!n. el = SOME n ==> b = n) /\
    compile_safe_pow x y ty bl el sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* Checked + - * / % on two integers of one type. *)
Theorem binop_frag_int_arith:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  cheat
QED

(* A typed value of type decimal. *)
Theorem decimal_type_value:
  !tenv tv v.
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\ value_has_type tv v ==>
    ?d. v = DecimalV d /\ within_int_bound (Signed 168) d
Proof
  cheat
QED

(* Checked + - * / % on two decimals. *)
Theorem binop_frag_decimal_arith:
  !ctx func cenv cx bop bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) (BaseT DecimalT) bl el
      tys v1 v2 es0
Proof
  cheat
QED

(* The wrapping operators on two integers of one type of a whole number of
   bytes. *)
Theorem binop_frag_unsafe_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    is_int_type ty /\ type_bits ty MOD 8 = 0 /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  cheat
QED

(* The comparisons, min and max on two word values of one type. *)
Theorem binop_frag_compare_typed:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0 tenv tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* & | ^ on two word values of one type. *)
Theorem binop_frag_bitwise_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  cheat
QED

(* Flag membership on two flags of one type. *)
Theorem binop_frag_flag_in_typed:
  !ctx func cenv cx bop nsid ty ann bl el tys v1 v2 es0 tenv tv.
    (bop = In \/ bop = NotIn) /\
    evaluate_type tenv (FlagT nsid) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* A non-negative integer within the bound of an integer type of at most
   256 bits is a uint256. *)
Theorem within_int_bound_unsigned_256:
  !u n i.
    (u = Unsigned n \/ u = Signed n) /\ n <= 256 /\ within_int_bound u i /\
    0 <= i ==>
    within_int_bound (Unsigned 256) i
Proof
  cheat
QED

(* << and >> on a 256-bit integer by a non-negative amount. *)
Theorem binop_frag_shift_typed:
  !ctx func cenv cx bop ty t2 bl el tys v1 v2 es0 tenv tv1 tv2 i2.
    (bop = ShL \/ bop = ShR) /\ is_int_type ty /\ type_bits ty = 256 /\
    is_int_type t2 /\ v2 = IntV i2 /\ 0 <= i2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  cheat
QED

(* Power guards reflect source bounds when literal metadata agrees with
   the typed operands.  A base literal or nonnegative exponent literal is
   required; the emitted ASSERT rejects negative exponents and overflow. *)
Theorem binop_frag_pow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = Exp /\ well_typed_binop ann bop t1 t2 /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Right-shift arithmetic at genuinely narrow widths, independent of any
   checker restriction: signed and unsigned encodings widen safely to 256 bits. *)
Theorem binop_frag_shr_narrow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = ShR /\ type_bits t1 < 256 /\ ~(?i. v2 = IntV i /\ i < 0) /\
    ann = t1 /\ is_int_type t1 /\ is_int_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Accepted shifts retain the nonnegative evaluated amount.  ShL is
   full-width; ShR also uses the independently proved narrow arithmetic. *)
Theorem binop_frag_shift_572:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ (?i. v2 = IntV i /\ 0 <= i) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Instantiates a dispatch lemma at the current goal's variables and
   discharges its premises from the assumptions. *)
fun binop_dispatch_tac th =
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t1`, `t2`, `bl`,
               `el`, `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`, `tv2`]
    mp_tac th >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >>
  simp[];

(* Each operator on typed operands of word_value_types, by its group. *)
Theorem binop_frag_arith_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_unsafe_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_shift_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
    (?i. v2 = IntV i /\ 0 <= i) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_in_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = In \/ bop = NotIn) /\ well_typed_binop ann bop t1 t2 /\
    word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_rest_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_word_typed:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    (bop = Exp ==>
      (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
      (!n. bl = SOME n ==> v1 = IntV n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    word_value_type t1 /\ word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

Theorem binop_frag_typed:
  !ctx func cenv cx bop ann e1 e2 v1 v2 es0 tv1 tv2.
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    (bop = Exp ==>
      IS_SOME (expr_int_literal e1) \/
      ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
    (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    type_bits (expr_type e1) MOD 8 = 0 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop (expr_type e1) ann
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE)
      [expr_type e1; expr_type e2] v1 v2 es0
Proof
  cheat
QED
