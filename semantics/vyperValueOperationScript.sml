Theory vyperValueOperation
Ancestors
  arithmetic alist combin option list finite_map pair rich_list
  cv cv_std words integer[ignore_grammar]
  integer_word[ignore_grammar, qualified]
  vyperAST vyperMisc vyperValue
Libs
  cv_transLib wordsLib intSimps

(* Evaluation of some of the simpler language constructs *)

Definition evaluate_literal_def:
  evaluate_literal (BoolL b) = BoolV b ∧
  evaluate_literal (StringL s) = StringV s ∧
  evaluate_literal (BytesL bs) = BytesV bs ∧
  evaluate_literal (IntL i) = IntV i ∧
  evaluate_literal (DecimalL i) = DecimalV i
End

val () = cv_auto_trans evaluate_literal_def;

(* reading arrays *)

Definition array_length_def:
  array_length tv av =
  case av of
  | DynArrayV ls => LENGTH ls
  | SArrayV al => (case tv of ArrayTV _ (Fixed n) => n | _ => 0)
  | TupleV ls => LENGTH ls
End

val () = cv_trans array_length_def;

Definition evaluate_in_array_def:
  evaluate_in_array tv v av =
  case av of
  | DynArrayV ls => MEM v ls
  | SArrayV al => (case tv of
      ArrayTV t (Fixed n) =>
        MEM v (MAP SND al) ∨ (LENGTH al < n ∧ v = default_value t)
    | _ => MEM v (MAP SND al))
  | TupleV ls => MEM v ls
End

val () = cv_auto_trans $
  REWRITE_RULE[member_intro]evaluate_in_array_def;

Definition array_index_def:
  array_index tv av i =
  if 0 ≤ i then let j = Num i in
  case av
    of DynArrayV ls => oEL j ls
     | SArrayV al =>
         (case tv of
            ArrayTV t (Fixed n) =>
              if j < n then case ALOOKUP al j
              of SOME v => SOME v
               | NONE => SOME $ default_value t
              else NONE
          | _ => ALOOKUP al j)
     | TupleV ls => oEL j ls
  else NONE
End

val () = cv_trans array_index_def;

Definition array_elements_def:
  array_elements tv av =
    case av of TupleV vs => vs
    | DynArrayV vs => vs
    | SArrayV al =>
        (case tv of
           ArrayTV t (Fixed n) =>
             let d = default_value t in
               GENLIST (λi. case ALOOKUP al i of SOME v => v | NONE => d) n
         | _ => MAP SND al)
End

val () = cv_auto_trans array_elements_def;

Definition extract_elements_def:
  extract_elements tv (ArrayV av) = (SOME $ array_elements tv av) ∧
  extract_elements _ _ = NONE
End

val () = cv_auto_trans extract_elements_def;

(* error type for pure functions *)
Datatype:
  error = RuntimeError string | TypeError string
End

(* binary operators and bounds checking *)

Definition binop_negate_def:
  binop_negate (INL (BoolV b)) = INL (BoolV (¬b)) ∧
  binop_negate x = x
End

val () = cv_auto_trans binop_negate_def;

Definition bounded_int_op_def:
  bounded_int_op u r =
    if within_int_bound u r
    then INL (IntV r)
    else INR (RuntimeError "bounded_int_op bound")
End

(* optimisation on exponentiation: overflow immediately if power is too big *)
Theorem bounded_exp:
  bounded_int_op u (i1 ** n2) =
    if 2 ≤ ABS i1 ∧ int_bound_bits u < n2
    then INR (RuntimeError "bounded_int_op bound")
    else let r = i1 ** n2 in
      if within_int_bound u r then INL (IntV r)
    else INR (RuntimeError "bounded_int_op bound")
Proof
  rw[bounded_int_op_def]
  \\ gvs[int_exp_num]
  \\ `Num (ABS i1 ** n2) < 2 ** int_bound_bits u`
  by (
    reverse $ Cases_on`u`
    >- (
      gvs[within_int_bound_def]
      \\ gvs[INT_ABS]
      \\ IF_CASES_TAC
      \\ fsrw_tac[INT_ARITH_ss][Num_int_exp]
      \\ Cases_on`EVEN n2`
      \\ fsrw_tac[INT_ARITH_ss][] )
    \\ gvs[within_int_bound_def]
    \\ gvs[INT_ABS]
    \\ IF_CASES_TAC
    \\ fsrw_tac[INT_ARITH_ss][Num_int_exp]
    >- (
      Cases_on`EVEN n2`
      \\ fsrw_tac[INT_ARITH_ss][]
      >- (
        irule LESS_LESS_EQ_TRANS
        \\ goal_assum drule \\ simp[] )
      \\ irule LESS_EQ_LESS_TRANS
      \\ goal_assum $ drule_at Any \\ simp[] )
    \\ irule LESS_LESS_EQ_TRANS
    \\ goal_assum drule \\ simp[] )
  \\ gvs[Num_int_exp]
  \\ qmatch_asmsub_abbrev_tac`b < n2`
  \\ `2 ** b < 2 ** n2` by simp[]
  \\ qmatch_asmsub_abbrev_tac`n1 ** n2 < _`
  \\ `2 ≤ n1` by (
    simp[Abbr`n1`]
    \\ irule LE_NUM_OF_INT
    \\ simp[] )
  \\ `2 ** n2 ≤ n1 ** n2` by simp[]
  \\ `2n ** n2 < 2 ** b` by (
    irule LESS_EQ_LESS_TRANS
    \\ goal_assum drule \\ simp[] )
  \\ fs[]
QED

Definition bounded_decimal_op_def:
  bounded_decimal_op i =
  if within_int_bound (Signed 168) i
  then INL $ DecimalV i
  else INR (RuntimeError "bounded_decimal_op")
End

Definition signed_int_mod_def:
  signed_int_mod b i =
    let n = 2 ** b in
    let r = int_mod i &n in
      if r ≥ &(2 ** (b - 1)) then r - &n else r
End

(* signed_int_mod is equivalent to w2i (i2w i) at the corresponding word width *)
Theorem signed_int_mod_w2i:
  ∀i. signed_int_mod (dimindex(:'a)) i = w2i ((i2w i):'a word)
Proof
  rpt strip_tac
  >> simp[signed_int_mod_def, integer_wordTheory.w2i_eq_w2n,
          INT_MIN_def, dimword_def]
  >> `&(w2n ((i2w i):'a word)) = i % &(2 ** dimindex(:'a))`
       by simp[integer_wordTheory.w2n_i2w, dimword_def]
  >> pop_assum (fn th => REWRITE_TAC [SYM th])
  >> `(w2n ((i2w i):'a word) < 2 ** (dimindex(:'a) - 1))
       ⇔ ¬(&(w2n ((i2w i):'a word)):num ≥ &(2 ** (dimindex(:'a) - 1)))`
       by simp[INT_NOT_LE]
  >> pop_assum SUBST_ALL_TAC
  >> rw[]
  >> gvs[int_ge]
QED

Definition wrapped_int_op_def:
  wrapped_int_op u i =
    let b = int_bound_bits u in
      if is_Unsigned u then INL $ IntV (int_mod i &(2 ** b))
      else INL $ IntV (signed_int_mod b i)
End

val signed_int_mod_pre_def = cv_trans_pre "signed_int_mod_pre" signed_int_mod_def;

Theorem signed_int_mod_pre[cv_pre]:
  signed_int_mod_pre x y
Proof
  rw[signed_int_mod_pre_def]
QED

val wrapped_int_op_pre_def = cv_trans_pre "wrapped_int_op_pre" wrapped_int_op_def;

Theorem wrapped_int_op_pre[cv_pre]:
  wrapped_int_op_pre x y
Proof
  rw[wrapped_int_op_pre_def]
QED

Definition evaluate_binop_def:
  evaluate_binop u tv bop v1 v2 =
  case bop
    of Add => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (i1 + i2) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           bounded_decimal_op (i1 + i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Sub => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (i1 - i2) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           bounded_decimal_op (i1 - i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Mul => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (i1 * i2) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (let p = i1 * i2 in
            if within_int_bound (Signed 168) ((ABS p) / 10000000000)
            then INL $ DecimalV $ w2i $ word_quot (i2w p) (10000000000w: bytes32)
            else INR (RuntimeError "Decimal Mul bound")) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Div => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (if i2 = 0 then INR (RuntimeError "Div0") else
            bounded_int_op u $
              (if is_Unsigned u
               then &(w2n $ word_div ((i2w i1):bytes32) (i2w i2))
               else w2i $ word_quot ((i2w i1):bytes32) (i2w i2)))
                | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (if i2 = 0 then INR (RuntimeError "Div0") else
            bounded_decimal_op $
              w2i $ word_quot ((i2w (i1 * 10000000000)):bytes32) (i2w i2))
                         | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | UAdd => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           wrapped_int_op u (i1 + i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | USub => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           wrapped_int_op u (i1 - i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | UMul => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           wrapped_int_op u (i1 * i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | UDiv => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           if i2 = 0 then INR (RuntimeError "UDiv0") else
           wrapped_int_op u (i1 / i2) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Mod => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (if i2 = 0 then INR (RuntimeError "Mod0") else
            bounded_int_op u $
              (if is_Unsigned u
               then &(w2n $ word_mod ((i2w i1):bytes32) (i2w i2))
               else w2i $ word_rem ((i2w i1):bytes32) (i2w i2)))
                | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (if i2 = 0 then INR (RuntimeError "Mod0") else
            bounded_decimal_op $
              (w2i $ word_rem ((i2w i1):bytes32) (i2w i2)))
                         | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Exp => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (if i2 < 0 then INR (RuntimeError "Exp~") else
            bounded_int_op u $ (i1 ** (Num i2))) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | ExpMod => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (if u = Unsigned 256
            then INL $ IntV (w2i (word_exp (i2w i1 : bytes32) (i2w i2)))
            else INR (TypeError "ExpMod")) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | ShL => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (if i2 < 0 then INR (RuntimeError "ShL0")
            else let r = int_shift_left (Num i2) i1;
                     b = int_bound_bits u in
              if is_Unsigned u then INL $ IntV (int_mod r &(2 ** b))
              else INL $ IntV (signed_int_mod b r))
           | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | ShR => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           (* TODO: check type constraints on shifts *)
           (if i2 < 0 then INR (RuntimeError "ShR0")
            else INL $ IntV $ int_shift_right (Num i2) i1) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | And => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (int_and i1 i2) | _ => INR (TypeError "binop"))
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ∧ b2) | _ => INR (TypeError "binop"))
       | FlagV n1 => (case v2 of FlagV n2 =>
           INL $ FlagV (Num(int_and (&n1) (&n2))) (* TODO: bitwise nums *)
           | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Or => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (int_or i1 i2) | _ => INR (TypeError "binop"))
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ∨ b2) | _ => INR (TypeError "binop"))
       | FlagV n1 => (case v2 of FlagV n2 =>
           INL $ FlagV (Num(int_or (&n1) (&n2))) (* TODO: bitwise nums *)
           | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | XOr => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           bounded_int_op u (int_xor i1 i2) | _ => INR (TypeError "binop"))
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ≠ b2) | _ => INR (TypeError "binop"))
       | FlagV n1 => (case v2 of FlagV n2 =>
           INL $ FlagV (Num(int_xor (&n1) (&n2))) (* TODO: bitwise nums *)
           | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | In => (case v2 of
         FlagV n2 => (case v1 of FlagV n1 =>
           INL $ BoolV (int_and (&n1) (&n2) ≠ 0) (* TODO: use bitwise ∧ on nums *)
           | _ => INR (TypeError "binop"))
       | ArrayV av => INL $ BoolV $ evaluate_in_array NoneTV v1 av
       | _ => INR (TypeError "binop"))
     | Eq => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (BoolV (i1 = i2)) | _ => INR (TypeError "binop"))
       | FlagV n1 => (case v2 of FlagV n2 =>
           INL (BoolV (n1 = n2)) | _ => INR (TypeError "binop"))
       | StringV s1 => (case v2 of StringV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR (TypeError "binop"))
       | BytesV s1 => (case v2 of BytesV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR (TypeError "binop"))
       | BoolV s1 => (case v2 of BoolV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR (TypeError "binop"))
       | DecimalV s1 => (case v2 of DecimalV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Lt => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (BoolV (i1 < i2)) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 < i2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Gt => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (BoolV (i1 > i2)) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 > i2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | LtE => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (BoolV (i1 ≤ i2)) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 ≤ i2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | GtE => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (BoolV (i1 ≥ i2)) | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 ≥ i2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Min => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (IntV (if i1 < i2 then i1 else i2))
           | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (DecimalV (if i1 < i2 then i1 else i2)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | Max => (case v1 of
         IntV i1 => (case v2 of IntV i2 =>
           INL (IntV (if i1 < i2 then i2 else i1))
           | _ => INR (TypeError "binop"))
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (DecimalV (if i1 < i2 then i2 else i1)) | _ => INR (TypeError "binop"))
       | _ => INR (TypeError "binop"))
     | NotIn => binop_negate $ evaluate_binop u tv In v1 v2
     | NotEq => binop_negate $ evaluate_binop u tv Eq v1 v2
     | _ => INR (TypeError "binop")
Termination
  WF_REL_TAC ‘inv_image $< (λ(u,tv,b,x,y). if b = NotIn ∨ b = NotEq then 2n else 0n)’
  \\ rw[]
End

val cv_NotIn_tm = rand $ rhs $ concl $ cv_eval_raw “NotIn”;
val cv_NotEq_tm = rand $ rhs $ concl $ cv_eval_raw “NotEq”;

val () = cv_auto_trans_rec
  (REWRITE_RULE [bounded_exp, COND_RATOR] evaluate_binop_def)
  (WF_REL_TAC
    ‘inv_image $< (λ(u,tv,b,x,y).
       if b = ^cv_NotIn_tm ∨ b = ^cv_NotEq_tm
       then 2n else 0n)’
   \\ rw[] \\ rw[] \\ gvs[]
   \\ Cases_on`cv_bop` \\ gvs[]
   \\ rw[]);

(* concat *)

Definition init_concat_output_def:
  init_concat_output (BytesV bs) = SOME $ BytesV bs ∧
  init_concat_output (StringV s) = SOME $ StringV s ∧
  init_concat_output _ = NONE
End

val () = cv_auto_trans init_concat_output_def;

Definition evaluate_concat_loop_def:
  evaluate_concat_loop n (StringV s1) sa ba [] =
  (let s = FLAT $ s1::REVERSE sa in
   (if compatible_bound (Dynamic n) (LENGTH s)
    then INL (StringV s)
    else INR (RuntimeError "concat bound"))) ∧
  evaluate_concat_loop n (BytesV b1) sa ba [] =
  (let bs = FLAT $ b1::REVERSE ba in
   (if compatible_bound (Dynamic n) (LENGTH bs)
    then INL (BytesV bs)
    else INR (RuntimeError "concat bound"))) ∧
  evaluate_concat_loop n (StringV s1) sa ba ((StringV s2)::vs) =
  evaluate_concat_loop n (StringV s1) (s2::sa) ba vs ∧
  evaluate_concat_loop n (BytesV b1) sa ba ((BytesV b2)::vs) =
  evaluate_concat_loop n (BytesV b1) sa (b2::ba) vs ∧
  evaluate_concat_loop _ _ _ _ _ = INR (TypeError "concat types")
End

val () = cv_auto_trans evaluate_concat_loop_def;

Definition evaluate_concat_def:
  evaluate_concat n vs =
  if NULL vs ∨ NULL (TL vs) then INR (TypeError "concat <2")
  else
    case init_concat_output (HD vs)
      of SOME v => evaluate_concat_loop n v [] [] (TL vs)
       | NONE => INR (TypeError "concat type or bound")
End

val evaluate_concat_pre_def = cv_auto_trans_pre "evaluate_concat_pre" evaluate_concat_def;

Theorem evaluate_concat_pre[cv_pre]:
  evaluate_concat_pre b vs
Proof
  rw[evaluate_concat_pre_def]
  \\ strip_tac \\ gvs[]
QED

(* slice *)

Definition evaluate_slice_def:
  evaluate_slice v sv lv n =
  let b = Dynamic n in
  case dest_NumV sv of NONE => INR (TypeError "evaluate_slice start") | SOME start =>
  case dest_NumV lv of NONE => INR (TypeError "evaluate_slice length") | SOME length =>
  case v
  of BytesV bs => (
       if start + length ≤ LENGTH bs then
       if compatible_bound b length then
         INL $ BytesV (TAKE length (DROP start bs))
       else INR (RuntimeError "evaluate_slice bound")
       else INR (RuntimeError "evaluate_slice range"))
   | StringV s => (
       if start + length ≤ LENGTH s then
       if compatible_bound b length then
         INL $ StringV (TAKE length (DROP start s))
       else INR (RuntimeError "evaluate_slice bound")
       else INR (RuntimeError "evaluate_slice range"))
  | _ => INR (TypeError "evaluate_slice v")
End

val () = cv_auto_trans evaluate_slice_def;

(* some more builtins *)

Definition evaluate_as_wei_value_def:
  evaluate_as_wei_value dn v =
  let m = case dn of
          | Wei => 1
          | Kwei => 1000
          | Mwei => 1000000
          | Gwei => 1000000000
          | Szabo => 1000000000000
          | Finney => 1000000000000000
          | Ether => 1000000000000000000
          | KEther => 1000000000000000000000
          | MEther => 1000000000000000000000000
          | GEther => 1000000000000000000000000000
          | TEther => 1000000000000000000000000000000 in
  let r = case v of IntV i => i * m
                  | DecimalV i => (i * m) / 10000000000
                  | _ => -1 in
  if 0 ≤ r then
    let u = Unsigned 256 in
    if within_int_bound u r then
      INL $ IntV r
    else INR (RuntimeError "ewv bound")
  else INR (TypeError "ewv neg")
End

val evaluate_as_wei_value_pre_def =
  cv_auto_trans_pre "evaluate_as_wei_value_pre" evaluate_as_wei_value_def;

Theorem evaluate_as_wei_value_pre[cv_pre]:
  evaluate_as_wei_value_pre x y
Proof
  rw[evaluate_as_wei_value_pre_def]
QED

Definition evaluate_max_value_def:
  evaluate_max_value (BaseT (UintT n)) = INL $ IntV (&(2 ** n) - 1) ∧
  evaluate_max_value (BaseT (IntT n)) = (if n = 0
                                         then INR (TypeError "max_value IntT")
                                         else INL $ IntV (&(2 ** (n-1)) - 1)) ∧
  evaluate_max_value (BaseT DecimalT) = INL $ DecimalV (&(2 ** 167) - 1) ∧
  evaluate_max_value _ = INR (TypeError "evaluate_max_value")
End

val () = cv_auto_trans evaluate_max_value_def;

Definition evaluate_min_value_def:
  evaluate_min_value (BaseT (UintT n)) = INL $ IntV 0 ∧
  evaluate_min_value (BaseT (IntT n)) = (if n = 0
                                         then INR (TypeError "min_value IntT")
                                         else INL $ IntV (-&(2 ** (n-1)))) ∧
  evaluate_min_value (BaseT DecimalT) = INL $ DecimalV (-&(2 ** 167)) ∧
  evaluate_min_value _ = INR (TypeError "evaluate_min_value")
End

val () = cv_auto_trans evaluate_min_value_def;

(* subscripting into arrays, structs, hashmaps *)

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => INL v
   | _ => INR (TypeError "attribute")) ∧
  evaluate_attribute _ _ = INR (TypeError "evaluate_attribute")
End

val () = cv_auto_trans evaluate_attribute_def;

(* convert *)

Definition evaluate_convert_def:
  evaluate_convert (BytesV bs) (BaseT BoolT) =
    INL $ BoolV (EXISTS (λb. b ≠ 0w) bs) ∧
  evaluate_convert (IntV i) (BaseT BoolT) = INL $ BoolV (i ≠ 0) ∧
  evaluate_convert (BoolV b) (BaseT (IntT n)) =
    INL $ IntV (if b then 1 else 0) ∧
  evaluate_convert (BoolV b) (BaseT (UintT n)) =
    INL $ IntV (if b then 1 else 0) ∧
  evaluate_convert (BytesV bs) (BaseT (BytesT (Fixed n))) =
    (if LENGTH bs ≤ n
     then INL $ BytesV (PAD_RIGHT 0w n bs)
     else INR (RuntimeError "convert BytesV bound")) ∧
  evaluate_convert (BytesV bs) (BaseT (BytesT (Dynamic n))) =
    (if LENGTH bs ≤ n
     then INL $ BytesV bs
     else INR (RuntimeError "convert BytesV bound")) ∧
  evaluate_convert (BytesV bs) (BaseT (UintT n)) =
    (let i = &(w2n $ (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32)) in
     if within_int_bound (Unsigned n) i
     then INL $ IntV i
     else INR (RuntimeError "convert BytesV uint bound")) ∧
  evaluate_convert (BytesV bs) (BaseT (IntT n)) =
    (let i = w2i $ (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) in
     if within_int_bound (Signed n) i
     then INL $ IntV i
     else INR (RuntimeError "convert BytesV int bound")) ∧
  evaluate_convert (IntV i) (BaseT (IntT n)) =
    (if within_int_bound (Signed n) i
     then INL $ IntV i
     else INR (RuntimeError "convert int bound")) ∧
  evaluate_convert (IntV i) (BaseT (UintT n)) =
    (if within_int_bound (Unsigned n) i
     then INL $ IntV i
     else INR (RuntimeError "convert uint bound")) ∧
  evaluate_convert (IntV i) (BaseT AddressT) =
    (if within_int_bound (Unsigned 160) i
     then INL $ AddressV (i2w i)
     else INR (RuntimeError "convert int address")) ∧
  evaluate_convert (FlagV m) (BaseT (IntT n)) =
    (let i = &m in
     if within_int_bound (Signed n) i
     then INL $ IntV i
     else INR (RuntimeError "convert flag int bound")) ∧
  evaluate_convert (FlagV m) (BaseT (UintT n)) =
    (let i = &m in
     if within_int_bound (Unsigned n) i
     then INL $ IntV i
     else INR (RuntimeError "convert flag uint bound")) ∧
  evaluate_convert (IntV i) (BaseT (BytesT bd)) =
  (* TODO: check and use type for width etc. *)
    (if compatible_bound bd 32
     then INL $ BytesV (word_to_bytes_be ((i2w i):bytes32))
     else INR (RuntimeError "convert int to bytes")) ∧
  evaluate_convert (BytesV bs) (BaseT (StringT n)) =
    (if LENGTH bs ≤ n
     then INL $ StringV (MAP (CHR o w2n) bs)
     else INR (RuntimeError "convert bytes string")) ∧
  evaluate_convert (StringV s) (BaseT (StringT n)) =
    (if LENGTH s ≤ n
     then INL $ StringV s
     else INR (RuntimeError "convert string string bound")) ∧
  evaluate_convert (StringV s) (BaseT (BytesT bd)) =
    (if compatible_bound bd (LENGTH s)
     then INL $ BytesV (MAP (n2w o ORD) s)
     else INR (RuntimeError "convert string bytes")) ∧
  evaluate_convert (IntV i) (BaseT DecimalT) =
    bounded_decimal_op (i * 10000000000) ∧
  evaluate_convert (DecimalV i) (BaseT (IntT n)) =
    (if within_int_bound (Signed 168) ((ABS i) / 10000000000)
     then INL $ IntV (i / 10000000000)
     else INR (RuntimeError "convert decimal int")) ∧
  evaluate_convert (DecimalV i) (BaseT (UintT n)) =
    (let r = i / 10000000000 in
     if 0 ≤ i ∧ within_int_bound (Signed 168) r
     then INL $ IntV r
     else INR (RuntimeError "convert decimal uint")) ∧
  evaluate_convert _ _ = INR (TypeError "convert")
End

val evaluate_convert_pre_def =
  cv_auto_trans_pre "evaluate_convert_pre" $
  REWRITE_RULE [GSYM CHR_o_w2n_eq]
  evaluate_convert_def;

Theorem evaluate_convert_pre[cv_pre]:
  evaluate_convert_pre x y
Proof
  rw[evaluate_convert_pre_def]
QED

(* implicit conversion from one type to another, used e.g. for function
* calls/returns. only "safe" conversions are allowed, e.g., extending the
* maximum length of a dynamic array*)

Definition safe_cast_def:
  safe_cast t v = (
  case t of
  | BaseTV (UintT n) =>
    (case v of
     | IntV i => if within_int_bound (Unsigned n) i then SOME v else NONE
     | _ => NONE)
  | BaseTV (IntT n) =>
    (case v of
     | IntV i => if within_int_bound (Signed n) i then SOME v else NONE
     | _ => NONE)
  | BaseTV BoolT =>
    (case v of
     | BoolV _ => SOME v
     | _ => NONE)
  | BaseTV DecimalT =>
    (case v of
     | DecimalV d => if within_int_bound (Signed 168) d then SOME v else NONE
     | _ => NONE)
  | BaseTV (StringT n) =>
    (case v of
     | StringV str
       => if LENGTH str ≤ n then SOME v else NONE
     | _ => NONE)
  | BaseTV (BytesT (Fixed n)) =>
    (case v of
     | BytesV bs => if LENGTH bs = n then SOME v else NONE
     | _ => NONE)
  | BaseTV (BytesT (Dynamic n)) =>
    (case v of
     | BytesV bs =>
       if LENGTH bs ≤ n then SOME v else NONE
     | _ => NONE)
  | BaseTV AddressT =>
    (case v of
     | BytesV bs => if LENGTH bs = 20 then SOME v else NONE
     | _ => NONE)
  | FlagTV n =>
    (case v of
     | FlagV m => if m < 2 ** n then SOME v else NONE
     | _ => NONE)
  | TupleTV ts =>
    (case v of
     | ArrayV (TupleV vs) =>
       (case safe_cast_list ts vs []
        of SOME vs => SOME $ ArrayV (TupleV vs)
        | _ => NONE)
     | _ => NONE)
  | ArrayTV t bd =>
    (case (bd, v) of
     | (Dynamic n, ArrayV (DynArrayV vs)) =>
       (let lvs = LENGTH vs in
        if n < lvs then NONE else
        case safe_cast_list (REPLICATE lvs t) vs []
        of SOME vs => SOME $ ArrayV (DynArrayV vs)
         | _ => NONE)
     | (Fixed n, ArrayV (SArrayV al)) =>
       (if n < LENGTH al then NONE else
        case safe_cast_list (REPLICATE (LENGTH al) t) (MAP SND al) []
        of SOME vs => SOME $ ArrayV (SArrayV (ZIP (MAP FST al, vs)))
         | _ => NONE)
     | _ => NONE)
  | StructTV args =>
    (case v of StructV al =>
      (let names = MAP FST al in
       if names = MAP FST args then
       (case safe_cast_list (MAP SND args) (MAP SND al) []
        of SOME vs => SOME $ StructV (ZIP (names, vs))
        | _ => NONE)
       else NONE)
     | _ => NONE)
  | NoneTV =>
    (case v of NoneV => SOME v
     | _ => NONE)) ∧
  safe_cast_list [] [] acc = SOME $ REVERSE acc ∧
  safe_cast_list (t::ts) (v::vs) acc = (
    case safe_cast t v of
    | SOME v => safe_cast_list ts vs (v::acc)
    | _ => NONE) ∧
  safe_cast_list _ _ _ = NONE
Termination
  WF_REL_TAC `measure (λx. case x of
    INR (_,vs,_) => list_size value_size vs
  | INL (_,v) => value_size v)`
  \\ rw[list_size_SUM_MAP, list_size_pair_size_map]
End

val safe_cast_pre_def = cv_auto_trans_pre_rec
  "safe_cast_pre safe_cast_list_pre" safe_cast_def (
  WF_REL_TAC `measure (λx. case x of
    INR (_,vs,_) => cv_size vs
  | INL (_,v) => cv_size v)`
  \\ rw[]
  \\ Cases_on`cv_v` \\ gvs[cv_size_def, cv_snd_def]
  \\ TRY (rename1`cv_snd g2` \\ Cases_on`g2`
          \\ gvs[cv_size_def, cv_snd_def] \\ NO_TAC)
  \\ TRY (rename1`cv_map_snd (cv_snd g2)` \\
          qspec_then`cv_snd g2`mp_tac
            cv_size_cv_map_snd_le \\
            Cases_on`g2` \\ simp[] \\ NO_TAC)
  \\ TRY (qmatch_goalsub_rename_tac`cv_map_snd p`
    \\ qspec_then`p`mp_tac cv_size_cv_map_snd_le \\ simp[] \\ NO_TAC)
);

Theorem safe_cast_pre[cv_pre]:
  (∀t v. safe_cast_pre t v) ∧
  (∀x y z. safe_cast_list_pre x y z)
Proof
  ho_match_mp_tac safe_cast_ind \\ rw[]
  \\ rw[Once safe_cast_pre_def]
QED

(* mutating arrays *)

Definition append_element_def:
  append_element tv (ArrayV (DynArrayV vs)) v =
    (case tv of ArrayTV elem_tv (Dynamic n) =>
       if compatible_bound (Dynamic n) (SUC (LENGTH vs))
       then case safe_cast elem_tv v of NONE => INR (TypeError "append cast")
            | SOME v => INL $ ArrayV $ DynArrayV (SNOC v vs)
       else INR (RuntimeError "append overflow")
     | _ => INR (TypeError "append_element type")) ∧
  append_element _ _ _ = INR (TypeError "append_element")
End

val () = cv_auto_trans append_element_def;

Definition pop_element_def:
  pop_element (ArrayV (DynArrayV vs)) =
    (if vs = [] then INR (RuntimeError "pop empty")
     else INL $ ArrayV $ DynArrayV (FRONT vs)) ∧
  pop_element _ = INR (TypeError "pop_element")
End

val () = cv_auto_trans pop_element_def;

Definition popped_value_def:
  popped_value (ArrayV (DynArrayV vs)) =
    (if vs = [] then INR (RuntimeError "pop empty") else INL $ LAST vs) ∧
  popped_value _ = INR (TypeError "popped_value")
End

val () = cv_auto_trans popped_value_def;

Definition insert_sarray_def:
  insert_sarray k v [] = [(k:num,v:value)] ∧
  insert_sarray k v ((k1,v1)::al) =
  if k = k1 then ((k,v)::al)
  else if k < k1 then (k,v)::(k1,v1)::al
  else (k1,v1)::(insert_sarray k v al)
End

val () = cv_trans insert_sarray_def;

Definition array_set_index_def:
  array_set_index tv av i v =
  if 0 ≤ i then let j = Num i in
    case av of DynArrayV vs =>
      if j < LENGTH vs then
        INL $ ArrayV $ DynArrayV (TAKE j vs ++ [v] ++ DROP (SUC j) vs)
      else INR (RuntimeError "array_set_index index")
    | SArrayV al =>
      (case tv of ArrayTV t (Fixed n) =>
        if j < n then
          INL $ ArrayV $ SArrayV $
          if v = default_value t then
            ADELKEY j al
          else
            insert_sarray j v al
        else INR (RuntimeError "array_set_index size")
      | _ => INR (TypeError "array_set_index type"))
    | TupleV vs => INR (TypeError "array_set_index tuple")
  else INR (TypeError "array_set_index negative")
End

val () = cv_auto_trans array_set_index_def;
