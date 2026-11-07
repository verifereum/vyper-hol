(*
 * Expression simulation for convert (#636, part 3)
 *
 * convert(e, t) of a non-bytestring lowers to e's fragment and
 * compile_type_convert, with ConvToFlag for a flag target and mk_convert_op
 * otherwise (lower_value_convert).  compile_convert_frag_sim builds
 * expr_sim of the whole from expr_sim of the argument and a unop_frag for
 * the conversion code f; compile_convert_frag_sim_word specializes it to
 * word conversions and convert_frag (via convert_frag_unop).
 *
 * TOP-LEVEL:
 *   compile_convert_word_case  — expr_vv_case of a conversion between
 *                                integer types, from bool to an integer
 *                                or from an integer to bool
 *   compile_convert_frag_sim   — the composition
 *   compile_convert_frag_sim_word — its word-to-word specialization
 *   compile_convert_int_frag   — convert_frag between integer types
 *                                (ConvIntToInt)
 *   compile_convert_bool_frag  — convert_frag from an integer to bool
 *   convert_int_run            — compile_type_convert between integer
 *                                types, both outcomes
 *
 * Covered are the conversions between integers and from bool to an
 * integer, and from an integer to bool, where the lowering and the source
 * agree.  Boolean to integer conversion is an identity on its encoded word.
 * The rest wait on #548: there the checker, the lowering and the
 * semantics disagree.  compile_convert_word_case takes the argument's
 * compile-state shape from exprSimOperators' lower_value_word_shape.
 *
 * Helpers: eval_expr_convert_cases, eval_expr_convert_action,
 * convert_operand_admissible, convert_exempt_cert,
 * convert_continuation_summary, expr_post_convert, convert_frag_straight,
 * convert_int_clamp, convert_u2s_clamp, convert_bool_run.
 *)

Theory exprSimConvert
Ancestors
  exprUnopSimDefs fragGasFresh gasContext gasSummary gasOutcome
  gasSummaryCompose gasExemptCert fragGasPath fragGasMode
  exprWordOperand exprSimSource exprSimProps exprSimHypsDefs exprSimDefs exprSimStack loweringPosts allocLimits exprSimUnop
  arithmetic list integer words integer_word
  fragExec varsExt  freshWrites exprSimOps exprSimArith
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps arithmeticProps
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation vyperArith valueEncoding venomExecSemantics venomInst
  venomState exprSimHyps exprSimOperators vyperTyping vyperTypeSystem
  vyperTypeCallGraph
Libs
  intLib pairLib

(* ===== Lowering of convert ===== *)

Theorem is_word_type_not_bytestring:
  !t. is_word_type t ==> ~is_bytestring_type t
Proof
  cheat
QED

(* A non-bytestring conversion selects ConvToFlag for flags and
   mk_convert_op for all other target types. *)
Theorem lower_value_convert:
  !cenv ty ann t e1 sa op sb.
    ~is_bytestring_type (expr_type e1) /\
    lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa =
      (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e1) e1 sa = (x, s1) /\
      compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (expr_type e1) t) s1 = (op, sb)
Proof
  cheat
QED

(* ===== Evaluating convert ===== *)

(* The source result of convert on a value, as eval_expr gives it for
   TypeBuiltin ann Convert t [e1] once e1 is evaluated to v, unless e1 is
   an address and t a bytesM (evaluate_convert_from). *)
Definition convert_result_def:
  convert_result cx src t v =
    case evaluate_convert_from (get_tenv cx) src v t of
      INL v' => INL v'
    | INR e => INR (Error e)
End

Theorem eval_expr_convert_cases:
  !cx ann t e1 es res es'.
    (do result <- eval_expr cx (TypeBuiltin ann Convert t [e1]);
        read_result cx result od) es = (res, es') ==>
    (?exc. (do result <- eval_expr cx e1; read_result cx result od) es =
             (INR exc, es') /\ res = INR exc) \/
    ?v1. (do result <- eval_expr cx e1; read_result cx result od) es =
           (INL v1, es') /\ res = convert_result cx (expr_type e1) t v1
Proof
  cheat
QED

Theorem eval_expr_convert_of_child:
  !cx ann ty e es v ee.
    bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
    bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx) es =
      (convert_result cx (expr_type e) ty v, ee)
Proof
  cheat
QED

(* ===== The conversion's fragment ===== *)

(* The conversion's fragment, from the argument holding v1 in a state
   related at es0, the source state after the argument: on a value its
   counted path reaches its end with the result, a word value, held by op,
   keeping the variables handed out before it, the allocations and the
   memory; on an error it exits as expr_exit allows. *)
Definition convert_frag_def:
  convert_frag ctx func cenv cx src conv t v1 es0 <=>
    !sa sb x op s0.
      compile_type_convert x conv sa = (op, sb) /\
      expr_res_ok (convert_result cx src t v1) /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\
      eval_operand x s0 = SOME (val_to_w256 v1) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path F ctx func s0 0 r /\
        ((?s v. r = OK s /\ convert_result cx src t v1 = INL v /\
                word_value v /\
                stmt_state_rel ctx func cenv cx es0 s /\
                eval_operand op s = SOME (val_to_w256 v) /\
                (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                       lookup_var z s = SOME w) /\
                (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                s.vs_current_bb = sb.cs_current_bb /\
                s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
         (exit_result r /\ expr_exit (convert_result cx src t v1) r))
End

Theorem convert_frag_unop:
  !ctx func cenv cx src conv t v1 es0 ann tv1.
    word_value v1 /\ is_word_type ann /\
    convert_frag ctx func cenv cx src conv t v1 es0 ==>
    unop_frag ctx func cenv cx (\x. compile_type_convert x conv)
      (typed_val_to_w256 tv1 v1) ann (convert_result cx src t v1) es0
Proof
  cheat
QED

Theorem expr_post_convert:
  !func cenv cx ann t e1 es es' sa s1 sb s0 t0 ss x op v1 v ctx.
    expr_post ctx func cenv cx e1 es sa s1 s0 es' v1 x t0 /\
    stmt_state_rel ctx func cenv cx es' ss /\
    expr_val_rel cx ann v op ss /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
           lookup_var z ss = SOME w) /\
    (!aid b. FLOOKUP t0.vs_allocas aid = SOME b ==>
             FLOOKUP ss.vs_allocas aid = SOME b) /\
    ss.vs_memory = t0.vs_memory /\
    is_word_type ann /\ sa.cs_next_var <= s1.cs_next_var ==>
    expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0 es'
      v op ss
Proof
  cheat
QED

(* The source action of a conversion: the argument's, then
   convert_result, which reads no state. *)
Theorem eval_expr_convert_action:
  bind (eval_expr cx (TypeBuiltin ann Convert t [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. (convert_result cx (expr_type e) t v, es))
Proof
  cheat
QED

Theorem convert_operand_admissible:
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  cheat
QED

Theorem convert_exempt_cert:
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) (return ())) start marks out endpoint
Proof
  cheat
QED

(* The conversion's code after the argument, as a counted summary. *)
Theorem convert_continuation_summary:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
    (convert_result cx (expr_type e1) t v1) (ee with gas_obs := []) /\
  expr_res_ok (convert_result cx (expr_type e1) t v1) /\
  f x s1 = (op,sb) /\ (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s1 /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at F (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) t v1,vs))
    (ee with gas_obs := [],t0)
    (\res fin t'. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0
        fin v op t' /\
      t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  cheat
QED

(* expr_sim of a conversion from expr_sim of its argument and unop_frag
   for the conversion's code. *)
Theorem compile_convert_frag_sim:
  !ctx func cenv cx ty ann t e1 f es.
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa = (op,sb) ==>
       ?x s1. lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
              f x s1 = (op,sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op,sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op,sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do r <- eval_expr cx e1; read_result cx r od)
        (es with gas_obs := gs1) = (INL v1,es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
         unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
           (convert_result cx (expr_type e1) t v1) es1) ==>
    expr_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  cheat
QED



(* Word-only specialization of the abstract composition interface. *)
Theorem compile_convert_frag_sim_word:
  !ctx func cenv cx ty ann t e1 es.
    (!n. t <> FlagT n) /\ is_word_type ann /\
    is_word_type (expr_type e1) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x sa sb op.
       compile_type_convert x (mk_convert_op (expr_type e1) t) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do result <- eval_expr cx e1; read_result cx result od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
       word_value v1 /\
       convert_frag ctx func cenv cx (expr_type e1) (mk_convert_op (expr_type e1) t) t v1 es1) ==>
    expr_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  cheat
QED

val sf_step = FIRST [
  irule straight_fresh_bind >> conj_tac,
  irule straight_fresh_ignore_bind >> conj_tac,
  gen_tac >> BETA_TAC,
  irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
  irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
  MATCH_ACCEPT_TAC straight_fresh_return,
  IF_CASES_TAC];

Theorem straight_fresh_convert:
  !x in_s in_b out_s out_b.
    straight_fresh (compile_type_convert x (ConvIntToInt in_s in_b out_s out_b)) /\
    straight_fresh (compile_type_convert x ConvToBool)
Proof
  cheat
QED

(* convert_frag from the run facts of the conversion's straight-line code. *)
Theorem convert_frag_straight:
  !ctx func cenv cx conv t v1 es0.
    (!x. straight_fresh (compile_type_convert x conv)) /\
    (expr_res_ok (convert_result cx src t v1) ==>
     (?v. convert_result cx src t v1 = INL v /\ word_value v /\
          !x sa sb op ss.
            compile_type_convert x conv sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (val_to_w256 v)) \/
     (?m. convert_result cx src t v1 = INR (Error (RuntimeError m)) /\
          !x sa sb op ss.
            compile_type_convert x conv sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    convert_frag ctx func cenv cx src conv t v1 es0
Proof
  cheat
QED

(* ===== Integer to integer ===== *)

Theorem within_int_bound_ineq:
  !b i.
    (within_int_bound (Unsigned b) i <=> 0 <= i /\ i < &(2 ** b)) /\
    (0 < b ==>
     (within_int_bound (Signed b) i <=>
      -&(2 ** (b - 1)) <= i /\ i < &(2 ** (b - 1))))
Proof
  cheat
QED

(* A narrowing between two integer types of one signedness is the target's
   clamp. *)
Theorem convert_int_clamp:
  !v s in_b out_b.
    out_b < in_b ==>
    compile_type_convert v (ConvIntToInt s in_b s out_b) =
    clamp_and_return v (BaseT (if s then IntT out_b else UintT out_b))
Proof
  cheat
QED

(* An unsigned source and a signed target of b bits: the clamp of an
   unsigned integer of b - 1 bits. *)
Theorem convert_u2s_clamp:
  !v in_b out_b.
    compile_type_convert v (ConvIntToInt F in_b T out_b) =
    clamp_and_return v (BaseT (UintT (out_b - 1)))
Proof
  cheat
QED

(* compile_type_convert between two integer types, both outcomes: the value
   passes through when it is within the target's bound, and the code
   reverts when it is not. *)
Theorem convert_int_run:
  !v in_s in_b out_s out_b i ss st op st'.
    compile_type_convert v (ConvIntToInt in_s in_b out_s out_b) st = (op, st') /\
    eval_operand v ss = SOME (i2w i) /\ fresh_vars_wrt st ss /\
    within_int_bound (if in_s then Signed in_b else Unsigned in_b) i /\
    0 < in_b /\ in_b <= 256 /\ 0 < out_b /\ (out_s ==> 1 < out_b) /\ out_b <= 256 ==>
    (within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (i2w i)) /\
    (~within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  cheat
QED

Theorem compile_convert_int_frag:
  !ctx func cenv cx in_s in_b out_s out_b t v1 i es0.
    val_to_w256 v1 = i2w i /\
    within_int_bound (if in_s then Signed in_b else Unsigned in_b) i /\
    0 < in_b /\ in_b <= 256 /\ 0 < out_b /\ (out_s ==> 1 < out_b) /\
    out_b <= 256 /\
    (within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     convert_result cx src t v1 = INL (IntV i)) /\
    (~within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     ?m. convert_result cx src t v1 = INR (Error (RuntimeError m))) ==>
    convert_frag ctx func cenv cx src (ConvIntToInt in_s in_b out_s out_b) t v1 es0
Proof
  cheat
QED

(* ===== Integer to bool ===== *)

Theorem convert_bool_run:
  !x w ss st op st'.
    compile_type_convert x ConvToBool st = (op, st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          eval_operand op ss' = SOME (bool_to_word (w <> 0w))
Proof
  cheat
QED

Theorem compile_convert_bool_frag:
  !ctx func cenv cx t v1 i es0 sg bits.
    val_to_w256 v1 = i2w i /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i /\
    bits <= 256 /\
    convert_result cx src t v1 = INL (BoolV (i <> 0)) ==>
    convert_frag ctx func cenv cx src ConvToBool t v1 es0
Proof
  cheat
QED

(* ===== The case lemma ===== *)

(* An identity conversion preserves the encoded word without emitting code. *)
Theorem compile_convert_identity_frag:
  convert_result cx src t v1 = INL v /\ word_value v /\
  val_to_w256 v1 = val_to_w256 v ==>
  convert_frag ctx func cenv cx src ConvIdentity t v1 es0
Proof
  cheat
QED

(* The conversions covered: between integer types (ConvIntToInt), from bool
   to an integer type (ConvIdentity), and from an integer type to bool
   (ConvToBool). *)
Definition int_convert_pair_def:
  int_convert_pair src dst <=>
    ((?n. src = BaseT (IntT n)) \/ (?n. src = BaseT (UintT n)) \/
     src = BaseT BoolT) /\
    ((?m. dst = BaseT (IntT m)) \/ (?m. dst = BaseT (UintT m))) \/
    ((?n. src = BaseT (IntT n)) \/ (?n. src = BaseT (UintT n))) /\
    dst = BaseT BoolT
End

val int_tac =
  Cases_on `v1` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `IntV i` >>
  irule compile_convert_int_frag >> simp[] >> qexists_tac `i` >>
  simp[val_to_w256_def, convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  simp[within_int_bound_def];

val bool_tac =
  Cases_on `v1` >> gvs[vyperTypingTheory.value_has_type_def] >>
  irule compile_convert_identity_frag >>
  rename1 `BoolV b` >>
  qexists_tac `IntV (if b then 1 else 0)` >>
  Cases_on `b` >>
  simp[val_to_w256_def, convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       word_value_def, integer_wordTheory.i2w_def];

(* sg: whether the source is signed *)
fun tobool_tac sg =
  rename1 `value_has_type (BaseTV (_ n)) v1` >>
  Cases_on `v1` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `IntV i` >>
  irule compile_convert_bool_frag >>
  simp[val_to_w256_def, convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  qexistsl_tac [`n`, `i`, sg] >> simp[within_int_bound_def];

(* convert_frag for a covered pair, on a value of the source type. *)
Theorem convert_frag_word:
  !ctx func cenv cx src t tyv v1 es0.
    int_convert_pair src t /\
    evaluate_type (get_tenv cx) src = SOME tyv /\ value_has_type tyv v1 /\
    IS_SOME (evaluate_type (get_tenv cx) t) ==>
    convert_frag ctx func cenv cx src (mk_convert_op src t) t v1 es0
Proof
  cheat
QED

Theorem straight_fresh_extends:
  !m sa x sb. straight_fresh m /\ m sa = (x, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED

Theorem expr_body_pre_convert:
  !cenv cx env ann t args es.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t args) es ==>
    ?e1. args = [e1] /\ ann = t /\ valid_conversion (expr_type e1) t /\
         expr_body_pre cenv cx env e1 es
Proof
  cheat
QED

Theorem eval_expr_type_builtin_value:
  !cx ann tb t args es tv es'.
    eval_expr cx (TypeBuiltin ann tb t args) es = (INL tv, es') ==>
    ?v. tv = Value v
Proof
  cheat
QED

Theorem compile_convert_stack:
  !cenv ty ann t args sa.
    ?t' op sb. compile_expr cenv ty (TypeBuiltin ann Convert t args) sa =
               (StackValue t' op, sb)
Proof
  cheat
QED

Theorem straight_fresh_convert_pair:
  !src t x. int_convert_pair src t ==>
    straight_fresh (compile_type_convert x (mk_convert_op src t))
Proof
  cheat
QED

(* A covered conversion: compile_convert_frag_sim, with the argument's
   shape from lower_value_word_shape. *)
Theorem compile_convert_word_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    int_convert_pair (expr_type e1) t ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  cheat
QED
