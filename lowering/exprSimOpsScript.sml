(*
 * Expression simulation for the operators (#636, part 2)
 *
 * A binary operator on two word operands lowers to the operands' fragments
 * and then compile_binop (exprBopLowering).  compile_bop_sim builds
 * expr_sim of the whole from expr_sim of the operands and binop_frag, the
 * operator's fragment from the operands' values to the source's
 * evaluate_builtin result.  compile_bop_typed_sim is the same composition
 * for operands held in their typed words (typed_val_to_w256), which
 * covers address and bytesN, whose values are BytesV; binop_frag_words is
 * its fragment.
 *
 * TOP-LEVEL:
 *   binop_frag_words       — the operator's fragment, from given operand
 *                            words
 *   binop_frag             — the fragment for operands of word values
 *   binop_frag_straight    — binop_frag from the run facts of straight-line
 *                            code
 *   compile_bop_typed_sim  — the composition, operands in typed words
 *   compile_bop_sim        — the composition, operands of word values
 *   compile_bitwise_sim    — binop_frag for And, Or and XOr
 *   compile_flag_in_sim    — binop_frag for In and NotIn on flags
 *   compile_shift_sim      — binop_frag for ShL and ShR on 256-bit
 *                            integers by a uint256 amount
 *
 * Not covered: shifts of narrower integers and by negative amounts.  The
 * type system allows both (well_typed_binop ShL/ShR: any integer types),
 * but the lowering emits a bare SHL/SHR/SAR: it neither truncates a left
 * shift to the narrower type, as the source does (int_mod, signed_int_mod),
 * nor fails on a negative amount, as the source does (RuntimeError).
 * Vyper itself rejects shifts of integer types other than int256 and
 * uint256.
 *
 * Helpers: eval_expr_bop_cases, eval_operand_frame, expr_val_rel_word,
 *   expr_val_rel_typed,
 *   local_region_frame, expr_post_bop, bop_result_bitwise, flag_and_zero,
 *   compile_flag_in_correct, bop_result_flag_in, straight_fresh_flag_in,
 *   bop_result_shift
 *)

Theory exprSimOps
Ancestors
  list rich_list finite_map pred_set
  fragExec varsExt exprSim freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib

(* ===== The operator ===== *)

(* The source result of bop on two values, as eval_expr gives it for
   Builtin ann (Bop bop) [e1; e2] once the operands are evaluated to v1
   and v2 in the state es.  tys are the operands' static types,
   [expr_type e1; expr_type e2], which evaluate_builtin takes for membership
   in a static array. *)
Definition bop_result_def:
  bop_result cx ann bop tys v1 v2 (es:evaluation_state) =
    case evaluate_builtin cx es.accounts ann (Bop bop) tys [v1; v2] of
      INL v => INL (Value v)
    | INR e => INR (Error e)
End

(* The operator's fragment, from the operands holding the words w1 and w2
   of their values v1 and v2 in a state related at es0, the source state
   after both operands: on a value it reaches its end with the result, a
   word value, holding it, keeping the variables handed out before it, the
   allocations and the memory, and on an error it exits as expr_exit
   allows.  The words are given because an operand of address or bytesN
   type holds its value in the typed encoding typed_val_to_w256, which for
   a bytes20 differs from val_to_w256 (compile_bop_typed_sim). *)
Definition binop_frag_words_def:
  binop_frag_words ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0 <=>
    !sa sb x y op s0.
      compile_binop bop x y ty bl el sa = (op, sb) /\
      expr_res_ok (bop_result cx ann bop tys v1 v2 es0) /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      (!z. y = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb
        (\s. s = s0 /\ stmt_state_rel func cenv cx es0 s /\
             eval_operand x s = SOME w1 /\ eval_operand y s = SOME w2)
        (\s. ?v. bop_result cx ann bop tys v1 v2 es0 = INL (Value v) /\
                 word_value v /\
                 stmt_state_rel func cenv cx es0 s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory)
        (expr_exit (bop_result cx ann bop tys v1 v2 es0))
End

(* binop_frag_words with the operands held in val_to_w256 of their values,
   as word_values are (compile_bop_sim). *)
Definition binop_frag_def:
  binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0 <=>
    binop_frag_words ctx func cenv cx bop ty ann bl el tys v1 v2
      (val_to_w256 v1) (val_to_w256 v2) es0
End

(* ===== Evaluating a binary operator ===== *)

Theorem eval_expr_bop_cases:
  !cx ann bop e1 e2 es res es'.
    eval_expr cx (Builtin ann (Bop bop) [e1; e2]) es = (res, es') ==>
    (?exc. eval_expr cx e1 es = (INR exc, es') /\ res = INR exc) \/
    (?tv1 es1. eval_expr cx e1 es = (INL tv1, es1) /\ !v. tv1 <> Value v) \/
    ?v1 es1.
      eval_expr cx e1 es = (INL (Value v1), es1) /\
      ((?exc. eval_expr cx e2 es1 = (INR exc, es') /\ res = INR exc) \/
       (?tv2 es2. eval_expr cx e2 es1 = (INL tv2, es2) /\
                  !v. tv2 <> Value v) \/
       ?v2. eval_expr cx e2 es1 = (INL (Value v2), es') /\
            res = bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es')
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e1 es` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `materialise cx tv1 es1` >>
  Cases_on `?v. tv1 = Value v` >> gvs[] >>
  simp[materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e2 es1` >> rename1 `_ = (r2, es2)` >>
  Cases_on `r2` >> simp[] >>
  rename1 `materialise cx tv2 es2` >>
  Cases_on `?v. tv2 = Value v` >> gvs[] >>
  simp[materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, get_accounts_def, lift_sum_def,
       bop_result_def] >>
  rename1 `evaluate_builtin _ _ _ _ _ [v1; v2]` >>
  Cases_on `evaluate_builtin cx es2.accounts ann (Bop bop)
              [expr_type e1; expr_type e2] [v1; v2]` >>
  simp[return_def, raise_def] >> rw[] >> gvs[]
QED

(* A straight-line operator fragment from its run facts: when the source
   result is no type error, either it is a value and the emitted code runs
   to the end with it, or it is a runtime error and the code reverts. *)
Theorem binop_frag_straight:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (!x y. straight_fresh (compile_binop bop x y ty bl el)) /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     (?v. bop_result cx ann bop tys v1 v2 es0 = INL (Value v) /\ word_value v /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (val_to_w256 v)) \/
     (?m. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError m)) /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_def, binop_frag_words_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`,
         `compile_binop bop x y ty bl el`, `sa`, `sb`, `op`, `val_to_w256 v`,
         `\ss. eval_operand x ss = SOME (val_to_w256 v1) /\
               eval_operand y ss = SOME (val_to_w256 v2)`,
         `\a. F`, `expr_exit (bop_result cx ann bop tys v1 v2 es0)`, `s0`]
        mp_tac frag_exec_straight_fresh >>
      (impl_tac
       >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
           >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
                 qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
                 qspecl_then [`y`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
                 asm_simp_tac bool_ss []) >>
           qpat_x_assum `!x y sa sb op ss. _`
             (qspecl_then [`x`, `y`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
           asm_rewrite_tac[])) >>
      disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`,
     `compile_binop bop x y ty bl el`, `sa`, `sb`, `op`,
     `\ss. eval_operand x ss = SOME (val_to_w256 v1) /\
           eval_operand y ss = SOME (val_to_w256 v2)`,
     `\a. a = Revert_abort`, `\s. F`,
     `expr_exit (bop_result cx ann bop tys v1 v2 es0)`, `s0`]
    mp_tac frag_exec_straight_fresh_abort >>
  (impl_tac
   >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
       >>~- ([`expr_exit _ _`], gvs[expr_exit_def])
       >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
             qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
             qspecl_then [`y`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
             asm_simp_tac bool_ss []) >>
       qpat_x_assum `!x y sa sb op ss. _`
         (qspecl_then [`x`, `y`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
       asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  gvs[]
QED

(* An operand that is a literal or a variable handed out before st keeps
   its value across a fragment that keeps those variables. *)
Theorem eval_operand_frame:
  !x st t u w.
    (!z. x = Var z ==> not_fresh_at st z) /\ (!l. x <> Label l) /\
    eval_operand x t = SOME w /\
    (!z w'. not_fresh_at st z /\ lookup_var z t = SOME w' ==>
            lookup_var z u = SOME w') ==>
    eval_operand x u = SOME w
Proof
  Cases >> rw[eval_operand_def] >> metis_tac[]
QED

(* ===== The composition ===== *)

(* A word value related at a word type is the operand's val_to_w256. *)
Theorem expr_val_rel_word:
  !cx t v op s.
    expr_val_rel cx t v op s /\ is_word_type t /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ word_value v ==>
    eval_operand op s = SOME (val_to_w256 v)
Proof
  rw[expr_val_rel_def, optionTheory.IS_SOME_EXISTS] >> first_x_assum drule >>
  simp[typed_val_to_w256_word_value]
QED

(* A value related at a word type is the operand's typed_val_to_w256. *)
Theorem expr_val_rel_typed:
  !cx t tv v op s.
    expr_val_rel cx t v op s /\ is_word_type t /\
    evaluate_type (get_tenv cx) t = SOME tv ==>
    eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  rw[expr_val_rel_def] >> first_x_assum drule >> simp[]
QED

(* A live local's region after an expression evaluated from es, which keeps
   the scopes' names, is one at es before it, whose pointer variable the
   expression's fragment keeps. *)
Theorem local_region_frame:
  !func cenv cx es s0 sa scopes t n b sz.
    stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    local_region cenv scopes t n b sz ==>
    local_region cenv es.scopes s0 n b sz
Proof
  rw[local_region_def] >>
  `lookup_scopes n es.scopes <> NONE` by
    metis_tac[lookup_scopes_none_map_fdom, optionTheory.NOT_SOME_NONE] >>
  Cases_on `lookup_scopes n es.scopes` >> fs[] >>
  rename1 `lookup_scopes n es.scopes = SOME e0` >>
  `?w0. lookup_var p s0 = SOME w0` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w0` by metis_tac[] >> gvs[]
QED

(* The end of an operator's fragment from the ends of its operands'. *)
Theorem expr_post_bop:
  !func cenv cx ann bop e1 e2 es es1 es' sa s1 s2 sb s0 t u ss x y op v1 v2 v.
    expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    stmt_state_rel func cenv cx es' ss /\
    eval_operand op ss = SOME (val_to_w256 v) /\ word_value v /\
    (!z w. not_fresh_at s2 z /\ lookup_var z u = SOME w ==>
           lookup_var z ss = SOME w) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==>
             FLOOKUP ss.vs_allocas aid = SOME b) /\
    ss.vs_memory = u.vs_memory /\
    is_word_type ann /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id ==>
    expr_post func cenv cx (Builtin ann (Bop bop) [e1; e2]) es sa sb s0 es'
      v op ss
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  simp[expr_val_rel_def, expr_val_at_def, vyperASTTheory.expr_type_def,
       typed_val_to_w256_word_value] >>
  conj_tac
  >- ((* the variables handed out before sa *)
      rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      `not_fresh_at s2 z` by
        (irule not_fresh_at_mono >> qexists_tac `s1` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s2 z /\ lookup_var z u = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at s1 x /\ lookup_var x t = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  (* the memory of the allocations before sa: kept by e1, then by e2 *)
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => rewrite_tac [GSYM th]) >>
  qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `n` >>
      irule local_region_frame >>
      conj_tac >- (qexistsl_tac [`cx`, `func`] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[])
  >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `sa.cs_next_id` >> asm_rewrite_tac[]) >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Theorem compile_bop_typed_sim:
  !ctx func cenv cx ty ann bop e1 e2 es tv1 tv2.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!tv es1. eval_expr cx e1 es = (INL tv, es1) ==> ?v. tv = Value v) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!v1 es1. eval_expr cx e1 es = (INL (Value v1), es1) ==>
       (!tv es2. eval_expr cx e2 es1 = (INL tv, es2) ==> ?v. tv = Value v) /\
       expr_sim ctx func cenv cx (expr_type e1) e2 es1 /\
       !v2 es2. eval_expr cx e2 es1 = (INL (Value v2), es2) ==>
         binop_frag_words ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2
           (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2) es2) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  (* only a start state related at es is of interest *)
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`frag_exec ctx sa sb (\s. F) (\s. F) (\r. F)` by
        simp[frag_exec_false_pre] >>
      pop_assum (fn th => irule (MATCH_MP frag_exec_weaken th)) >>
      simp[]) >>
  drule_all lower_value_bop >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e2 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x y sa sb op. compile_binop _ _ _ _ _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `cs_extends s1 sb /\ cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func`
    by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  drule eval_expr_bop_cases >> strip_tac
  >- ((* e1 raises *)
      qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`]
                    mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                               `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s1` >> simp[])
  >- ((* e1 is no value *)
      qpat_x_assum `!tv es1. eval_expr cx e1 es = (INL tv, es1) ==> _` drule >>
      simp[])
  >- ((* e2 raises *)
      qpat_x_assum `!v1 es1. eval_expr cx e1 es = _ ==> _` drule >>
      strip_tac >>
      qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INL (Value v1)`, `es1`,
                               `s0`] mp_tac) >>
      (impl_tac >- simp[expr_res_ok_def]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                               `expr_exit res`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
      asm_rewrite_tac[] >> rpt strip_tac >> fs[expr_post_def] >>
      irule frag_exec_exit_prefix >> qexists_tac `s2` >> asm_rewrite_tac[] >>
      qpat_x_assum `expr_sim _ _ _ _ _ e2 _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`s1`, `s2`, `y`, `INR exc`, `es'`, `t`]
                    mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
      gvs[])
  >- ((* e2 is no value *)
      qpat_x_assum `!v1 es1. eval_expr cx e1 es = _ ==> _` drule >>
      strip_tac >>
      qpat_x_assum `!tv es2. eval_expr cx e2 es1 = (INL tv, es2) ==> _` drule >>
      simp[]) >>
  (* both values *)
  qpat_x_assum `!v1 es1. eval_expr cx e1 es = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `!v2 es2. eval_expr cx e2 es1 = _ ==> _` drule >>
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL (Value v1)`, `es1`, `s0`]
                mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                           `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t` >>
  `stmt_state_rel func cenv cx es1 t /\
   eval_operand x t = SOME (typed_val_to_w256 tv1 v1)` by
    (fs[expr_post_def] >> irule expr_val_rel_typed >> metis_tac[]) >>
  (* the right operand, from t *)
  qpat_x_assum `expr_sim _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `y`, `INL (Value v2)`, `es'`, `t`]
                mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = t`,
                           `expr_exit (bop_result cx ann bop [expr_type e1; expr_type e2]
                                         v1 v2 es')`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u` >>
  `stmt_state_rel func cenv cx es' u /\
   eval_operand y u = SOME (typed_val_to_w256 tv2 v2) /\
   eval_operand x u = SOME (typed_val_to_w256 tv1 v1)` by
    (fs[expr_post_def] >> conj_tac
     >- (irule expr_val_rel_typed >> metis_tac[]) >>
     irule eval_operand_frame >> metis_tac[]) >>
  (* the operator, from u *)
  qpat_x_assum `binop_frag_words _ _ _ _ _ _ _ _ _ tys _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `sb`, `x`, `y`, `op`, `u`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[not_fresh_at_mono])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  irule expr_post_bop >> simp[] >>
  qexistsl_tac [`es1`, `s1`, `s2`, `t`, `u`, `v1`, `v2`, `x`, `y`] >>
  simp[]
QED

(* compile_bop_typed_sim for operands of the types whose values are
   word_values, held in their plain encoding val_to_w256. *)
Theorem compile_bop_sim:
  !ctx func cenv cx ty ann bop e1 e2 es.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
    is_word_type (expr_type e2) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!tv es1. eval_expr cx e1 es = (INL tv, es1) ==> ?v. tv = Value v) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!v1 es1. eval_expr cx e1 es = (INL (Value v1), es1) ==>
       word_value v1 /\
       (!tv es2. eval_expr cx e2 es1 = (INL tv, es2) ==> ?v. tv = Value v) /\
       expr_sim ctx func cenv cx (expr_type e1) e2 es1 /\
       !v2 es2. eval_expr cx e2 es1 = (INL (Value v2), es2) ==>
         word_value v2 /\
         binop_frag ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2 es2) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e1))`
    (qx_choose_then `t1` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e2))`
    (qx_choose_then `t2` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_bop_typed_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t1`, `t2`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!v1 es1. _ ==> word_value v1 /\ _` drule >> strip_tac >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!v2 es2. _ ==> word_value v2 /\ _` drule >> strip_tac >>
  gvs[typed_val_to_w256_word_value, binop_frag_def]
QED

(* ===== Bitwise operators ===== *)

(* proves bop_result_bitwise for one of the operations *)
fun bop_bitwise_tac g =
  (fs[bop_result_def, evaluate_builtin_def] >>
   Cases_on `v1` >> Cases_on `v2` >>
   gvs[evaluate_binop_def, expr_res_ok_def, bounded_int_op_def,
       val_to_w256_def, i2w_int_and, i2w_int_or, i2w_int_xor,
       word_value_def] >>
   FIRST [
     (* flags *)
     qmatch_goalsub_abbrev_tac `n2w (Num z)` >>
     `~(z < 0)` by
       simp[Abbr `z`, int_and_def, int_or_def, int_xor_def, int_bitwise_neg] >>
     `(n2w (Num z) : bytes32) = i2w z` by simp[i2w_def] >>
     pop_assum SUBST1_TAC >>
     simp[Abbr `z`, i2w_int_and, i2w_int_or, i2w_int_xor, i2w_pos],
     (* booleans *)
     rpt (IF_CASES_TAC >> gvs[]) >>
     simp[WORD_AND_CLAUSES, WORD_OR_CLAUSES, WORD_XOR_CLAUSES]]) g;

(* And, Or and XOr on two values give the word operation on their words.
   On integers the source checks the result against the type's bound;
   operands within it keep the result within it, so the check never
   fails. *)
Theorem bop_result_bitwise:
  !cx ann bop v1 v2 es.
    (bop = And \/ bop = Or \/ bop = XOr) /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) ==>
    ?v. bop_result cx ann bop tys v1 v2 es = INL (Value v) /\ word_value v /\
        val_to_w256 v =
          (if bop = And then word_and else if bop = Or then word_or
           else word_xor) (val_to_w256 v1) (val_to_w256 v2)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac
    `u = case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0` >>
  `!i1 i2. within_int_bound u i1 /\ within_int_bound u i2 ==>
     within_int_bound u (int_and i1 i2) /\ within_int_bound u (int_or i1 i2) /\
     within_int_bound u (int_xor i1 i2)` by
    simp[int_and_def, int_or_def, int_xor_def, within_int_bound_int_bitwise] >>
  (* one operation at a time, each unfolding a third of the value pairs *)
  gvs[]
  >>~- ([`bop_result _ _ And tys _ _ _`], bop_bitwise_tac)
  >>~- ([`bop_result _ _ Or tys _ _ _`], bop_bitwise_tac) >>
  bop_bitwise_tac
QED

(* The lowering emits the word operation, one instruction. *)
Theorem compile_bitwise_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (bop = And \/ bop = Or \/ bop = XOr) /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_def, binop_frag_words_def] >> rpt gen_tac >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `v1`, `v2`, `es0`] mp_tac
    bop_result_bitwise >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[compile_binop_def] >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `s0`,
                           `val_to_w256 v`, `\r. F`] mp_tac) >>
  (impl_tac >- simp[step_AND, step_OR, step_XOR, is_terminator_def]) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  simp[] >> metis_tac[]
QED

(* ===== Flag membership ===== *)

Theorem flag_and_zero:
  !n n'. n < 2 ** 256 /\ n' < 2 ** 256 ==>
         (int_and (&n) (&n') = 0 <=> (n2w n && n2w n' : bytes32) = 0w)
Proof
  rpt strip_tac >>
  qspecl_then [`Unsigned 256`, `$/\`, `&n`, `&n'`] mp_tac
    within_int_bound_int_bitwise >>
  fs[within_int_bound_def, GSYM int_and_def] >> strip_tac >>
  qabbrev_tac `z = int_and (&n) (&n')` >>
  `?k. z = &k` by metis_tac[NUM_POSINT_EXISTS] >>
  `(n2w n && n2w n' : bytes32) = n2w k` by
    (rewrite_tac[GSYM i2w_pos, GSYM i2w_int_and] >> fs[Abbr `z`]) >>
  fs[n2w_11, dimword_def]
QED

(* The run of the lowered In or NotIn from a state with the fresh
   variables unbound. *)
Theorem compile_flag_in_correct:
  !bop x y ty bl el st op st' a b ss.
    (bop = In \/ bop = NotIn) /\ compile_binop bop x y ty bl el st = (op, st') /\
    eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          eval_operand op ss' =
            SOME (bool_to_word (if bop = In then word_and a b <> 0w
                                else word_and a b = 0w))
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_binop_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op AND [x; y] st = (and_op, s_and)` >>
  qspecl_then [`x`, `y`, `a`, `b`, `st`, `and_op`, `s_and`, `ss`] mp_tac
    emit_op_AND_correct >>
  simp[] >> disch_then (qx_choose_then `s1` strip_assume_tac)
  >- ((* In: AND, ISZERO, ISZERO *)
      rename1 `emit_op ISZERO [and_op] s_and = (z, s_z)` >>
      qspecl_then [`and_op`, `a && b`, `s_and`, `z`, `s_z`, `s1`] mp_tac
        emit_op_ISZERO_correct >>
      simp[] >> disch_then (qx_choose_then `s2` strip_assume_tac) >>
      qspecl_then [`z`, `bool_to_word (a && b = 0w)`, `s_z`, `op`, `st'`,
                   `s2`] mp_tac emit_op_ISZERO_correct >>
      simp[] >> disch_then (qx_choose_then `s3` strip_assume_tac) >>
      imp_res_tac emit_op_extends >>
      `run_inst_seq (emitted_insts st s_z) ss = OK s2 /\
       s_z.cs_current_insts = st.cs_current_insts ++ emitted_insts st s_z` by
        (qspecl_then [`st`, `s_and`, `s_z`, `ss`, `s1`] mp_tac
           run_inst_seq_chain >> simp[]) >>
      qspecl_then [`st`, `s_z`, `st'`, `ss`, `s2`] mp_tac
        run_inst_seq_chain >> simp[] >>
      strip_tac >> qexists_tac `s3` >> simp[]) >>
  (* NotIn: AND, ISZERO *)
  qspecl_then [`and_op`, `a && b`, `s_and`, `op`, `st'`, `s1`] mp_tac
    emit_op_ISZERO_correct >>
  simp[] >> disch_then (qx_choose_then `s2` strip_assume_tac) >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`st`, `s_and`, `st'`, `ss`, `s1`] mp_tac run_inst_seq_chain >>
  simp[] >> strip_tac >> qexists_tac `s2` >> simp[]
QED

(* In and NotIn on two flags of a type with at most 256 members test the
   words' common bits. *)
Theorem bop_result_flag_in:
  !cx ann bop m v1 v2 es.
    (bop = In \/ bop = NotIn) /\
    value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\
    m <= 256 ==>
    bop_result cx ann bop tys v1 v2 es =
      INL (Value (BoolV
        (if bop = In then word_and (val_to_w256 v1) (val_to_w256 v2) <> 0w
         else word_and (val_to_w256 v1) (val_to_w256 v2) = 0w)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  Cases_on `v2` >> gvs[value_has_type_def] >>
  rename1 `bop_result _ _ _ tys (FlagV k1) (FlagV k2) _` >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      binop_negate_def, val_to_w256_def] >>
  `k1 < 2 ** 256 /\ k2 < 2 ** 256` by
    (`2 ** m <= 2 ** 256` by simp[] >> conj_tac >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m` >>
     asm_rewrite_tac[]) >>
  simp[flag_and_zero]
QED

Theorem straight_fresh_flag_in:
  !x y ty bl el.
    straight_fresh (compile_binop In x y ty bl el) /\
    straight_fresh (compile_binop NotIn x y ty bl el)
Proof
  rw[compile_binop_def] >>
  rpt (FIRST [irule straight_fresh_bind >> rw[],
              irule straight_fresh_emit_op >> simp[fresh_write_op_def]])
QED

(* binop_frag for In and NotIn on two flags of a tys type with at most 256
   members. *)
Theorem compile_flag_in_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 m.
    (bop = In \/ bop = NotIn) /\
    value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\
    m <= 256 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qspecl_then [`cx`, `ann`, `bop`, `m`, `v1`, `v2`, `es0`] mp_tac
    bop_result_flag_in >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> metis_tac[straight_fresh_flag_in]) >>
  strip_tac >> disj1_tac >> simp[word_value_def] >> rpt strip_tac >>
  qspecl_then [`bop`, `x`, `y`, `ty`, `bl`, `el`, `sa`, `op`, `sb`,
               `val_to_w256 v1`, `val_to_w256 v2`, `ss`] mp_tac
    compile_flag_in_correct >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >>
  Cases_on `if bop = In then val_to_w256 v1 && val_to_w256 v2 <> 0w
            else val_to_w256 v1 && val_to_w256 v2 = 0w` >>
  simp[val_to_w256_def, bool_to_word_def]
QED

(* ===== Shifts ===== *)

(* ShL and ShR of a 256-bit integer by a uint256 amount give the word
   shift: left, arithmetic right when signed, logical right when not. *)
Theorem bop_result_shift:
  !cx ann bop ty v1 v2 es i1 i2.
    (bop = ShL \/ bop = ShR) /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256)
      i1 ==>
    ?v. bop_result cx ann bop tys v1 v2 es = INL (Value v) /\ word_value v /\
        val_to_w256 v =
          if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
          else if is_signed_type ty
          then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
          else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~(i2 < 0) /\ w2n (i2w i2 : bytes32) = Num i2` by
    (fs[within_int_bound_def] >>
     `?k. i2 = &k` by metis_tac[NUM_POSINT_EXISTS] >>
     gvs[i2w_pos, w2n_n2w, dimword_def]) >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      val_to_w256_def, word_value_def] >>
  Cases_on `is_signed_type ty` >> gvs[] >>
  FIRST [
    (* ShL, signed: wrapped by signed_int_mod *)
    simp[val_to_w256_def] >>
    qmatch_goalsub_abbrev_tac `signed_int_mod 256 rr` >>
    `signed_int_mod 256 rr = w2i (i2w rr : bytes32)` by
      (qspec_then `rr` mp_tac
         (INST_TYPE [alpha |-> ``:256``] signed_int_mod_w2i) >> simp[]) >>
    simp[i2w_w2i, Abbr `rr`, i2w_int_shift_left] >> NO_TAC,
    (* ShL, unsigned: wrapped by int_mod *)
    simp[val_to_w256_def] >>
    qmatch_goalsub_abbrev_tac `i2w (rr % _)` >>
    `rr % &dimword (:256) = &w2n (i2w rr : bytes32)` by simp[w2n_i2w] >>
    fs[dimword_def, i2w_w2n, Abbr `rr`, i2w_int_shift_left] >> NO_TAC,
    irule i2w_int_shift_right_signed >> simp[] >> NO_TAC,
    irule i2w_int_shift_right_unsigned >> simp[]]
QED

(* binop_frag for ShL and ShR of a 256-bit integer by a uint256 amount:
   one instruction. *)
Theorem compile_shift_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2.
    (bop = ShL \/ bop = ShR) /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256)
      i1 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_def, binop_frag_words_def] >> rpt gen_tac >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `v1`, `v2`, `es0`, `i1`, `i2`]
    mp_tac bop_result_shift >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[compile_binop_def] >>
  qpat_x_assum `_ sa = (op, sb)` mp_tac >> rw[] >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `s0`,
                           `val_to_w256 v`, `\r. F`] mp_tac) >>
  (impl_tac >- simp[step_SHL, step_SHR, step_SAR, is_terminator_def]) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  simp[] >> metis_tac[]
QED
