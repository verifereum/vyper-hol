(*
 * Expression simulation for one-operand builtins (#636, Operators row 7)
 *
 * A builtin applied to one word operand lowers to the operand's fragment
 * and then code of its own on the operand's word.  compile_unop_sim builds
 * expr_sim of the whole from expr_sim of the operand and unop_frag, the
 * builtin's fragment from the operand's word to the source's
 * evaluate_builtin result: compile_bop_sim (exprSimOps) for one operand,
 * or exprSimConvert's compile_convert_frag_sim for a Builtin.  The
 * operand's word is its typed encoding (typed_val_to_w256), so bytesN
 * operands are covered too.
 *
 * TOP-LEVEL:
 *   unop_result, unop_frag   — the source result and the fragment
 *   compile_unop_sim         — the composition
 *   unop_frag_straight       — unop_frag from the run facts of
 *                              straight-line code
 *   compile_expr_not_abs, lower_value_not, lower_value_abs,
 *   compile_not_abs_stack
 *                            — how not and abs lower
 *   compile_not_frag         — unop_frag for not on bool (ISZERO),
 *                              uint256 and bytes32 (NOT) and flags (XOR
 *                              with the members' mask)
 *   compile_abs_frag         — unop_frag for abs on int256
 *
 * Helpers: eval_expr_unop_cases, expr_post_unop, compile_expr_body_not_abs,
 *   straight_fresh_cs_extends, straight_fresh_not, straight_fresh_abs,
 *   not_type_cases, flag_not_xor, abs_i2w, int256_abs_bound,
 *   word_of_bytes_be_to_bytes, length_word_to_bytes_be
 *)

Theory exprSimUnop
Ancestors
  arithmetic list integer words integer_word byte
  fragExec varsExt exprSim freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps
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
Definition unop_frag_def:
  unop_frag ctx func cenv cx f w1 t res es0 <=>
    !sa sb x op s0.
      f x sa = (op, sb) /\ expr_res_ok res /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb
        (\s. s = s0 /\ stmt_state_rel func cenv cx es0 s /\
             eval_operand x s = SOME w1)
        (\s. ?v. res = INL v /\
                 stmt_state_rel func cenv cx es0 s /\
                 expr_val_rel cx t v op s /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory)
        (expr_exit res)
End

(* ===== Evaluating a one-operand builtin ===== *)

Theorem eval_expr_unop_cases:
  !cx ann bi e1 es res es'.
    (do r <- eval_expr cx (Builtin ann bi [e1]); read_result cx r od) es = (res, es') /\ bi <> Len /\
    builtin_args_length_ok bi 1 ==>
    (?exc. (do r <- eval_expr cx e1; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
    ?v1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1, es') /\
         res = unop_result cx ann bi [expr_type e1] v1 es'
Proof
  rpt gen_tac >> strip_tac >>
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

(* ===== The composition ===== *)

Theorem expr_post_unop:
  !func cenv cx ann bi e1 es es' sa s1 sb s0 t0 ss x op v1 v.
    expr_post func cenv cx e1 es sa s1 s0 es' v1 x t0 /\
    stmt_state_rel func cenv cx es' ss /\
    expr_val_rel cx ann v op ss /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
           lookup_var z ss = SOME w) /\
    (!aid b. FLOOKUP t0.vs_allocas aid = SOME b ==>
             FLOOKUP ss.vs_allocas aid = SOME b) /\
    ss.vs_memory = t0.vs_memory /\
    is_word_type ann /\ sa.cs_next_var <= s1.cs_next_var ==>
    expr_post func cenv cx (Builtin ann bi [e1]) es sa sb s0 es' v op ss
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  `locals_kept cenv es s0 ss` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
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
Theorem compile_unop_sim:
  !ctx func cenv cx ty ann bi e1 ty1 f es.
    bi <> Len /\ builtin_args_length_ok bi 1 /\
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (Builtin ann bi [e1]) sa = (op, sb) ==>
       ?x s1. lower_value compile_expr cenv ty1 e1 sa = (x, s1) /\
              f x s1 = (op, sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv ty1 e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx ty1 e1 es /\
    (!v1 es1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1, es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
             unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
               (unop_result cx ann bi [expr_type e1] v1 es1) es1) ==>
    expr_sim ctx func cenv cx ty (Builtin ann bi [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`frag_exec ctx sa sb (\s. F) (\s. F) (\r. F)` by
        simp[frag_exec_false_pre] >>
      pop_assum (fn th => irule (MATCH_MP frag_exec_weaken th)) >>
      simp[]) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty (Builtin _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty1 e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `builtin_args_length_ok bi 1 /\ bi <> Len` by asm_rewrite_tac[] >>
  drule_all eval_expr_unop_cases >> strip_tac
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
  >>
  qpat_x_assum `!v1 es1. bind _ _ es = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`]
                mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                           `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post func cenv cx e1 es sa s1 s0 es' v1 x t0` >>
  `stmt_state_rel func cenv cx es' t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_def]) >>
  disch_then (qspecl_then [`s1`, `sb`, `x`, `op`, `t0`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[not_fresh_at_mono])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  irule expr_post_unop >> simp[] >>
  qexistsl_tac [`s1`, `t0`, `v1`, `x`] >> simp[]
QED

(* unop_frag from the run facts of the builtin's straight-line code. *)
Theorem unop_frag_straight:
  !ctx func cenv cx f w1 t res es0.
    (!x. straight_fresh (f x)) /\ is_word_type t /\
    (expr_res_ok res ==>
     (?v w. res = INL v /\
            (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
                  w = typed_val_to_w256 tv v) /\
            !x sa sb op ss.
              f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
              eval_operand x ss = SOME w1 ==>
              ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                    eval_operand op ss' = SOME w) \/
     (?m. res = INR (Error (RuntimeError m)) /\
          !x sa sb op ss.
            f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME w1 ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    unop_frag ctx func cenv cx f w1 t res es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `f x`, `sa`, `sb`,
         `op`, `w`, `\ss. eval_operand x ss = SOME w1`,
         `\a. F`, `expr_exit res`, `s0`]
        mp_tac frag_exec_straight_fresh >>
      (impl_tac
       >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
           >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
                 qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
                 asm_simp_tac bool_ss []) >>
           qpat_x_assum `!x sa sb op ss. _`
             (qspecl_then [`x`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
           asm_rewrite_tac[])) >>
      disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
      simp[] >> rpt strip_tac >> gvs[expr_val_rel_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `f x`, `sa`, `sb`, `op`,
     `\ss. eval_operand x ss = SOME w1`,
     `\a. a = Revert_abort`, `\s. F`, `expr_exit res`, `s0`]
    mp_tac frag_exec_straight_fresh_abort >>
  (impl_tac
   >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
       >>~- ([`expr_exit _ _`], gvs[expr_exit_def])
       >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
             qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
             asm_simp_tac bool_ss []) >>
       qpat_x_assum `!x sa sb op ss. _`
         (qspecl_then [`x`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
       asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  gvs[]
QED

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
Theorem compile_not_frag:
  !ctx func cenv cx ann tys v1 es0 tv1.
    (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
     is_flag_type ann) /\
    evaluate_type (get_tenv cx) ann = SOME tv1 /\ value_has_type tv1 v1 /\
    (!nsid m. ann = FlagT nsid /\ tv1 = FlagTV m ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    unop_frag ctx func cenv cx
      (\x. if ann = BaseT BoolT then emit_op ISZERO [x]
           else compile_invert x ann cenv)
      (typed_val_to_w256 tv1 v1) ann (unop_result cx ann Not tys v1 es0) es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
                              strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule unop_frag_straight >>
  (conj_tac
   >- (gen_tac >> simp[compile_invert_def, LET_THM] >>
       irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
  (conj_tac >- simp[is_word_type_def]) >>
  disch_then kall_tac >> disj1_tac >>
  Cases_on `v1` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def, vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (rpt strip_tac >> drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
      qexists_tac `ss'` >> asm_rewrite_tac[] >> BasicProvers.every_case_tac >>
      gvs[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> rpt strip_tac >>
      drule_all emit_op_NOT_correct >> rw[] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >> rpt strip_tac >> gvs[listTheory.PAD_RIGHT] >>
      drule_all emit_op_NOT_correct >> rw[] >>
      simp[listTheory.PAD_RIGHT, length_word_to_bytes_be,
           word_of_bytes_be_to_bytes]) >>
  rename1 `k < 2 ** m` >> rpt strip_tac >>
  qspecl_then [`XOR`, `word_xor`, `x`, `Lit (n2w (2 ** m - 1))`, `n2w k`,
               `n2w (2 ** m - 1)`, `sa`, `op`, `sb`, `ss`]
    mp_tac emit_op_pure2_correct >>
  impl_tac
  >- (simp[eval_operand_def] >> irule step_XOR >> simp[eval_operand_def]) >>
  rw[] >> simp[flag_not_xor]
QED

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

Theorem compile_abs_frag:
  !ctx func cenv cx tys v1 es0.
    value_has_type (BaseTV (IntT 256)) v1 ==>
    unop_frag ctx func cenv cx compile_builtin_abs
      (typed_val_to_w256 (BaseTV (IntT 256)) v1) (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Abs tys v1 es0) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  rpt conj_tac
  >- simp[straight_fresh_abs]
  >- simp[is_word_type_def] >>
  disch_then kall_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, bounded_int_op_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)`
  >- (`i2w i = (INT_MINw : bytes32)` by metis_tac[] >>
      qpat_x_assum `i = _`
        (fn th => REWRITE_TAC [EQT_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
      disj2_tac >> simp[] >>
      rpt strip_tac >> drule_all compile_builtin_abs_run >> simp[]) >>
  `i2w i <> (INT_MINw : bytes32)` by metis_tac[] >>
  qpat_x_assum `i <> _`
    (fn th => REWRITE_TAC [EQF_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
  disj1_tac >>
  simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  rpt strip_tac >> drule_all compile_builtin_abs_run >>
  disch_then (drule o CONJUNCT1) >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >> simp[]
QED
