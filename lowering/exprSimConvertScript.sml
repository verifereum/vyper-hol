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
  Cases >> simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, is_bytestring_type_def]
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
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  Cases_on `t` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
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
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e1 es` >> rename1 `_ = (raw1, st1)` >>
  reverse (Cases_on `raw1`)
  >- (simp[] >> rw[] >> simp[]) >>
  rename1 `eval_expr cx e1 es = (INL r1, st1)` >>
  Cases_on `read_result cx r1 st1` >> rename1 `_ = (res1, es1)` >>
  reverse (Cases_on `res1`)
  >- (simp[] >> rw[] >> simp[]) >>
  rename1 `read_result cx r1 st1 = (INL v1, es1)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e1) v1 t` >>
  simp[read_result_def, return_def, raise_def] >> rw[] >> gvs[]
QED

Theorem eval_expr_convert_of_child:
  !cx ann ty e es v ee.
    bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
    bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx) es =
      (convert_result cx (expr_type e) ty v, ee)
Proof
  rpt strip_tac >>
  Cases_on `bind (eval_expr cx (TypeBuiltin ann Convert ty [e]))
                 (read_result cx) es` >>
  drule (SRULE [SF ETA_ss] eval_expr_convert_cases) >>
  strip_tac >> gvs[]
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
  rpt gen_tac >> strip_tac >>
  simp[unop_frag_def, typed_val_to_w256_word_value] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `convert_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [convert_frag_def]) >>
  disch_then (qspecl_then [`sa`,`sb`,`x`,`op`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `r` >> gvs[] >>
  simp[expr_val_rel_def, typed_val_to_w256_word_value]
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
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  `~expr_has_effect (TypeBuiltin ann Convert t [e1]) ==>
   pure_frame cenv func es sa s0 ss` by
    (simp[loweringPostsTheory.expr_has_effect_thm] >> strip_tac >>
     match_mp_tac exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `t0` >>
     simp[]) >>
  `locals_kept cenv es es' s0 ss` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  simp[expr_val_at_def, expr_type_def] >>
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

(* The source action of a conversion: the argument's, then
   convert_result, which reads no state. *)
Theorem eval_expr_convert_action:
  bind (eval_expr cx (TypeBuiltin ann Convert t [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. (convert_result cx (expr_type e) t v, es))
Proof
  pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
              (read_result cx) x` >>
  drule (SRULE [SF ETA_ss] eval_expr_convert_cases) >>
  strip_tac >> gvs[bind_def]
QED

Theorem convert_operand_admissible:
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[eval_expr_convert_action] >>
  rw[gas_admissible_def] >>
  Cases_on `res`
  >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem convert_exempt_cert:
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx (TypeBuiltin ann Convert t [e]))
                    (read_result cx)) (return ())) start marks out endpoint
Proof
  strip_tac >> rewrite_tac[eval_expr_convert_action] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v es. (convert_result cx (expr_type e) t v,es))) (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (\es. (convert_result cx (expr_type e) t v,es))
       (return ()))` by
    (qmatch_goalsub_abbrev_tac `bind a _` >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[] >>
     Cases_on `convert_result cx (expr_type e) t a'` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >> simp[]
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
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_def]) >>
  disch_then (qspecl_then [`s1`,`sb`,`x`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
      conj_tac
      >- (simp[gas_marked_exec_def] >> metis_tac[]) >>
      gvs[] >> irule expr_post_convert >> simp[] >>
      qexistsl_tac [`s1`,`t0`,`v1`,`x`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) t v1`,`ee`,`r`] >>
  simp[gas_marked_exec_def]
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
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty (TypeBuiltin _ _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ (expr_type e1) e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "counted" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

Resume compile_convert_frag_sim[counted]:
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- (gvs[] >>
      `bind (eval_expr cx e1) (read_result cx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         (INL v, es_end with gas_obs := [])` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
           (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
         strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      qpat_x_assum `!gs1 v1 es1. _`
        (drule o CONV_RULE (DEPTH_CONV ETA_CONV)) >> strip_tac >>
      `~t'.vs_halted` by
        metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      `expr_res_ok (convert_result cx (expr_type e1) t v)` by
        (qpat_x_assum
           `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
           (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
         disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
         rewrite_tac[eval_expr_convert_action] >>
         simp[bind_def] >> disch_then irule >> simp[]) >>
      drule_all convert_continuation_summary >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`,`es_end'`,`r`] >>
      (conj_tac
       >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                  |> REWRITE_RULE [APPEND_NIL]) >>
           qexistsl_tac [`es_end`,`t'`,`v`] >> gvs[]) >>
       gvs[])) >>
  Cases_on `res` >- gvs[] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
  simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  gvs[]
QED

Finalise compile_convert_frag_sim

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
  rpt gen_tac >> strip_tac >>
  irule compile_convert_frag_sim >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  qexists_tac `\x. compile_type_convert x (mk_convert_op (expr_type e1) t)` >>
  simp[] >> rpt conj_tac
  >~ [`lower_value _ _ ty _ _ = _`]
  >- (rpt gen_tac >> strip_tac >>
      `~is_bytestring_type (expr_type e1)` by
        metis_tac[is_word_type_not_bytestring] >>
      drule_all lower_value_convert >>
      strip_tac >> qexistsl_tac [`x`, `s1`] >>
      Cases_on `t` >> gvs[])
  >~ [`unop_frag _ _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      Cases_on `evaluate_type (get_tenv cx) (expr_type e1)` >> gvs[] >>
      irule convert_frag_unop >> simp[]) >>
  metis_tac[]
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
  rw[compile_type_convert_def, compile_int_clamp_def] >> rpt sf_step
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
  rpt gen_tac >> strip_tac >> simp[convert_frag_def] >> rpt gen_tac >>
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v1)` by
    metis_tac[eval_operand_drop_fresh] >>
  qpat_x_assum `!x. straight_fresh (compile_type_convert x conv)`
    (qspec_then `x` assume_tac) >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qpat_x_assum `!x sa sb op ss. _`
        (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
      simp[] >> strip_tac >>
      drule_all straight_fresh_clean_success_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      drule_all straight_fresh_run_post >> strip_tac >>
      qmatch_asmsub_rename_tac `vars_ext ss' target` >>
      qexists_tac `OK (target with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `!x sa sb op ss. _`
    (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_rename_tac
    `gas_marked_path F ctx func s0 0 (Abort Revert_abort endpoint)` >>
  qexists_tac `Abort Revert_abort endpoint` >>
  simp[exit_result_def, expr_exit_def]
QED

(* ===== Integer to integer ===== *)

Theorem within_int_bound_ineq:
  !b i.
    (within_int_bound (Unsigned b) i <=> 0 <= i /\ i < &(2 ** b)) /\
    (0 < b ==>
     (within_int_bound (Signed b) i <=>
      -&(2 ** (b - 1)) <= i /\ i < &(2 ** (b - 1))))
Proof
  rpt gen_tac >> conj_tac >> TRY strip_tac >>
  simp[within_int_bound_def] >>
  (Cases_on `i < 0`
   >- (`?n. i = -&n` by (irule NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
       gvs[] >> intLib.ARITH_TAC) >>
   `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
   gvs[] >> intLib.ARITH_TAC)
QED

(* A narrowing between two integer types of one signedness is the target's
   clamp. *)
Theorem convert_int_clamp:
  !v s in_b out_b.
    out_b < in_b ==>
    compile_type_convert v (ConvIntToInt s in_b s out_b) =
    clamp_and_return v (BaseT (if s then IntT out_b else UintT out_b))
Proof
  gen_tac >> Cases >>
  rw[FUN_EQ_THM, compile_type_convert_def, compile_int_clamp_def,
     clamp_and_return_def,
     compile_clamp_def, type_bounds_def, is_signed_type_def, type_bits_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* An unsigned source and a signed target of b bits: the clamp of an
   unsigned integer of b - 1 bits. *)
Theorem convert_u2s_clamp:
  !v in_b out_b.
    compile_type_convert v (ConvIntToInt F in_b T out_b) =
    clamp_and_return v (BaseT (UintT (out_b - 1)))
Proof
  rw[FUN_EQ_THM, compile_type_convert_def, clamp_and_return_def,
     compile_clamp_def, type_bounds_def, is_signed_type_def, type_bits_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
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
  rpt gen_tac >> strip_tac >> Cases_on `in_s` >> Cases_on `out_s` >> gvs[]
  >- ((* signed to signed *)
      Cases_on `out_b < in_b`
      >- (qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
          simp[convert_int_clamp] >> strip_tac >>
          `math_val (BaseT (IntT out_b)) (i2w i : bytes32) = i` by
            (simp[math_val_def, is_signed_type_def] >>
             irule w2i_i2w_within_signed >> metis_tac[]) >>
          `in_type_range (BaseT (IntT out_b)) i <=>
           within_int_bound (Signed out_b) i` by
            simp[in_type_range_within, is_signed_type_def, type_bits_def] >>
          conj_tac >> strip_tac
          >- (qspecl_then [`v`, `BaseT (IntT out_b)`, `st`, `op`, `st'`, `st`,
                           `ss`, `ss`, `i2w i`] mp_tac clamp_and_return_ok >>
              simp[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
          qspecl_then [`v`, `BaseT (IntT out_b)`, `st`, `op`, `st'`, `st`,
                       `ss`, `ss`, `i2w i`] mp_tac
            clamp_and_return_out_of_range >>
          simp[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
      gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
          run_inst_seq_nil] >>
      gvs[within_int_bound_ineq] >>
      `2 ** (in_b - 1) <= 2 ** (out_b - 1)` by simp[] >>
      intLib.ARITH_TAC)
  >- ((* signed to unsigned *)
      `w2i (i2w i : bytes32) = i` by
        (irule w2i_i2w_within_signed >> metis_tac[]) >>
      `((i2w i : bytes32) < 0w <=> i < 0)` by
        asm_simp_tac (srw_ss()) [integer_wordTheory.WORD_LTi,
                              integer_wordTheory.word_0_w2i] >>
      `2 ** out_b - 1 < dimword (:256)` by
        (simp[dimword_def] >>
         `2 ** out_b <= 2 ** 256` by simp[] >> decide_tac) >>
      `0 < 2 ** (in_b - 1) /\ 0 < 2 ** out_b` by simp[] >>
      conj_tac >> strip_tac
      >- (qspecl_then [`v`, `in_b`, `out_b`, `i2w i`, `ss`, `st`, `op`, `st'`]
            mp_tac convert_s2u_ok >>
          impl_tac
          >- (gvs[within_int_bound_ineq] >> conj_tac >- intLib.ARITH_TAC >>
              strip_tac >>
              `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
              gvs[integer_wordTheory.i2w_pos, w2n_n2w]) >>
          strip_tac >> gvs[] >> metis_tac[]) >>
      qspecl_then [`v`, `in_b`, `out_b`, `i2w i`, `ss`, `st`, `op`, `st'`]
        mp_tac convert_s2u_abort >>
      impl_tac
      >- (gvs[within_int_bound_ineq] >>
          Cases_on `i < 0` >> simp[] >>
          `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
          gvs[integer_wordTheory.i2w_pos, w2n_n2w] >>
          `2 ** (in_b - 1) <= 2 ** 255` by simp[] >>
          `2 ** 255 <= dimword (:256)` by simp[dimword_def] >>
          `n < dimword (:256)` by decide_tac >>
          asm_simp_tac (srw_ss()) [arithmeticTheory.LESS_MOD] >>
          CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS]
          >- (`2 ** (in_b - 1) <= 2 ** out_b` by simp[] >> decide_tac) >>
          `0 < 2 ** out_b` by simp[] >> decide_tac) >>
      simp[])
  >- ((* unsigned to signed *)
      qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
      simp[convert_u2s_clamp] >> strip_tac >>
      `?n. i = &n /\ n < 2 ** in_b` by
        (gvs[within_int_bound_ineq] >>
         `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
         gvs[]) >>
      `n < dimword (:256)` by
        (simp[dimword_def] >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
         qexists_tac `2 ** in_b` >> simp[]) >>
      `math_val (BaseT (UintT (out_b - 1))) (i2w i : bytes32) = i` by
        gvs[math_val_def, is_signed_type_def, integer_wordTheory.i2w_pos] >>
      `in_type_range (BaseT (UintT (out_b - 1))) i <=>
       within_int_bound (Signed out_b) i` by
        (gvs[in_type_range_def, is_signed_type_def, type_bits_def,
             within_int_bound_ineq] >> intLib.ARITH_TAC) >>
      conj_tac >> strip_tac
      >- (qspecl_then [`v`, `BaseT (UintT (out_b - 1))`, `st`, `op`, `st'`,
                       `st`, `ss`, `ss`, `i2w i`] mp_tac clamp_and_return_ok >>
          gvs[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
      qspecl_then [`v`, `BaseT (UintT (out_b - 1))`, `st`, `op`, `st'`, `st`,
                   `ss`, `ss`, `i2w i`] mp_tac clamp_and_return_out_of_range >>
      gvs[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
  (* unsigned to unsigned *)
  `?n. i = &n /\ n < 2 ** in_b` by
    (gvs[within_int_bound_ineq] >>
     `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
     gvs[]) >>
  Cases_on `out_b < in_b`
  >- (qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
      simp[convert_int_clamp] >> strip_tac >>
      `n < dimword (:256)` by
        (simp[dimword_def] >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
         qexists_tac `2 ** in_b` >> simp[]) >>
      `math_val (BaseT (UintT out_b)) (i2w i : bytes32) = i` by
        gvs[math_val_def, is_signed_type_def, integer_wordTheory.i2w_pos] >>
      `in_type_range (BaseT (UintT out_b)) i <=>
       within_int_bound (Unsigned out_b) i` by
        gvs[in_type_range_def, is_signed_type_def, type_bits_def,
            within_int_bound_ineq] >>
      conj_tac >> strip_tac
      >- (qspecl_then [`v`, `BaseT (UintT out_b)`, `st`, `op`, `st'`, `st`,
                       `ss`, `ss`, `i2w i`] mp_tac clamp_and_return_ok >>
          gvs[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
      qspecl_then [`v`, `BaseT (UintT out_b)`, `st`, `op`, `st'`, `st`,
                   `ss`, `ss`, `i2w i`] mp_tac clamp_and_return_out_of_range >>
      gvs[run_inst_seq_nil, type_bits_def, emitted_insts_refl]) >>
  gvs[compile_type_convert_def, comp_return_def, run_inst_seq_nil,
      emitted_insts_refl, within_int_bound_ineq] >>
  `2 ** in_b <= 2 ** out_b` by simp[] >> decide_tac
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
  rpt gen_tac >> strip_tac >> irule convert_frag_straight >>
  simp[straight_fresh_convert] >> strip_tac >>
  Cases_on `within_int_bound (if out_s then Signed out_b else Unsigned out_b) i`
  >- (disj1_tac >> gvs[word_value_def, val_to_w256_def] >> rpt strip_tac >>
      qspecl_then [`x`, `in_s`, `in_b`, `out_s`, `out_b`, `i`, `ss`, `sa`,
                   `op`, `sb`] mp_tac convert_int_run >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[])) >>
      strip_tac >> res_tac >> metis_tac[]) >>
  disj2_tac >> fs[] >> rpt strip_tac >>
  qspecl_then [`x`, `in_s`, `in_b`, `out_s`, `out_b`, `i`, `ss`, `sa`, `op`, `sb`]
    mp_tac convert_int_run >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[])) >>
    strip_tac >> res_tac >> metis_tac[]
QED

(* ===== Integer to bool ===== *)

Theorem convert_bool_run:
  !x w ss st op st'.
    compile_type_convert x ConvToBool st = (op, st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          eval_operand op ss' = SOME (bool_to_word (w <> 0w))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ISZERO [x] st = (z, cs1)` >>
  qspecl_then [`x`, `w`, `st`, `z`, `cs1`, `ss`] mp_tac emit_op_ISZERO_correct >>
  asm_rewrite_tac[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  qspecl_then [`z`, `bool_to_word (w = 0w)`, `cs1`, `op`, `st'`, `ss1`] mp_tac
    emit_op_ISZERO_correct >>
  asm_rewrite_tac[] >> strip_tac >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`st`, `cs1`, `st'`, `ss`, `ss1`] mp_tac run_inst_seq_chain >>
  asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >>
  qexists_tac `ss'` >> gvs[] >> Cases_on `w = 0w` >> simp[]
QED

Theorem compile_convert_bool_frag:
  !ctx func cenv cx t v1 i es0 sg bits.
    val_to_w256 v1 = i2w i /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i /\
    bits <= 256 /\
    convert_result cx src t v1 = INL (BoolV (i <> 0)) ==>
    convert_frag ctx func cenv cx src ConvToBool t v1 es0
Proof
  rpt gen_tac >> strip_tac >> irule convert_frag_straight >>
  simp[straight_fresh_convert, word_value_def] >> rpt strip_tac >>
  qspecl_then [`x`, `i2w i`, `ss`, `sa`, `op`, `sb`] mp_tac convert_bool_run >>
  asm_rewrite_tac[] >> strip_tac >> qexists_tac `ss'` >> asm_rewrite_tac[] >>
  simp[val_to_w256_def] >>
  qspecl_then [`bits`, `sg`, `i`] mp_tac i2w_eq_0_within >>
  asm_rewrite_tac[] >> strip_tac >> Cases_on `i = 0` >>
  gvs[bool_to_word_def, integer_wordTheory.i2w_def]
QED

(* ===== The case lemma ===== *)

(* An identity conversion preserves the encoded word without emitting code. *)
Theorem compile_convert_identity_frag:
  convert_result cx src t v1 = INL v /\ word_value v /\
  val_to_w256 v1 = val_to_w256 v ==>
  convert_frag ctx func cenv cx src ConvIdentity t v1 es0
Proof
  rpt strip_tac >> irule convert_frag_straight >>
  simp[compile_type_convert_def, straight_fresh_return, comp_return_def,
       emitted_insts_refl, run_inst_seq_nil]
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
  rpt gen_tac >> simp[int_convert_pair_def] >> strip_tac >>
  gvs[evaluate_type_def, vyperTypingTheory.value_has_type_def,
      mk_convert_op_def, is_bytestring_type_def, AllCaseEqs()]
  >~ [`ConvToBool`, `BaseTV (UintT _)`] >- tobool_tac `F`
  >~ [`ConvToBool`] >- tobool_tac `T`
  >~ [`BaseTV BoolT`] >- bool_tac
  >~ [`BaseTV BoolT`] >- bool_tac >>
  int_tac
QED

Theorem straight_fresh_extends:
  !m sa x sb. straight_fresh m /\ m sa = (x, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >> fs[straight_fresh_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem expr_body_pre_convert:
  !cenv cx env ann t args es.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t args) es ==>
    ?e1. args = [e1] /\ ann = t /\ valid_conversion (expr_type e1) t /\
         expr_body_pre cenv cx env e1 es
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     byte_widths_expr_def, alloc_limits_expr_def, type_builtin_result_ok_def,
     well_typed_type_builtin_args_def] >>
  Cases_on `args` >> gvs[] >> rename1 `h::tl` >> Cases_on `tl` >>
  gvs[well_typed_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.supported_exprs_exists_every,
      byte_widths_expr_def, alloc_limits_expr_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            listTheory.APPEND_ASSOC]
QED

Theorem eval_expr_type_builtin_value:
  !cx ann tb t args es tv es'.
    eval_expr cx (TypeBuiltin ann tb t args) es = (INL tv, es') ==>
    ?v. tv = Value v
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, COND_RATOR] >>
  rw[] >> gvs[AllCaseEqs()]
QED

Theorem compile_convert_stack:
  !cenv ty ann t args sa.
    ?t' op sb. compile_expr cenv ty (TypeBuiltin ann Convert t args) sa =
               (StackValue t' op, sb)
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `t` >> simp[as_stack_val_pair] >> rw[]
QED

Theorem straight_fresh_convert_pair:
  !src t x. int_convert_pair src t ==>
    straight_fresh (compile_type_convert x (mk_convert_op src t))
Proof
  rw[int_convert_pair_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def, straight_fresh_convert] >>
  simp[compile_type_convert_def, straight_fresh_return]
QED

(* A covered conversion: compile_convert_frag_sim, with the argument's
   shape from lower_value_word_shape. *)
Theorem compile_convert_word_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    int_convert_pair (expr_type e1) t ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  rw[expr_vv_case_def] >> drule expr_body_pre_convert >> strip_tac >>
  gvs[exprs_case_def] >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (irule expr_sim_case_apply >> conj_tac >- (qexists `env` >> simp[]) >>
     qexists `nocalls` >> simp[] >>
     metis_tac[int_calls_type_builtin_arg, listTheory.MEM]) >>
  `word_value_type (expr_type e1) /\ is_word_type (expr_type e1) /\
   ~(expr_type e1 = BaseT AddressT /\ ?m. ann = BaseT (BytesT (Fixed m))) /\
   is_word_type ann /\ !n. ann <> FlagT n` by
    gvs[int_convert_pair_def, word_value_type_def, is_word_type_def,
        is_numeric_type_def, is_bool_type_def, is_int_type_def] >>
  irule expr_vv_sim_stack >> rpt conj_tac
  >- simp[compile_convert_stack]
  >- metis_tac[eval_expr_type_builtin_value] >>
  irule compile_convert_frag_sim_word >> rpt conj_tac
  >~ [`lower_value _ _ _ _ _ = _`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`convert_frag _ _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
      drule_all expr_body_pre_word_result >>
      strip_tac >> gvs[] >>
      irule convert_frag_word >> simp[] >>
      qspecl_then [`cenv`, `cx`, `env`, `TypeBuiltin ann Convert ann [e1]`,
                   `es`] mp_tac expr_body_pre_type_evaluates >>
      simp[vyperASTTheory.expr_type_def])
  >~ [`compile_type_convert _ _ _ = _`]
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`compile_type_convert x (mk_convert_op (expr_type e1) ann)`,
                   `sa`, `op`, `sb`] mp_tac straight_fresh_extends >>
      simp[straight_fresh_convert_pair])
  >~ [`IS_SOME _`]
  >- (irule expr_body_pre_type_evaluates >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED
