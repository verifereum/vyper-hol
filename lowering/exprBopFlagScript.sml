(* Counted binary operator producer and its source facts. *)
Theory exprBopFlag
Ancestors
  exprBopSimDefs exprBopSimProps exprSimBopTyped exprBopStraight
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib

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
    m <= 256 /\ expr_res_ok (bop_result cx ann bop tys v1 v2 es) ==>
    bop_result cx ann bop tys v1 v2 es =
      INL (BoolV
        (if bop = In then word_and (val_to_w256 v1) (val_to_w256 v2) <> 0w
         else word_and (val_to_w256 v1) (val_to_w256 v2) = 0w))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  Cases_on `v2` >> gvs[value_has_type_def] >>
  rename1 `bop_result _ _ _ tys (FlagV k1) (FlagV k2) _` >>
  Cases_on `evaluate_type (get_tenv cx) (EL 1 tys)` >>
  gvs[bop_result_def, evaluate_membership_def, evaluate_binop_def,
      expr_res_ok_def, binop_negate_def, val_to_w256_def] >>
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
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> metis_tac[straight_fresh_flag_in]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `m`, `v1`, `v2`, `es0`] mp_tac
    bop_result_flag_in >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  disj1_tac >> simp[word_value_def] >> rpt strip_tac >>
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
