Theory bodyPtrBopContinuation
Ancestors
  bodyPtrBopParentPost bodyPtrBopSource bodyPtrBopScalarRun exprSimOperators exprSimHyps
  exprSimSource exprSimHypsDefs vyperTypeSystem exprBopLowering
  bodyPtrBopEntry bodyPtrBopOperandContract exprBopSimProps exprSimWordArgs
  bodyPtrDefs loweringPosts bodyPtrBopScalarOutcome bodyPtrBopScalarDispatch
  compileEnv exprLoweringProps localPtrsProps emitHelperProps freshWrites
  list rich_list fragExec bodyPtrBopAnchored bodyPtrBopTypedSource
  bodyPtrBopTypedBytes bodyPtrBopClassification valueEncoding

Theorem bop_pair_source_facts:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) ==>
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  type_bits (expr_type e1) MOD 8 = 0 /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
  (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  (?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
         value_has_type tv1 v1) /\
  (?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
         value_has_type tv2 v2) /\
  expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v1`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v2`, `es2`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `is_word_type ann` by
    (Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def]) >>
  `type_bits (expr_type e1) MOD 8 = 0` by
    (irule byte_widths_expr_type >> gvs[expr_body_pre_def]) >>
  `IS_SOME (evaluate_type (get_tenv cx) ann)` by
    metis_tac[expr_body_pre_type_evaluates, vyperASTTheory.expr_type_def] >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2)` by
    (irule bop_typed_source_result_ok >> simp[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `builtin_operands_ok (Bop bop) [e1;e2]` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[builtin_operands_ok_def, nonneg_int_literal_def, GSYM expr_int_literal_value,
      AllCaseEqs()] >>
  conj_tac >- (Cases_on `expr_int_literal e2` >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem bop_pair_scalar_run:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) /\
  bop_operand_post d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  bop <> In /\ bop <> NotIn /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) /\
  (!z. x = Var z ==> not_fresh_at c2 z) /\
  (!z. y = Var z ==> not_fresh_at c2 z) ==>
  (?v t. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 = INL v /\
    word_value v /\ run_inst_seq (emitted_insts c2 cz) t2 = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts c2 cz) t2 = Abort Revert_abort t)
Proof
  strip_tac >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`, `v1`, `es2`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[word_value_type_word])) >> strip_tac >>
  drule_all bop_pair_word_inputs >> strip_tac >>
  Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
  >- (fs[] >> `word_value v1 /\ word_value v2` by metis_tac[word_value_type_typed] >>
      `eval_operand x t1 = SOME (val_to_w256 v1) /\
       eval_operand y t2 = SOME (val_to_w256 v2)` by
        (gvs[bop_operand_post_def, expr_post_def] >>
         metis_tac[expr_val_rel_word, optionTheory.IS_SOME_EXISTS]) >>
      irule bop_scalar_typed_run >> simp[] >>
      reverse conj_tac >- metis_tac[] >> qexistsl_tac [`x`, `y`] >> simp[]) >>
  drule_all bop_byte_typed_values >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?b1 b2. _` strip_assume_tac >>
  qpat_x_assum `v1 = BytesV _` SUBST_ALL_TAC >>
  qpat_x_assum `v2 = BytesV _` SUBST_ALL_TAC >>
  `eval_operand x t1 = SOME (typed_val_to_w256 tv1 (BytesV b1)) /\
   eval_operand y t2 = SOME (typed_val_to_w256 tv1 (BytesV b2))` by
    metis_tac[bop_operand_post_typed_word] >>
  irule bop_compare_bytes_run >> simp[] >>
  qexistsl_tac [`if bop = Exp then expr_int_literal e1 else NONE`,
    `if bop = Exp then expr_int_literal e2 else NONE`, `tv1`, `expr_type e1`, `x`, `y`] >>
  simp[] >> metis_tac[]
QED

Theorem bop_scalar_parent_outcome:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  bop_operand_entry d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es ca cz op t0 G0 tn0 /\
  bop_operand_post d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) /\
  bop <> In /\ bop <> NotIn /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  cs_extends ca c1 /\ cs_extends c1 c2 /\
  ca.cs_next_var <= c1.cs_next_var /\ ca.cs_next_id <= c1.cs_next_id /\
  c1.cs_next_var <= c2.cs_next_var /\ c1.cs_next_id <= c2.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at c2 z) /\
  es2.gas_obs = [] /\ ~t2.vs_halted ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))
    (es2,t2,G2,tn2)
    (\res ee G tn t. ?v. res = INL v /\
      bop_operand_post d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es ca cz op t0 G0 tn0 v ee t G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`, `v1`, `es2`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[word_value_type_word])) >> strip_tac >>
  drule_all bop_pair_word_inputs >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at c2 z` by metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv c1 /\
   local_ptrs_reserved cenv c2` by
    metis_tac[bop_operand_entry_def, local_ptrs_reserved_next_var] >>
  drule compile_binop_shape >> strip_tac >>
  `fn_has_code c2 cz func` by
    metis_tac[bop_operand_entry_def, fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `?B. (bop_scalar_seq {z | not_fresh_at c2 z}
       ({x;y} UNION IMAGE Lit UNIV) (emitted_insts c2 cz) B /\
     ({x;y} UNION IMAGE Lit UNIV) SUBSET B /\
     cz.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 cz /\
     same_blocks c2 cz /\ c2.cs_next_var <= cz.cs_next_var) /\ op IN B` by
    (irule bop_scalar_compile_binop_typed >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[] >>
     metis_tac[]) >>
  `?bb. lookup_block t2.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts c2 cz) (DROP t2.vs_inst_idx bb.bb_instructions)` by
    (irule bop_suffix_placement >> gvs[bop_operand_post_def] >>
     qexistsl_tac [`c2`, `cz`] >> simp[]) >>
  `ghost_inv d cenv cx es2 G2 tn2 t2` by gvs[bop_operand_post_def] >>
  drule bop_scalar_suffix_outcome_ptr_anchored >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ es2 _ _ _`)) >>
  disch_then (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[bop_operand_entry_def, not_fresh_at_mono] >>
  conj_tac >- metis_tac[bop_operand_entry_def, not_fresh_at_mono] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `t2.vs_current_bb = cz.cs_current_bb /\
       LENGTH (emitted_insts c2 cz) + t2.vs_inst_idx = LENGTH cz.cs_current_insts` by
        (gvs[bop_operand_post_def, same_blocks_def] >> simp[]) >>
      drule_all bop_scalar_parent_success >> simp[]) >>
  conj_tac >- metis_tac[bop_operand_entry_def] >>
  irule bop_pair_scalar_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
