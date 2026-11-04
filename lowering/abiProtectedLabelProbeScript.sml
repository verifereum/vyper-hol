Theory abiProtectedLabelProbe
Ancestors exprSim exprLoweringProps fragExec compileEnv exprLowering finite_map

Theorem protected_label_name_lower:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) ==>
  lower_value compile_expr ce ty (Name ann id) sa = (Label l,sa)
Proof
  simp[lower_value_def, comp_bind_def,
       Once compile_expr_def, compile_expr_body_def, compile_name_vv_def,
       unwrap_value_def, contextTheory.mk_ptr_def,
       comp_return_def]
QED

Theorem protected_label_name_sim:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) /\
  ce.ce_imm_alloca = SOME (Label l) /\
  evaluate_type (get_tenv cx) (expr_type (Name ann id)) = NONE /\
  (do r <- eval_expr cx (Name ann id); read_result cx r od) es = (INL v,es) ==>
  expr_sim ctx func ce cx (expr_type (Name ann id)) (Name ann id) es
Proof
  strip_tac >> rw[expr_sim_def] >>
  drule_all protected_label_name_lower >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> simp[expr_post_def, expr_val_at_def,
    expr_val_rel_def, stmt_state_rel_def, immutable_base_zero_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A nonword annotation with no evaluated type, independent of the tenv.
   This checks the candidate branch only, not satisfiability of the state seed. *)
Theorem protected_label_candidate_type:
  ~is_word_type (ArrayT (BaseT BoolT) (Fixed 0)) /\
  evaluate_type E (ArrayT (BaseT BoolT) (Fixed 0)) = NONE
Proof
  EVAL_TAC
QED

Theorem protected_label_candidate_eval:
  let es' = es with scopes :=
    [FEMPTY |+ ("x", <|type := BaseTV BoolT; value := NoneV|>)] in
  (do r <- eval_expr cx (Name (ArrayT (BaseT BoolT) (Fixed 0)) "x");
      read_result cx r od) es' = (INL NoneV,es')
Proof
  EVAL_TAC
QED

Definition protected_probe_ce_def:
  protected_probe_ce ce = ce with <|
    ce_vars := FEMPTY |+ ("x", PtrVar (Label "protected") 0);
    ce_imm_alloca := SOME (Label "protected"); ce_is_ctor := F;
    ce_module_vars := FEMPTY |>
End

Definition protected_probe_es_def:
  protected_probe_es = vyperState$empty_state with <|
    scopes := [FEMPTY |+ ("x", <|type := BaseTV BoolT; value := NoneV|>)];
    outcomes := SOME [] |>
End

Definition protected_probe_fn_def:
  protected_probe_fn fn = fn with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions := []|>]
End

Definition protected_probe_cx_def:
  protected_probe_cx = vyperContext$empty_evaluation_context with
    txn := vyperContext$empty_call_txn with <|block_number := 1; block_hashes := [0w]|>
End

Definition protected_probe_s_def:
  protected_probe_s = (init_venom_state "entry") with <|
    vs_labels := FEMPTY |+ ("protected",0w);
    vs_block_ctx := empty_block_context with bc_number := 1w |>
End

Theorem protected_probe_seed:
  stmt_state_rel
    (ctx with ctx_functions := [protected_probe_fn fn])
    (protected_probe_fn fn) (protected_probe_ce ce)
    protected_probe_cx protected_probe_es protected_probe_s
Proof
  `fn_directly_calls (ctx with ctx_functions := [protected_probe_fn fn]) =
    (\x y. F)` by
    (simp[FUN_EQ_THM, fcgDefsTheory.fn_directly_calls_def,
      venomInstTheory.lookup_function_def, protected_probe_fn_def,
      venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
      listTheory.FIND_thm] >> metis_tac[]) >>
  fs[protected_probe_fn_def] >>
  simp[stmt_state_rel_def, state_rel_def] >> rpt conj_tac >> EVAL_TAC >>
  simp[venomInstTheory.fn_insts_blocks_def, venomStateTheory.eval_operand_def,
       FLOOKUP_UPDATE] >> EVAL_TAC >>
  simp[Once relationTheory.TC_CASES1] >>
  simp[Once relationTheory.TC_CASES1]
QED

Definition protected_probe_sa_def:
  protected_probe_sa sa = sa with <|cs_current_bb := "entry";
    cs_current_insts := []; cs_blocks := []|>
End

Theorem protected_probe_code:
  fn_has_code (protected_probe_sa sa) (protected_probe_sa sa) (protected_probe_fn fn) /\
  fn_inst_ids_distinct (protected_probe_fn fn) /\
  local_ptrs_reserved (protected_probe_ce ce) (protected_probe_sa sa)
Proof
  simp[fn_has_code_def, emitted_blocks_def, protected_probe_sa_def,
    protected_probe_fn_def, venomInstTheory.lookup_block_def,
    listTheory.FIND_thm, venomWfTheory.fn_inst_ids_distinct_def,
    venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
    local_ptrs_reserved_def, protected_probe_ce_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* All premises of abi_args_success_not_label, and its negated conclusion.
   This is a helper-contract counterexample, NOT an endpoint counterexample. *)
Theorem protected_label_full_premise_counterexample:
  let e = Name (ArrayT (BaseT BoolT) (Fixed 0)) "x";
      c = protected_probe_ce ce;
      f = protected_probe_fn fn;
      a = protected_probe_sa sa;
      ct = ctx with ctx_functions := [f] in
  expr_sim ct f c protected_probe_cx (expr_type e) e protected_probe_es /\
  lower_value compile_expr c (expr_type e) e a = (Label "protected",a) /\
  (do r <- eval_expr protected_probe_cx e;
      read_result protected_probe_cx r od) protected_probe_es =
        (INL NoneV,protected_probe_es) /\
  fn_has_code a a f /\ fn_inst_ids_distinct f /\
  local_ptrs_reserved c a /\
  stmt_state_rel ct f c protected_probe_cx protected_probe_es protected_probe_s /\
  ~(!l. Label "protected" <> Label l)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `~is_word_type (expr_type (Name (ArrayT (BaseT BoolT) (Fixed 0)) "x")) /\
   evaluate_type (get_tenv protected_probe_cx)
     (expr_type (Name (ArrayT (BaseT BoolT) (Fixed 0)) "x")) = NONE` by EVAL_TAC >>
  ` (do r <- eval_expr protected_probe_cx
          (Name (ArrayT (BaseT BoolT) (Fixed 0)) "x");
        read_result protected_probe_cx r od) protected_probe_es =
      (INL NoneV,protected_probe_es)` by EVAL_TAC >>
  simp[protected_probe_seed, protected_probe_code] >>
  conj_tac >- (irule protected_label_name_sim >>
    simp[protected_probe_ce_def, FLOOKUP_UPDATE]) >>
  irule protected_label_name_lower >>
  simp[protected_probe_ce_def, FLOOKUP_UPDATE]
QED
