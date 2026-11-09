Theory bodyPtrIfExpWord
Ancestors
  bodyPtrDefs bodyPtrPreds exprPtrUnwrap exprSimIfExp exprSimOperators
  bodyPtrIfExpAssignFrame ifJumpPtr gasSummaryComposePtr exprLowering
  vyperAST vyperInterpreter vyperState exprSimUnwrap exprSimUnwrapProps
  loweringPosts loweringHalt fragGasPathPtr context compileEnv

Theorem word_probe_eval_forced[local]:
  eval_expr cx (IfExp t c a b) =
  bind (bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, vyperStateTheory.bind_def]
QED

(* A word annotation does not exclude located operands: those compile to
   active pointer loads.  Calldata alone is ruled out by the vv post. *)
Theorem ifexp_word_unwrap_dispatch:
  vv_post ctx fn cenv cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  is_word_type (expr_type e) ==>
  ty = expr_type e /\ p.ptr_location <> LocCalldata /\
  unwrap_value cenv (LocatedValue ty p) =
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      p.ptr_location p.ptr_operand
Proof
  strip_tac >>
  `ty = expr_type e` by
    (fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  `p.ptr_location <> LocCalldata` by metis_tac[exprSimUnwrapTheory.vv_post_calldata] >>
  simp[unwrap_value_def]
QED

(* The raw StackValue route needs no machine instruction, and preserves
   all ghost/frame facts verbatim.  The active located-load routes do not
   follow from this lemma. *)
Theorem ifexp_stack_unwrap_counted:
  unwrap_value cenv (StackValue ty op) sm = (src,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw (StackValue ty op) s /\
  ptr_vv_ok cx (expr_type e) raw (StackValue ty op) ee G tn s /\
  ~s.vs_halted ==>
  ?v. sb = sm /\ src = op /\ read_result cx raw ee = (INL v,ee) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
      expr_post ctx fn cenv cx e es sa sb s0 ee v src s /\
      ptr_val_ok cx (expr_type e) v src G tn s
Proof
  simp[unwrap_value_def, comp_return_def, ptr_vv_ok_def] >>
  strip_tac >> gvs[] >> conj_tac
  >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  irule expr_post_of_vv_post_stack >>
  drule vv_post_read_result >> disch_then (fn th => fs[th]) >>
  goal_assum drule
QED

Theorem ifexp_word_arm_compile:
  is_word_type res_ty ==>
  compile_ifexp_arm cenv res_ty arm_ty vv = unwrap_value cenv vv
Proof
  simp[compile_ifexp_arm_def]
QED

(* Interface diagnostic: the normal located-word suffix still requires a
   counted pointer counterpart of unwrap_value_path.  Its caller provides
   vv_post and ptr_vv_ok at the raw compile_expr endpoint sm, a successful
   read_result, ghost_inv and original-sa ghost_kept, code sm..sb for
   unwrap_value, word typing and runtime type evaluation, scope-domain and
   compiler-counter monotonicity, oldness of vv_operand and control at sm.
   The required result is a zero-mark gas_path_ptr to sb carrying expr_post,
   ptr_val_ok, ghost_inv and the original-sa ghost_kept.  StackValue is
   checked above. LocatedValue does not reduce to that branch: word loads
   remain for Memory, Storage, Transient and Code; Calldata is impossible.
   The S1 unwrap_value_path is only gas_path and supplies no ghost.  The
   existing typedCopyPtr/stmtAppendStorageRunPtr load results are fixed-run
   instruction interfaces, not this counted semantic consumer. *)

