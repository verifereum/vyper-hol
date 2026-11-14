Theory augAssignPtrMemoryOutcome
Ancestors
  augAssignPtrMemoryStore augAssignPtrOperator augAssignPtrMemoryCompose
  bodyPtrIfExpAllocProbe bodyPtrBopInNameBoundary stmtSimAugAssignPlaceMemory
  stmtSimDeclStore stmtSimAugAssign exprSimSource exprBopSimDefs exprSimDefs
  bodyPtrDefs fragGasPathPtr gasSummaryComposePtr gasOutcome ptrDiscipline
  loweringPosts compileEnv vyperState vyperInterpreter venomState words finite_map

(* Q is the consumer's framed statement post.  Its premise mentions the
   actual write_place endpoint, so no source-state equality is guessed. *)
Theorem augassign_memory_binop_write_outcome_ptr:
  compile_binop bop x y ty NONE
    (if bop = Exp then expr_int_literal e else NONE) ca = (op,cb) /\
  emit_void MSTORE [Var dst;op] cb = ((),cc) /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  well_typed_binop ty bop ty (expr_type e) /\ type_bits ty MOD 8 = 0 /\
  (bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e = SOME n ==> rhs = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i) /\
  word_value_type ty /\ word_value_type (expr_type e) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rtv /\ value_has_type rtv rhs /\
  bop <> In /\ bop <> NotIn /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type ptv v) /\
  gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) ee /\
  (!l. x <> Label l /\ y <> Label l) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  fn_has_code ca cb fn /\ fn_has_code cb cc fn /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  (!z. x = Var z ==> not_fresh_at ca z) /\
  (!z. y = Var z ==> not_fresh_at ca z) /\ not_fresh_at ca dst /\
  (!z. not_fresh_at ca z ==> not_fresh_at cb z) /\
  local_ptrs_reserved cenv ca /\
  stmt_state_rel ctx fn cenv cx ee s /\ ghost_inv d cenv cx ee G tn s /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z) /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  (!z w. not_fresh_at origin z /\ lookup_var z s0 = SOME w ==>
    lookup_var z s = SOME w) /\
  ghost_kept cenv frame_es origin G0 tn0 s0 G tn /\
  (!z. not_fresh_at origin z ==> not_fresh_at ca z) /\
  (!v ff H tm t.
    write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    stmt_state_rel ctx fn cenv cx ff t /\ ghost_inv d cenv cx ff H tm t /\
    ~t.vs_halted /\ t.vs_current_bb = cc.cs_current_bb /\
    t.vs_inst_idx = LENGTH cc.cs_current_insts /\
    (!z w. not_fresh_at origin z /\ lookup_var z s0 = SOME w ==>
      lookup_var z t = SOME w) /\
    (!z. not_fresh_at origin z ==> FLOOKUP H z = FLOOKUP G0 z /\
      op_taint tm (Var z) = op_taint tn0 (Var z)) ==>
    Q (INL ()) (ff with gas_obs := []) H tm t) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path))) (ee,s,G,tn)
    Q (\res ff gt r. !tail. stmt_exit_ptr RetQ (ff with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_ptr _ _ _ _ k _ _ _` >>
  Cases_on `k ee` >> rename1 `k ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (unabbrev_all_tac >> drule_all aug_place_pure_suffix_admissible >> simp[]) >>
  `case bop_result cx ty bop [ty;expr_type e] cur rhs ee of
     INR ex => res = INR ex /\ ff = ee
   | INL v => write_place cx (MemoryPlace id path) v ee = (res,ff)` by
    (`bop_result cx ty bop [ty;expr_type e] cur rhs ee =
      case evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
       (irule bop_result_augassign >> simp[] >>
        metis_tac[word_value_type_typed, word_value_not_bytes]) >>
     simp[] >> qpat_x_assum `k ee = _` mp_tac >>
     simp[Abbr `k`, bind_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ptv bop cur rhs` >> simp[return_def, raise_def] >> metis_tac[]) >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee)` by
    (irule aug_place_bop_write_result_ok >> metis_tac[]) >>
  `!z. not_fresh_at origin z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)` by
    (fs[ghost_kept_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_kept cenv frame_es origin G0 tn0 s0 G tn` kall_tac >>
  `!z. not_fresh_at ca z ==> not_fresh_at ca z` by simp[] >>
  `ghost_kept cenv ee ca G tn s G tn` by simp[ghost_kept_refl] >>
  drule augassign_clean_operator_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac)
  >- suspend "normal" >> suspend "abort"
QED

Resume augassign_memory_binop_write_outcome_ptr[normal]:
  gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u)` >>
  `lookup_var dst u = SOME a` by metis_tac[] >>
  `ptr_covers H tm dst u 32` by
    (irule ptr_covers_ghost_kept >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >> metis_tac[]) >>
  `res = INL ()` by (irule aug_place_memory_write_success >> metis_tac[]) >>
  gvs[] >>
  `store_lays_out ptv ptv v` by
    (irule store_lays_out_typed >> metis_tac[word_value_type_word]) >>
  `eval_operand op u = SOME (typed_val_to_w256 ptv v)` by
    simp[Abbr `u`, exprSimPropsTheory.typed_val_to_w256_word_value] >>
  `~u.vs_halted /\ u.vs_current_bb = cb.cs_current_bb /\
    u.vs_inst_idx = LENGTH cb.cs_current_insts /\ ghost_inv d cenv cx ee H tm u` by
    simp[Abbr `u`] >>
  `lookup_var dst u = SOME a` by metis_tac[] >>
  drule_all augassign_memory_store_case_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `Q (INL ()) (ff with gas_obs := []) H tnf sf` by
    (first_x_assum irule >> simp[] >>
     fs[ghost_kept_def, op_taint_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL ()`, `ff`, `H`, `tnf`, `OK sf`] >> simp[] >>
  rewrite_tac[gas_marked_exec_ptr_def] >> conj_tac
  >- (simp[] >> unabbrev_all_tac >>
      drule aug_place_pure_suffix_gas_obs >> simp[]) >>
  simp[] >> metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume augassign_memory_binop_write_outcome_ptr[abort]:
  gvs[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `ee`, `H`, `tm`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def] >>
  rewrite_tac[gas_marked_exec_ptr_def] >> simp[] >>
  unabbrev_all_tac >> drule aug_place_pure_suffix_gas_obs >> simp[]
QED

Finalise augassign_memory_binop_write_outcome_ptr
