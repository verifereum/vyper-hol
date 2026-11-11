Theory bodyPtrBopInLiteralContinuation
Ancestors
  bodyPtrBopInLiteralTyped exprSimPtrProps appendStorageGhostPtr
  stmtSimAppendStorageCompose exprSimWordArgs exprSimWordBuiltins
  bodyPtrDefs exprSimDefs loweringPosts compileEnv codegenRel freshWrites exprLoweringProps
  venomState venomExecSemantics ptrDiscipline finite_map list stateFrame
  gasSummaryComposePtr fragGasPathPtr vyperState vyperAST valueEncoding exprLowering loweringSlice

(* The scalar suffix changes only fresh variable bindings and the cursor.
   This boundary packages frames from the actual, not the cleaned, state. *)
Theorem literal_readonly_frames:
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s) /\
  (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) /\
  (tn' with t_var := tn.t_var) = tn /\
  stmt_state_rel ctx fn cenv cx ee s /\ ghost_inv d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  wb_frame cenv es ee sa s0 s /\ sa.cs_next_var <= sm.cs_next_var ==>
  stmt_state_rel ctx fn cenv cx ee t /\ ghost_inv d cenv cx ee G' tn' t /\
  ghost_kept cenv ee sm G tn s G' tn' /\ wb_frame cenv es ee sa s0 t
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ state_frame (t with vs_inst_idx := s.vs_inst_idx) = state_frame s` by
    gvs[venom_state_component_equality, state_frame_def] >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    gvs[taint_component_equality] >>
  conj_tac
  >- (`stmt_state_rel ctx fn cenv cx ee (t with vs_inst_idx := s.vs_inst_idx)`
        suffices_by simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_reserved_frame >> goal_assum (drule_at Any) >>
      qexists_tac `sm` >> gvs[lookup_var_def]) >>
  conj_tac
  >- (irule ghost_inv_fresh_frame >>
      goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      qexists_tac `sm` >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_old_transport >> simp[]) >>
  irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
  qexists_tac `sm` >> simp[]
QED

Theorem literal_bool_post:
  stmt_state_rel ctx fn cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
  eval_operand op t = SOME (bool_to_word b) /\
  op_prov G op = NONE /\ op_taint tn op = {} ==>
  expr_post ctx fn cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee (BoolV b) op t /\
  ptr_val_ok cx (BaseT BoolT) (BoolV b) op G tn t
Proof
  strip_tac >> conj_tac
  >- (irule expr_post_word_intro >>
      simp[expr_type_def, is_word_type_def, word_value_def, val_to_w256_def,
           bool_to_word_def] >> Cases_on `b` >> simp[]) >>
  irule ptr_val_ok_word >> simp[is_word_type_def]
QED

Theorem literal_typed_continuation_summary_ptr:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs) /\
  fn_has_code sm sb fn /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  stmt_state_rel ctx fn cenv cx (ee with gas_obs := []) s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
  sa.cs_next_var <= sm.cs_next_var /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_ptr_at D (ctx,fn) PG []
    (return (BoolV (if bop = In then MEM v vs else ~MEM v vs)))
    (ee with gas_obs := [],s,G,tn)
    (\res fin G' tn' t. ?w. res = INL w /\
      expr_post ctx fn cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray aet n) elems])
        es sa sb s0 fin w op t /\
      ghost_inv d cenv cx fin G' tn' t /\
      ptr_val_ok cx (BaseT BoolT) w op G' tn' t /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin ghosts r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_typed_scalar_path_arbitrary >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    gvs[venom_state_component_equality] >>
  drule_all literal_readonly_frames >> strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_suffix_compose >> goal_assum (drule_at Any) >>
     gvs[taint_component_equality]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BoolV (if bop = In then MEM v vs else ~MEM v vs))`,
    `ee`,`G'`,`tn'`,`OK t`] >>
  simp[vyperStateTheory.return_def] >>
  drule_all literal_bool_post >> disch_tac >> gvs[]
QED
