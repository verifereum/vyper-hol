(* Concrete modular suffix certificates, before expression-post assembly. *)
Theory bodyPtrWordBuiltinsModularCases
Ancestors bodyPtrWordBuiltinsModular bodyPtrWordBuiltinsModularPost
  bodyPtrWordBuiltinsModularSource bodyPtrWordBuiltinsIntervalGhost
  exprSimWordBuiltins exprSimWordArgs fragGasFresh exprLoweringProps
  bodyPtrDefs ptrDiscipline compileEnv fragExec freshWrites
  venomState venomExecSemantics list finite_map valueEncoding integer_word

Theorem word_pow_typed_outcome:
  compile_pow_mod256 a b sa = (op,sb) /\
  value_has_type (BaseTV (UintT 256)) v1 /\ value_has_type (BaseTV (UintT 256)) v2 /\
  (!z. a = Var z ==> not_fresh_at sa z) /\ (!z. b = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME (val_to_w256 v1) /\
  eval_operand b s = SOME (val_to_w256 v2) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann PowMod256 ts [v1;v2],ee)) (es,s,G,tn)
    (\r ee G' tn' u.
      (r = INL (IntV (&w2n (word_exp (val_to_w256 v1) (val_to_w256 v2)))) /\
      ee = es with gas_obs := [] /\ stmt_state_rel ctx func cenv cx es u /\
      eval_operand op u = SOME (word_exp (val_to_w256 v1) (val_to_w256 v2)) /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z u = SOME v) /\
      (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl) /\
      u.vs_memory = s.vs_memory /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
      ghost_inv d cenv cx es G' tn' u /\ ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >>
  `straight_fresh (compile_pow_mod256 a b)` by simp[straight_fresh_compile_modular] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  drule word_pow_cursor_length >> strip_tac >>
  ho_match_mp_tac word_pow_suffix_outcome >>
  qexists_tac `bb` >> simp[allocas_from_def, word_pow_source_typed] >>
  conj_tac
  >- (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> drule_all word_pow_actual_post >> gvs[]
QED

Theorem word_modular_typed_outcome:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  value_has_type (BaseTV (UintT 256)) v1 /\ value_has_type (BaseTV (UintT 256)) v2 /\
  value_has_type (BaseTV (UintT 256)) v3 /\ val_to_w256 v3 <> 0w /\
  (!z. a = Var z ==> not_fresh_at sa z) /\ (!z. b = Var z ==> not_fresh_at sa z) /\
  (!z. c = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME (val_to_w256 v1) /\ eval_operand b s = SOME (val_to_w256 v2) /\
  eval_operand c s = SOME (val_to_w256 v3) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann (if is_mul then MulMod else AddMod) ts [v1;v2;v3],ee))
    (es,s,G,tn)
    (\r ee G' tn' u.
      (r = INL (IntV (&w2n ((if is_mul then mulmod else addmod)
         (val_to_w256 v1) (val_to_w256 v2) (val_to_w256 v3)))) /\
      ee = es with gas_obs := [] /\ stmt_state_rel ctx func cenv cx es u /\
      eval_operand op u = SOME ((if is_mul then mulmod else addmod)
        (val_to_w256 v1) (val_to_w256 v2) (val_to_w256 v3)) /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z u = SOME v) /\
      (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl) /\
      u.vs_memory = s.vs_memory /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
      ghost_inv d cenv cx es G' tn' u /\ ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >>
  `straight_fresh ((if is_mul then compile_mulmod else compile_addmod) a b c)` by
    (Cases_on `is_mul` >> simp[straight_fresh_compile_modular]) >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  drule word_modular_cursor_length >> strip_tac >>
  ho_match_mp_tac word_modular_suffix_outcome >>
  qexists_tac `bb` >> simp[allocas_from_def, word_modular_source_typed] >>
  conj_tac
  >- (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> drule_all word_modular_actual_post >> gvs[]
QED

Theorem word_modular_typed_abort_outcome:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  value_has_type (BaseTV (UintT 256)) v1 /\ value_has_type (BaseTV (UintT 256)) v2 /\
  value_has_type (BaseTV (UintT 256)) v3 /\ val_to_w256 v3 = 0w /\
  eval_operand a s = SOME (val_to_w256 v1) /\ eval_operand b s = SOME (val_to_w256 v2) /\
  eval_operand c s = SOME (val_to_w256 v3) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (\ee. (builtin_result cx ee.accounts ann (if is_mul then MulMod else AddMod) ts [v1;v2;v3],ee))
    (es,s,G,tn) Q (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `straight_fresh ((if is_mul then compile_mulmod else compile_addmod) a b c)` by
    (Cases_on `is_mul` >> simp[straight_fresh_compile_modular]) >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  ho_match_mp_tac word_modular_abort_outcome >>
  qexists_tac `bb` >> simp[allocas_from_def, word_modular_source_typed]
QED
