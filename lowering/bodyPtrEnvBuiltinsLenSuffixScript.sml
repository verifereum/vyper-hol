(* Post framing for the raw value/place length suffix. *)
Theory bodyPtrEnvBuiltinsLenSuffix
Ancestors
  bodyPtrEnvBuiltinsLen bodyPtrEnvBuiltinsLenSource bodyPtrEnvBuiltinsOperandFrame
  bodyPtrDefs context loweringPosts exprSimDefs exprSimProps exprLoweringProps compileEnv loweringStateRelDefs
  exprSimLen vyperState vyperAST vyperTyping vyperValue valueEncoding integer_word freshWrites

Theorem len_builtin_post_frame:
  !func cenv cx e es sa sm sb s0 es' tv vv s1 op s n ctx.
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s1 /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' s /\ eval_operand op s = SOME (n2w n) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\ s.vs_memory = s1.vs_memory ==>
    vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
      sa sb s0 es' (Value (IntV (&n))) (StackValue (BaseT (UintT 256)) op) s
Proof
  rw[vv_post_def]
  >~ [`vv_holds`]
  >- simp[vv_holds_def, read_result_def, return_def, expr_val_rel_def, expr_type_def, is_word_type_def,
          evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
          integer_wordTheory.i2w_def]
  >~ [`vv_at`]
  >- simp[vv_at_def, expr_val_at_def, expr_type_def, is_word_type_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- (fs[vv_post_def] >> metis_tac[])
  >~ [`locals_kept`]
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem len_operand_header:
  !env ctx fn cenv cx ty r vv es s tv.
    stmt_state_rel ctx fn cenv cx es s /\
    vv_holds cenv cx ty r vv es s /\ is_sized_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,es) r (Type ty) /\
    (!v. read_result cx r es = (INL v,es) ==> value_has_type tv v) ==>
    ?n w. result_array_length cx r es = (INL n,es) /\
      eval_operand (vv_operand vv) s = SOME w /\
      ptr_load_val cenv.ce_is_ctor
        (case vv_location vv of SOME l => l | NONE => LocMemory) w s = n2w n /\
      (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata
Proof
  rpt gen_tac >> strip_tac >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  qexistsl_tac [`n`, `w`] >> simp[] >>
  Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> gvs[]
QED

Theorem len_vv_path_ptr:
  !env ctx func PG d cenv cx e es sa sm sb s0 es' r vv op tv t G0 tn0 G tn.
    post_value_type cenv e = expr_type e /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\ ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
    is_sized_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es') r (Type (expr_type e)) /\
    (!v. read_result cx r es' = (INL v,es') ==> value_has_type tv v) /\
    fn_has_code sm sb func /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sm s0 es' r vv t /\
    ptr_vv_ok cx (expr_type e) r vv es' G tn t /\
    ghost_inv d cenv cx es' G tn t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ?n t' G' tn'.
      gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G' tn' (OK t') /\
      result_array_length cx r es' = (INL n,es') /\
      vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
        sa sb s0 es' (Value (IntV (&n))) (StackValue (BaseT (UintT 256)) op) t' /\
      t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx es' G' tn' t' /\
      ptr_vv_ok cx (BaseT (UintT 256)) (Value (IntV (&n)))
        (StackValue (BaseT (UintT 256)) op) es' G' tn' t' /\
      (!ty op'. StackValue (BaseT (UintT 256)) op = StackValue ty op' /\
         ~is_word_type (expr_type (Builtin (BaseT (UintT 256)) Len [e])) ==>
         ptr_buf_ok cenv (Builtin (BaseT (UintT 256)) Len [e]) op' G' t') /\
      (!ty p. StackValue (BaseT (UintT 256)) op = LocatedValue ty p /\
         p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv (Builtin (BaseT (UintT 256)) Len [e]) p.ptr_operand G' t') /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' t /\
   vv_holds cenv cx (expr_type e) r vv es' t` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[vv_post_def] >>
     qpat_assum `post_value_type cenv e = _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all len_operand_header >> strip_tac >>
  qabbrev_tac `loc = case vv_location vv of SOME l => l | NONE => LocMemory` >>
  `?opc.
    compile_builtin_len F cenv.ce_imm_alloca (vv_operand vv) loc = emit_op opc [vv_operand vv] /\
    MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
    ptr_inst_ok (cx_dead cx) 0 0 ctx func G tn
      (mk_inst sm.cs_next_id opc [vv_operand vv] [STRING #"%" (toString sm.cs_next_var)]) t /\
    step_inst_base (mk_inst sm.cs_next_id opc [vv_operand vv]
      [STRING #"%" (toString sm.cs_next_var)]) t =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) (ptr_load_val F loc w t) t) /\
    op_taint (step_taint (mk_inst sm.cs_next_id opc [vv_operand vv]
      [STRING #"%" (toString sm.cs_next_var)]) t
      (update_var (STRING #"%" (toString sm.cs_next_var)) (ptr_load_val F loc w t) t) tn)
      (Var (STRING #"%" (toString sm.cs_next_var))) = {}` by
    (irule ptr_vv_length_instruction_properties >> simp[Abbr `loc`] >> metis_tac[]) >>
  `emit_op opc [vv_operand vv] sm = (op,sb)` by
    (qpat_x_assum `compile_builtin_len _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `ptr_load_val F loc w t = n2w n` by
    (qpat_x_assum `ptr_load_val _ _ _ _ = _` mp_tac >> simp[]) >>
  `step_inst_base (mk_inst sm.cs_next_id opc [vv_operand vv]
     [STRING #"%" (toString sm.cs_next_var)]) t =
     OK (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t)` by metis_tac[] >>
  `op_taint (step_taint (mk_inst sm.cs_next_id opc [vv_operand vv]
     [STRING #"%" (toString sm.cs_next_var)]) t
     (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t) tn)
     (Var (STRING #"%" (toString sm.cs_next_var))) = {}` by metis_tac[] >>
  `~not_fresh_at sa (STRING #"%" (toString sm.cs_next_var))` by
    (simp[not_fresh_at_def] >> metis_tac[]) >>
  drule_all emit_load_builtin_run >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`n`, `t'`, `G'`, `tn'`] >>
  simp[expr_type_def, is_word_type_def] >>
  conj_tac
  >- (irule len_builtin_post_frame >> simp[] >>
      qexistsl_tac [`t`, `sm`, `r`, `vv`] >> simp[]) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, return_def,
       is_word_type_def]
QED
