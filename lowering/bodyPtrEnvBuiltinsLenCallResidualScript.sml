(* Residual leaf for Len over an internal call whose lowered return type
   differs from the call site's annotation. *)
Theory bodyPtrEnvBuiltinsLenCallResidual
Ancestors
  bodyPtrDefs exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  compileEnv loweringStateRelDefs context vyperAST bodyPtrEnvBuiltinsLenSuffix
  bodyPtrEnvBuiltinsBoundary exprSimLen vyperTypeSystem vyperTyping
  vyperValue valueEncoding valueEncodingDefs vyperState vyperInterpreter exprPtrUnwrapStorageShape
  bodyPtrEnvBuiltinsLen exprLowering venomExecSemantics venomState builtinProps
  bodyPtrEnvBuiltinsLenSource gasSummaryComposePtr fragGasPathPtr
  exprLoweringProps gasSummary fragGasPath fragGasMode
  exprSimProps exprSimSource exprSimUnwrap fragExec vyperTypeInvariants
  vyperContext

Theorem len_widened_memory_observation[local]:
  !tenv pt t pvt tvt v a mem cx es.
    type_widens_to tenv pt t /\ is_sized_type t /\
    evaluate_type tenv pt = SOME pvt /\
    evaluate_type tenv t = SOME tvt /\ value_has_type tvt v /\
    val_in_memory pvt v a mem ==>
    is_sized_type pt /\
    ?n. result_array_length cx (Value v) es = (INL n,es) /\
        mem_word_at a mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  gvs[type_widens_to_def]
  >- metis_tac[sized_memory_header] >>
  Cases_on `t` >> gvs[is_sized_type_def]
  >- (Cases_on `b` >> gvs[is_sized_type_def]
      >~ [`BytesT bd`]
      >- (Cases_on `bd` >> gvs[is_sized_type_def] >>
          Cases_on `pt` >> gvs[arg_type_fits_def] >>
          Cases_on `b` >> gvs[arg_type_fits_def] >>
          Cases_on `b'` >> gvs[arg_type_fits_def, evaluate_type_def,
            is_sized_type_def, AllCaseEqs()] >>
          Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def,
            result_array_length_def, read_result_def, bind_def, return_def]) >>
      Cases_on `pt` >> gvs[arg_type_fits_def] >>
      Cases_on `b` >> gvs[arg_type_fits_def, evaluate_type_def,
        is_sized_type_def, AllCaseEqs()] >>
      Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def,
        result_array_length_def, read_result_def, bind_def, return_def]) >>
  Cases_on `b` >> gvs[is_sized_type_def] >>
  Cases_on `pt` >> gvs[arg_type_fits_def] >>
  Cases_on `b` >> gvs[arg_type_fits_def, evaluate_type_def,
    is_sized_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def] >>
  Cases_on `a'` >> gvs[value_has_type_def, val_in_memory_def,
    result_array_length_def, read_result_def, bind_def, return_def]
QED

Theorem len_widened_post_sized[local]:
  type_widens_to tenv pt t /\ is_sized_type t ==> is_sized_type pt
Proof
  strip_tac >> gvs[type_widens_to_def] >>
  Cases_on `t` >> gvs[is_sized_type_def]
  >- (Cases_on `b` >> gvs[is_sized_type_def]
      >~ [`BytesT bd`]
      >- (Cases_on `bd` >> gvs[is_sized_type_def] >>
          Cases_on `pt` >> gvs[arg_type_fits_def, is_sized_type_def] >>
          Cases_on `b` >> gvs[arg_type_fits_def, is_sized_type_def] >>
          Cases_on `b'` >> gvs[arg_type_fits_def, is_sized_type_def]) >>
      Cases_on `pt` >> gvs[arg_type_fits_def, is_sized_type_def] >>
      Cases_on `b` >> gvs[arg_type_fits_def, is_sized_type_def]) >>
  Cases_on `b` >> gvs[is_sized_type_def] >>
  Cases_on `pt` >> gvs[arg_type_fits_def, is_sized_type_def] >>
  Cases_on `b` >> gvs[arg_type_fits_def, is_sized_type_def]
QED

Theorem len_widened_memory_view[local]:
  compile_expr cenv ty e sa = (vv,sm) /\
  post_value_type cenv e <> expr_type e /\
  vv_holds cenv cx (post_value_type cenv e) r vv es s /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt ==>
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  ?v w. read_result cx r es = (INL v,es) /\
    eval_operand (vv_operand vv) s = SOME w /\
    val_in_memory pvt v (w2n w) s.vs_memory
Proof
  strip_tac >> Cases_on `vv`
  >- gvs[vv_holds_def, expr_val_rel_def, vv_location_def, vv_operand_def] >>
  `p.ptr_location = LocMemory` by
    (spose_not_then assume_tac >>
     drule_all compile_nonmemory_lowered_value_type >>
     metis_tac[post_value_type_lowered]) >>
  gvs[vv_holds_def, vv_location_def, vv_operand_def] >> metis_tac[]
QED

Theorem len_widened_operand_header[local]:
  compile_expr cenv ty e sa = (vv,sm) /\
  post_value_type cenv e <> expr_type e /\
  vv_holds cenv cx (post_value_type cenv e) r vv es s /\
  ptr_vv_ok cx (post_value_type cenv e) r vv es G tn s /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
  is_sized_type (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es) r (Type (expr_type e)) /\
  (!v. read_result cx r es = (INL v,es) ==> value_has_type tv v) ==>
  ?n w. result_array_length cx r es = (INL n,es) /\
    eval_operand (vv_operand vv) s = SOME w /\
    (case vv_location vv of SOME l => l | NONE => LocMemory) = LocMemory /\
    ptr_load_val F LocMemory w s = n2w n /\
    op_taint tn (vv_operand vv) = {} /\
    (?p. vv_operand vv = Var p /\ ptr_covers G tn p s 32) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `is_sized_type (post_value_type cenv e)` by metis_tac[len_widened_post_sized] >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[sized_type_not_word] >>
  drule_all len_widened_memory_view >> strip_tac >>
  `value_has_type tv v` by metis_tac[] >>
  drule_all len_widened_memory_observation >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
  `result_array_length cx (Value v) es = result_array_length cx r es` by
    (irule sized_read_result_length >>
     metis_tac[]) >>
  `ptr_val_ok cx (post_value_type cenv e) v (vv_operand vv) G tn s` by
    (Cases_on `vv` >> gvs[ptr_vv_ok_def, ptr_val_ok_def, vv_operand_def,
                           vv_location_def] >> metis_tac[]) >>
  `ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) G tn s` by
    fs[ptr_val_ok_def] >>
  `!mem. val_in_memory pvt v (w2n w) mem ==>
    mem_word_at (w2n w) mem = n2w n` by
    (rpt strip_tac >> drule_all len_widened_memory_observation >>
     disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]) >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[ptr_mem_ok_header_clean] >>
  drule_all sized_ptr_val_header_covers >> strip_tac >>
  qexistsl_tac [`n`, `w`] >>
  gvs[ptr_val_ok_def, ptr_load_val_def, mload_def, mem_word_at_def,
      AllCaseEqs()]
QED

Theorem len_widened_path_ptr[local]:
  !env ctx func PG d cenv cx ty e se es sa sm sb s0 es' r vv op tv pvt t G0 tn0 G tn.
    post_value_type cenv e <> expr_type e /\
    compile_expr cenv ty e se = (vv,sm) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
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
    ptr_vv_ok cx (post_value_type cenv e) r vv es' G tn t /\
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
      ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' t /\
   vv_holds cenv cx (post_value_type cenv e) r vv es' t` by fs[vv_post_def] >>
  drule_all len_widened_operand_header >> strip_tac >>
  `?opc.
    compile_builtin_len F cenv.ce_imm_alloca (vv_operand vv) LocMemory =
      emit_op opc [vv_operand vv] /\
    MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
    ptr_inst_ok (cx_dead cx) 0 0 ctx func G tn
      (mk_inst sm.cs_next_id opc [vv_operand vv] [STRING #"%" (toString sm.cs_next_var)]) t /\
    step_inst_base (mk_inst sm.cs_next_id opc [vv_operand vv]
      [STRING #"%" (toString sm.cs_next_var)]) t =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t) /\
    op_taint (step_taint (mk_inst sm.cs_next_id opc [vv_operand vv]
      [STRING #"%" (toString sm.cs_next_var)]) t
      (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t) tn)
      (Var (STRING #"%" (toString sm.cs_next_var))) = {}` by
    (qpat_assum `ptr_load_val _ _ _ _ = _`
       (fn th => rewrite_tac[GSYM th]) >>
     irule length_load_instruction_properties >> simp[] >> metis_tac[]) >>
  `emit_op opc [vv_operand vv] sm = (op,sb)` by gvs[] >>
  `~not_fresh_at sa (STRING #"%" (toString sm.cs_next_var))` by
    (simp[not_fresh_at_def] >> metis_tac[]) >>
  drule_all emit_load_builtin_run >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`n`, `t'`, `G'`, `tn'`] >> simp[] >>
  conj_tac
  >- (irule len_builtin_post_frame >> simp[] >>
      qexistsl_tac [`t`, `sm`, `r`, `vv`] >> simp[]) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, return_def, is_word_type_def]
QED

(* Len of an internal-call source whose lowered return type differs from
   its annotation (Decision 18). Intuition: post_value_type cenv e widens to
   expr_type e (exprSimHyps.post_value_type_widens), and post_type_evaluates
   gives it an evaluated type. Len loads only the 32-byte header word
   [w, w+32); its pointer coverage follows from ptr_val_ok at the post type
   (sized_ptr_val_header_covers, since 32 <= val_footprint), and its
   cleanliness from ptr_mem_ok_header_clean via val_in_memory under
   type_widens_to + value_has_type, as exprSimLen's *_widens lemmas do for
   the non-pointer simulation. The eq-typed sibling
   compile_len_singleton_eq_sim_ptr (bodyPtrEnvBuiltinsLenCase) is the
   template. *)
Theorem compile_len_singleton_call_sim_ptr:
  !d ctx PG func cenv cx env ty e es.
    post_value_type cenv e <> expr_type e /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type (expr_type e)` by (drule len_builtin_pre_shape >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e)` by
    (fs[expr_body_pre_def] >> metis_tac[post_value_type_widens]) >>
  drule_all post_type_evaluates >> strip_tac >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  gvs[len_compile_split] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv,sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  drule_all len_builtin_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `evv`, `s0`] mp_tac) >>
  disch_then (qspecl_then [`G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked])
      >- suspend "normal"
      >> suspend "exception") >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule len_builtin_exempt_cert >> simp[]
QED

Resume compile_len_singleton_call_sim_ptr[normal]:
  gvs[] >>
  `gas_marked_exec F (ctx,func) (eval_expr cx e)
    (es,s0) marks (INL tv') es_end (OK t)` by
    metis_tac[gas_marked_exec_ptr_exec] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL tv',es_end with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,es_end with gas_obs := []) tv' (Type (expr_type e)) /\
    (!v. read_result cx tv' (es_end with gas_obs := []) =
       (INL v,es_end with gas_obs := []) ==> value_has_type tvt v)` by
    (irule expr_body_pre_runtime_typed >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `cenv` >> simp[]) >>
  `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm = (q,r)` by simp[] >>
  drule_all len_widened_path_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL (Value (IntV (&n)))`, `es_end`, `G'`, `tn'`, `OK t'`] >>
  simp[expr_type_def, is_word_type_def] >>
  rewrite_tac[len_builtin_source] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
    |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`G`, `es_end`, `t`, `tn`, `tv'`] >> simp[] >>
  simp[gas_marked_exec_ptr_def, bind_def, return_def] >>
  rpt strip_tac >>
  qspecl_then [`cx`, `tv'`, `es_end with gas_obs := []`, `tail`]
    mp_tac len_result_length_observation >> simp[]
QED

Resume compile_len_singleton_call_sim_ptr[exception]:
  gvs[] >> Cases_on `res` >- fs[expr_exit_def] >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r'`] >> simp[] >>
  rewrite_tac[len_builtin_source] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED

Finalise compile_len_singleton_call_sim_ptr
