Theory bodyPtrCodeSliceExternal
Ancestors
  bodyPtrCodeSliceExternalEntry bodyPtrCodeSliceSelfOperands bodyPtrCodeSliceSelf
  bodyPtrCodeSliceExternalJoin bodyPtrPreds bodyPtrDefs exprPtrUnwrap
  exprSimSliceExtcodeTyped exprSimSliceExtcodeContext exprSimSliceSource
  exprSimSource exprSimHyps exprSimHypsDefs exprSimWordArgs exprSimPrecompiles
  typedWordArgsReadyPtr gasSummaryComposePtr gasOutcomeMarkedPtr
  exprLoweringProps exprLowering exprBopLowering builtinBytes compileEnv
  vyperInterpreter vyperContext vyperState

(* Rebase a tail's post over the start and length operand evaluations. *)
Theorem code_slice_external_post_rebase:
  stmt_state_rel ctx func cenv cx ec u /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
  MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  expr_post ctx func cenv cx start ec sc sd u e1 v1 op1 t /\
  expr_post ctx func cenv cx len e1 sd se t e2 v2 op2 r /\
  (~expr_has_effect result ==> ~expr_has_effect start /\ ~expr_has_effect len) /\
  vv_post ctx func cenv cx result e2 se sf r ef tv vv z /\
  ghost_kept cenv ec sc G0 tn0 u G1 tn1 /\
  ghost_kept cenv e1 sd G1 tn1 t G2 tn2 /\
  ghost_kept cenv e2 se G2 tn2 r G tn ==>
  vv_post ctx func cenv cx result ec sc sf u ef tv vv z /\
  ghost_kept cenv ec sc G0 tn0 u G tn
Proof
  strip_tac >> conj_tac
  >- (mp_tac (SPEC_ALL
        exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  `wb_frame cenv ec e1 sc u t /\ wb_frame cenv e1 e2 sd t r` by
    metis_tac[expr_post_frame] >>
  `stmt_state_rel ctx func cenv cx e1 t` by metis_tac[expr_post_state] >>
  `ghost_kept cenv e1 sd G1 tn1 t G tn` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     qpat_assum `ghost_kept cenv e2 se G2 tn2 r G tn` (irule_at Any) >>
     qpat_assum `ghost_kept cenv e1 sd G1 tn1 t G2 tn2` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  irule wordArgsPtrTheory.ghost_kept_wb_trans >>
  qpat_assum `ghost_kept cenv e1 sd G1 tn1 t G tn` (irule_at Any) >>
  qpat_assum `ghost_kept cenv ec sc G0 tn0 u G1 tn1` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem code_slice_external_vv_ptr:
  ~is_self_code (Builtin ct (Acc Code) [a]) /\
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [start;len] /\
  (!s vs t. eval_exprs cx [start;len] s = (INL vs,t) ==>
    body_exprs_ptr_ok cx [a]) /\
  expr_body_pre cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) es
Proof
  strip_tac >> drule code_slice_external_typing >> strip_tac >> gvs[] >>
  `!e ee. MEM e [start;len] /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac >> drule_all code_slice_external_operand_pre >> strip_tac >>
     fs[is_word_type_def] >> metis_tac[]) >>
  `typed_args_ready ctx func cenv cx (K ty) (expr_sim_inv cenv cx env) [start;len]` by
    (irule code_slice_typed_args_ready_of_body >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `tops` >> simp[]) >>
  `ptr_args_ready d ctx PG func cenv cx (K ty) (expr_sim_inv cenv cx env) [start;len]` by
    (irule body_exprs_ptr_ok_ready >> goal_assum (drule_at Any) >> metis_tac[]) >>
  rw[expr_vv_sim_ptr_def] >>
  drule_all code_slice_external_lowering >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es /\ expr_body_pre cenv cx env start es /\
   expr_body_pre cenv cx env len es` by
    (fs[expr_body_pre_def] >> metis_tac[]) >>
  suspend "context"
QED

Resume code_slice_external_vv_ptr[context]:
  `as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
    (compile_slice_extcode aop sop lop
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sq) =
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr r LocMemory),sb)` by
    simp[as_ptr_val_def] >>
  drule_all slice_extcode_pipeline_context >> strip_tac >>
  `fn_has_code sa sn func` by
    (irule fragExecTheory.fn_has_code_mid >> fs[ci_mono_def] >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  drule slice_extcode_actions >> disch_then (fn th => rewrite_tac[th]) >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
    expr_sim_inv cenv cx env (ee with gas_obs := gs)` by
    simp[] >>
  drule_all (code_slice_uint_head_outcome_ptr |>
    Q.INST [`arg_ty` |-> `K ty`, `Inv` |-> `expr_sim_inv cenv cx env`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (mp_tac o MATCH_MP code_slice_ptr_outcome_with_exec) >>
  disch_tac >>
  irule gas_outcome_ptr_bind >> BETA_TAC >> simp[] >>
  suspend "start_bind"
QED

Resume code_slice_external_vv_ptr[start_bind]:
  conj_tac
  >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      asm_rewrite_tac[ignore_bind_def] >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      asm_rewrite_tac[ignore_bind_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (Cases >> simp[] >> rpt strip_tac >>
    metis_tac[exprSimHashTheory.expr_exit_INR_cast]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >>
  suspend "length"
QED

Resume code_slice_external_vv_ptr[length]:
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `expr_body_pre cenv cx env len (raw with gas_obs := [])` by
    (first_x_assum (qspec_then `len` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env (raw with gas_obs := [])` by simp[] >>
  `stmt_state_rel ctx func cenv cx (raw with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
    expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  drule_all (code_slice_uint_head_outcome_ptr |>
    Q.INST [`arg_ty` |-> `K ty`, `Inv` |-> `expr_sim_inv cenv cx env`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (mp_tac o MATCH_MP code_slice_ptr_outcome_with_exec) >>
  disch_tac >>
  irule gas_outcome_ptr_bind >> BETA_TAC >> simp[] >>
  suspend "length_bind"
QED

Resume code_slice_external_vv_ptr[length_bind]:
  conj_tac
  >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      asm_rewrite_tac[ignore_bind_def] >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      asm_rewrite_tac[ignore_bind_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (Cases >> simp[] >> rpt strip_tac >>
    metis_tac[exprSimHashTheory.expr_exit_INR_cast]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >>
  suspend "address"
QED

Resume code_slice_external_vv_ptr[address]:
  `?s vs t. eval_exprs cx [start;len] s = (INL vs,t)` by
    (irule slice_two_marked_reads_success >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `body_exprs_ptr_ok cx [a]` by metis_tac[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `expr_body_pre cenv cx env a (raw' with gas_obs := [])` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _`
       (mp_then Any mp_tac slice_code_address_body_pre) >> simp[]) >>
  `expr_sim_ptr d ctx PG func cenv cx ty a (raw' with gas_obs := [])` by
    (qpat_assum `body_exprs_ptr_ok cx [a]` mp_tac >>
     simp_tac (srw_ss()) [body_exprs_ptr_ok_def, body_expr_ptr_ok_def] >>
     strip_tac >> first_x_assum (mp_tac o cj 1) >>
     metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (raw' with gas_obs := []) t'` by
    metis_tac[expr_post_state] >>
  `?gs. bind (eval_expr cx len) (read_result cx)
      ((raw with gas_obs := []) with gas_obs := gs) =
      (INL (IntV (&i')),raw' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ (INL (IntV (&i'))) _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `i' <= n` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >> rename1 `Literal lt lit` >>
     Cases_on `lit` >> simp[] >> strip_tac >> gvs[] >>
     drule exprSimSliceCapacityReadTheory.slice_literal_read_length >> intLib.ARITH_TAC) >>
  suspend "operand_frames"
QED

Resume code_slice_external_vv_ptr[operand_frames]:
  `(!z. sop = Var z ==> not_fresh_at sm z) /\ (!l. sop <> Label l)` by
    (qpat_assum `lower_value _ _ _ start _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `(!z. lop = Var z ==> not_fresh_at sn z) /\ (!l. lop <> Label l)` by
    (qpat_assum `lower_value _ _ _ len _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `!z. aop = Var z ==> not_fresh_at sq z` by
    (qpat_assum `lower_value _ _ _ a _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `wb_frame cenv (raw with gas_obs := []) (raw' with gas_obs := []) sm t t'` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `eval_operand sop t' = SOME (n2w i) /\ op_taint tn' sop = {} /\
   op_prov G' sop = NONE` by
    (drule_all code_slice_word_operand_frame >> simp[]) >>
  `!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sn x)` by
    (Cases_on `sop` >> Cases_on `lop` >> gvs[] >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  suspend "join"
QED

Resume code_slice_external_vv_ptr[join]:
  `fn_has_code sn sb func` by
    (irule fragExecTheory.fn_has_code_mid >> fs[ci_mono_def] >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  mp_tac (Q.INST [`sa` |-> `sn`, `sb` |-> `sq`, `sc` |-> `sb`, `fn` |-> `func`,
    `sz` |-> `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
    `es` |-> `raw' with gas_obs := []`, `s` |-> `t'`, `G0` |-> `G'`,
    `tn0` |-> `tn'`, `k` |-> `i'`,
    `tys` |-> `[ct; BaseT (UintT 256); BaseT (UintT 256)]`,
    `result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [a];start;len]`]
    external_code_continue_outcome_ptr) >>
  simp[vyperASTTheory.expr_type_def, lowered_value_type_def] >>
  impl_tac
  >- (fs[] >> fs[compileEnvTheory.type_memory_bytes_def,
        vyperValueTheory.type_slot_size_def, vfmConstantsTheory.word_size_def]) >>
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
   sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def, cs_extends_def] >>
  `MAP FDOM (raw with gas_obs := []).scopes =
   MAP FDOM (raw' with gas_obs := []).scopes` by
    metis_tac[exprBopSimPropsTheory.bop_marked_scopes_dom] >>
  `MAP FDOM es.scopes = MAP FDOM (raw with gas_obs := []).scopes` by
    simp[exprBopSimPropsTheory.bop_marked_scopes_dom,
      vyperStateTheory.evaluation_state_accfupds] >>
  `~expr_has_effect (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [a];start;len]) ==>
   ~expr_has_effect start /\ ~expr_has_effect len` by simp[] >>
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ PB /\ _` >>
  `PB` by simp[Abbr`PB`, contextTheory.mk_ptr_def] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule code_slice_external_post_rebase >>
  qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept _ (raw with gas_obs := []) _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept _ (raw' with gas_obs := []) _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ (raw' with gas_obs := []) _ _ _ _ _ _ _`
    (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise code_slice_external_vv_ptr

(* The public value judgment uses the same inherited unwrap interface as
   the self-code case; operand readiness remains conditional on tail success. *)
Theorem body_code_slice_external_ptr:
  !cx ty n ct a start len.
    ~is_self_code (Builtin ct (Acc Code) [a]) /\
    body_exprs_ptr_ok cx [start;len] /\
    (!s vs t. eval_exprs cx [start;len] s = (INL vs,t) ==>
      body_exprs_ptr_ok cx [a]) ==>
    body_expr_ptr_ok cx (Builtin ty (Slice n)
      [Builtin ct (Acc Code) [a];start;len])
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_ptr_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_vv_sim_ptr d ctx PG func cenv cx ty'
        (Builtin ty (Slice n) [Builtin ct (Acc Code) [a];start;len]) es` by
        metis_tac[code_slice_external_vv_ptr] >>
      conj_tac >- metis_tac[expr_sim_ptr_of_vv] >>
      first_assum ACCEPT_TAC) >>
  simp[]
QED
