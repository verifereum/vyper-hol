(* Compose the ordinary linked Slice route at the reached operand cuts. *)
Theory bodySliceOrdinaryRouteMods
Ancestors
  bodySliceOrdinaryReadMods bodySliceOrdinaryOperandPreMods
  bodySliceOrdinaryCapturedWordsMods bodySliceOrdinarySourceBindMods
  bodySliceOrdinaryDynamicContinuationMods bodySliceOrdinaryFixedContinuationMods
  bodySliceOrdinaryDynamicLayoutMods bodySliceOrdinaryFixedLayoutMods
  bodyFullIfExpReach bodyForcedStorageFrameMods exprBodyPreProps exprSimWordArgs
  exprSimFullBundleProps exprSimSliceSource bodyFullPredsMods vyperStorageTrace
  bodyFullPostsMods compileEnv loweringPosts exprLoweringProps
  vyperTypeExprSoundness vyperValue vyperTyping
Libs monadsyntax

val W = fst (dest_conj (fst (dest_imp (concl
  bodySliceOrdinaryTerminalOutcomeModsTheory.slice_ordinary_terminal_outcome_mods))));
val finish = ``\v v1 v2. do
  acc <- get_accounts;
  r <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                  (MAP expr_type [src;start;len]) [v;v1;v2]);
  return (Value r)
  od``;
val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val next = ``\v. bind (^forced start) (\v1. bind (^forced len) (^finish v v1))``;
val E = ``Builtin ann (Slice n) args``;

Triviality slice_return_bind:
  bind (return v) k = k v
Proof
  simp[FUN_EQ_THM,vyperStateTheory.bind_def,vyperStateTheory.return_def]
QED

Triviality ordinary_slice_bind_action:
  code_slice_source (Slice n) [src;start;len] = NONE ==>
  eval_expr cx (Builtin ann (Slice n) [src;start;len]) = bind (^forced src) ^next
Proof
  disch_then (pure_once_rewrite_tac o single o MATCH_MP slice_eval_ordinary) >>
  BETA_TAC >> simp[eval_exprs_cons_action,vyperStateTheory.bind_assoc] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,vyperStateTheory.return_def,eval_exprs_nil] >>
  simp[vyperStateTheory.bind_assoc,slice_return_bind]
QED

Triviality slice_capture_value_kind:
  ((ann = BaseT (BytesT (Dynamic n)) /\ (?bd. expr_type src = BaseT (BytesT bd))) \/
   (ann = BaseT (StringT n) /\ (?m. expr_type src = BaseT (StringT m)))) /\
  is_bytestring_type (expr_type src) /\ value_runtime_typed env (expr_type src) v /\
  (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) ==>
  ?bd. (ann = BaseT (BytesT (Dynamic n)) /\ expr_type src = BaseT (BytesT bd) /\ v = BytesV bs) \/
       (?m str. ann = BaseT (StringT n) /\ expr_type src = BaseT (StringT m) /\
                v = StringV str /\ bs = MAP (n2w o ORD) str)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `(ann = _ /\ _) \/ (ann = _ /\ _)` strip_assume_tac
  >- (qexists_tac `bd` >> asm_rewrite_tac[] >> disj1_tac >>
      qpat_assum `v = BytesV bs \/ _` strip_assume_tac >>
      Cases_on `bd` >> gvs[is_bytestring_type_def,value_runtime_typed_def,evaluate_type_def,value_has_type_def]) >>
  qexists_tac `Dynamic 0` >> disj2_tac >> qexists_tac `m` >> asm_rewrite_tac[] >>
  qpat_assum `v = BytesV bs \/ _` strip_assume_tac >>
  gvs[value_runtime_typed_def,evaluate_type_def,value_has_type_def]
QED

Theorem slice_ordinary_from_cuts_mods:
  !mods exps DF lo d ctx shadow_ctx PG func shadow_func cenv cx env msrc tops ty ann n args es.
    ^W /\
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok_mods mods exps cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok_mods mods exps cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok_mods mods exps cx [addr])) /\
    code_slice_source (Slice n) args = NONE /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods msrc tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env ^E es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es /\ expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`src`,`start`,`len`] (map_every assume_tac o CONJUNCTS))
    slice_ordinary_operands_pre_mods >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  conj_asm2_tac
  >- (irule slice_ordinary_read_from_vv_mods >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  `expr_sim_inv_mods mods cenv cx env es` by (drule expr_body_pre_mods_inv >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env src es` by
    (qpat_assum `!e mid. _ ==> expr_body_pre_mods _ _ _ _ e mid` irule >> simp[]) >>
  pure_rewrite_tac[expr_vv_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`vv`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> qexists_tac `func` >> simp[]) >>
  qpat_assum `code_slice_source _ _ = NONE` (fn th =>
    let val eq = BETA_RULE (MATCH_MP ordinary_slice_bind_action th)
    in PURE_ONCE_REWRITE_TAC [eq] >>
       qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
         (assume_tac o PURE_ONCE_REWRITE_RULE [eq])
    end) >>
  Cases_on `is_bytestring_type (expr_type src)` >>
  (drule_all_then (qx_choosel_then
     [`op0`,`sm`,`limit`,`data`,`sc`,`x`,`sd`,`y`,`se`,`out`,`shm`,`shc`,`shd`,`she`]
     (map_every assume_tac o CONJUNCTS)) slice_ordinary_dynamic_layout_mods ORELSE
   (`?m. expr_type src = BaseT (BytesT (Fixed m))` by
      (qpat_assum `(ann = _ /\ _) \/ (ann = _ /\ _)` strip_assume_tac
       >- (Cases_on `bd` >> fs[is_bytestring_type_def] >> metis_tac[]) >>
       fs[is_bytestring_type_def]) >>
    drule_all_then (qx_choosel_then
      [`op0`,`sm`,`buf`,`stage`,`sc`,`x`,`sd`,`y`,`se`,`out`,`shm`,`shstage`,`shc`,`shd`,`she`]
      (map_every assume_tac o CONJUNCTS)) slice_ordinary_fixed_layout_mods)) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
     `is_bytestring_type (expr_type src) \/ (?m. expr_type src = BaseT (BytesT (Fixed m)))`
   >- ((disj1_tac >> first_assum ACCEPT_TAC) ORELSE
       (disj2_tac >> qexists_tac `m` >> first_assum ACCEPT_TAC))) >>
  qpat_assum `vv = LocatedValue _ _` (PURE_ONCE_REWRITE_TAC o single) >>
  irule (BETA_RULE (Q.INST [`next` |-> `^next`] slice_ordinary_source_bind_mods)) >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[]) >>
  (conj_tac
   >- simp[storage_trace_frame_bind_all,storage_trace_frame_state_reads,
           storage_trace_frame_lifts,storage_trace_frame_return,
           bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`op0`,`sa`,`sha`,`shadow_func`,`shm`,`sm`,`msrc`,`tops`,`expr_type src`] >>
  qpat_assum `ci_mono sa sm` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  asm_rewrite_tac[expr_sim_full_code_def] >>
  qx_genl_tac [`marks`,`v`,`ec`,`Gm`,`tm`,`sms`] >>
  disch_then strip_assume_tac >>
  qpat_x_assum `is_bytestring_type (expr_type src) \/ (?m. expr_type src = BaseT (BytesT (Fixed m)))` kall_tac >>
  qpat_assum `ci_mono sm sc` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `ci_mono sc sd` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `ci_mono sd se` (strip_assume_tac o REWRITE_RULE [ci_mono_def])
  >- suspend "dynamic_layout" >>
  suspend "fixed_layout"
QED

Resume slice_ordinary_from_cuts_mods[dynamic_layout]:
  `?bt. expr_type src = BaseT bt` by
    (qpat_assum `(ann = _ /\ _) \/ (ann = _ /\ _)` strip_assume_tac >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ec.storage_trace ==>
      expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op0 sms /\
      ptr_val_ok cx (post_value_type cenv src) v op0 Gm tm sms` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     asm_rewrite_tac[]) >>
  mp_tac (BETA_RULE (Q.INST [`op` |-> `op0`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    slice_ordinary_dynamic_continuation_mods)) >>
  (impl_tac >- (asm_rewrite_tac[] >>
     qpat_assum `expr_type src = BaseT bt` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`scs`,`Gc`,`tc`,`lp`,`root`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (qx_choose_then `bd` assume_tac) slice_capture_value_kind >>
  mp_tac (slice_ordinary_captured_words_reached_mods
    |> Q.INST [`obs0` |-> `gas_explicit marks s0.vs_gas_readings`,
               `ty1` |-> `ty`, `ty2` |-> `ty`]
    |> BETA_RULE |> REWRITE_RULE [LET_THM] |> BETA_RULE) >>
  (impl_tac >- (
    rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ expr_store_bound _ _ _ _ _ /\ _`
          (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- (irule EQ_SYM >> first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
    >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- simp[]
    >- simp[]
    >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!H sd se start len e1 e2 v1 v2 op1 op2 sds ses Gd Ge td te env1. _ ==> mem_bytes_at _ _ _ = _ /\ _`
          (drule_all_then ACCEPT_TAC))
    >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!e mid. MEM e [src;start;len] /\ _ ==> expr_body_pre_mods _ _ _ _ _ _` irule >>
        fs[listTheory.MEM]) >>
    rewrite_tac[expr_sim_full_code_def] >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
    qpat_assum `data = Var root` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
Resume slice_ordinary_from_cuts_mods[fixed_layout]:
  `!H. valid_horizon cx st0 H ec.storage_trace ==>
      expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op0 sms /\
      ptr_val_ok cx (expr_type src) v op0 Gm tm sms` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     `post_value_type cenv src = expr_type src` by asm_rewrite_tac[] >>
     qpat_assum `post_value_type cenv src = expr_type src` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (BETA_RULE (Q.INST [`op` |-> `op0`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    slice_ordinary_fixed_continuation_mods)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`scs`,`Gc`,`tc`,`root`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ann = BaseT (BytesT (Dynamic n))` by
    (qpat_assum `(ann = _ /\ _) \/ (ann = _ /\ _)` strip_assume_tac >> fs[]) >>
  mp_tac (slice_ordinary_captured_words_mods
    |> Q.INST [`obs0` |-> `gas_explicit marks s0.vs_gas_readings`,
               `bd` |-> `Fixed m`, `limit` |-> `Lit (n2w m)`,
               `ty1` |-> `ty`, `ty2` |-> `ty`]
    |> BETA_RULE |> REWRITE_RULE [LET_THM] |> BETA_RULE) >>
  (impl_tac >- (
    rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
    >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- (qpat_assum `expr_type src = BaseT (BytesT (Fixed m))` SUBST1_TAC >> first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ expr_store_bound _ _ _ _ _ /\ _`
          (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- (irule EQ_SYM >> first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
    >- (disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- simp[]
    >- simp[]
    >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!H sd se start len e1 e2 v1 v2 op1 op2 sds ses Gd Ge td te. _ ==> mem_bytes_at _ _ _ = _ /\ _`
          (drule_all_then ACCEPT_TAC))
    >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!e mid. MEM e [src;start;len] /\ _ ==> expr_body_pre_mods _ _ _ _ _ _` irule >>
        fs[listTheory.MEM]) >>
    rewrite_tac[expr_sim_full_code_def] >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
    qpat_assum `buf.buf_operand = Var root` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
Finalise slice_ordinary_from_cuts_mods
