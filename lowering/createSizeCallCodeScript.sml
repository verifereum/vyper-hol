(* Caller-code ownership for non-CREATE calls and ABI argument staging. *)
Theory createSizeCallCode
Ancestors
  createSizeCutOpens createSizeCutCode exprLowering exprCallBounds builtinSystem
  builtinSimple compileEnv context emitHelper venomInst vyperAST pair list option
  pred_set
Libs
  monadsyntax

Theorem call_cut_option[local]:
  create_cut_code exits a (SND p) /\
  (!x. create_cut_code exits a (SND (k x))) ==>
  create_cut_code exits a (SND (option_CASE v p k))
Proof
  Cases_on `v` >> simp[]
QED

Theorem call_cut_result_snd[local,simp]:
  SND (UNCURRY (\x a. if c then (f x,a) else (g x,a)) p) = SND p /\
  SND (UNCURRY (\x a. (h x,a)) p) = SND p
Proof
  Cases_on `p` >> Cases_on `c` >> simp[]
QED

(* Keep the wrapped callbacks opaque when certifying their consumers. *)
fun call_cut_steps_with extra ths =
  rpt (FIRST ([CHANGED_TAC (simp (ths @ [Excl "expr_child_callback_def",
                     create_cut_code_emit_inst, create_cut_code_emit_op,
                     create_cut_code_emit_void, create_cut_code_emit_multi_op,
                     create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind] @
              extra @ [conj_tac, gen_tac, IF_CASES_TAC]));

val call_cut_steps = call_cut_steps_with [];
val call_pair_steps = call_cut_steps_with
  [irule create_cut_code_pair, irule call_cut_option,
   CONV_TAC (RAND_CONV (RAND_CONV (FIRST_CONV
     [REWR_CONV UNCURRY_VAR, RATOR_CONV (REWR_CONV UNCURRY_VAR)])))];

Theorem create_ext_call_args_case:
  (!ty e a. expr_size e + cenv_defaults_size ce < bound ==>
      create_cut_code {} a (SND (f ce ty e a))) /\
  (!mutates vv a. create_cut_code {} a (SND (compile_snapshot_vv ce mutates vv a))) ==>
  !es tys a. create_cut_code {} a
    (SND (compile_ext_call_args (expr_child_callback bound f) ce kw tys es a))
Proof
  strip_tac >>
  `!ty e a. create_cut_code {} a (SND (expr_child_callback bound f ce ty e a))` by
    (rpt gen_tac >> irule create_cut_guarded_expr >> simp[]) >>
  Induct >> gen_tac >> Cases_on `tys` >> gen_tac >>
  call_cut_steps [compile_ext_call_args_def]
QED

val _ = augment_srw_ss [rewrites [create_alloc_buffer_cut_code]];

Theorem call_cut_materialize[local]:
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!v dst dt st a. create_cut_code {} a
      (SND (compile_store_memory ce v dst dt st a))) ==>
  !ty vv a. create_cut_code {} a (SND (compile_materialize_vv ce ty vv a))
Proof
  rpt strip_tac >> call_cut_steps [compile_materialize_vv_def]
QED

Theorem call_cut_kwarg[local]:
  (!ty e a. create_cut_code {} a (SND (f ce ty e a))) /\
  (!ty e a. create_cut_code {} a (SND (lower_value f ce ty e a))) /\
  (!ty vv a. create_cut_code {} a (SND (compile_materialize_vv ce ty vv a))) ==>
  !k e a. create_cut_code {} a (SND (compile_ext_call_kwarg f ce rt k e a))
Proof
  rpt strip_tac >> call_cut_steps [compile_ext_call_kwarg_def, LET_DEF]
QED

Theorem call_cut_kwargs[local]:
  (!k e a. create_cut_code {} a (SND (compile_ext_call_kwarg f ce rt k e a))) ==>
  !ks es a. create_cut_code {} a (SND (compile_ext_call_kwargs f ce rt ks es a))
Proof
  strip_tac >> Induct >> Cases_on `es` >> gen_tac >>
  call_cut_steps [compile_ext_call_kwargs_def, UNCURRY_VAR]
QED

Theorem call_cut_stage_intcall[local]:
  (!ty e a. create_cut_code {} a (SND (f ce ty e a))) /\
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!v dst dt st a. create_cut_code {} a
      (SND (compile_store_memory ce v dst dt st a))) ==>
  !es flags tys a. create_cut_code {} a
    (SND (compile_stage_intcall_args f ce es flags tys a))
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `flags` >> Cases_on `tys` >>
  TRY (rename1 `(flag:bool)::flags` >> Cases_on `flag`) >>
  call_cut_steps [compile_stage_intcall_args_def, LET_DEF,
    compile_store_bytestring_def, compile_bytestring_copy_len_def]
QED

Theorem call_cut_store_multi[local,simp]:
  !ops off a. create_cut_code {} a (SND (store_multi_results buf ops off a))
Proof
  Induct >> rpt gen_tac >> call_cut_steps [store_multi_results_def]
QED

Theorem call_cut_raw_outbuf[local,simp]:
  create_cut_code {} a (SND (compile_raw_call_outbuf n a))
Proof
  call_cut_steps [compile_raw_call_outbuf_def, LET_DEF]
QED

Theorem call_cut_msg_data[local,simp]:
  create_cut_code {} a (SND (compile_msg_data_to_memory a))
Proof
  call_cut_steps [compile_msg_data_to_memory_def, compile_alloc_dynamic_def]
QED

Theorem call_cut_raw_revert[local,simp]:
  create_cut_code {} a (SND (compile_raw_revert op a))
Proof
  call_cut_steps [compile_raw_revert_def]
QED

Theorem call_cut_revert_arms[local]:
  (!a. create_cut_code {} a (SND ((fail_action : unit compiler) a))) /\
  (!a. create_cut_code {} a (SND (k a))) ==>
  create_cut_code {} a (SND ((do
    emit_inst JNZ [cond; Label ok; Label fail_lbl] [];
    new_block fail_lbl;
    fail_action;
    new_block ok;
    k
  od) a))
Proof
  strip_tac >> simp[comp_ignore_bind_def, comp_bind_def, UNCURRY_VAR] >>
  qabbrev_tac `a1 = SND (emit_inst JNZ [cond; Label ok; Label fail_lbl] [] a)` >>
  qabbrev_tac `a2 = SND (new_block fail_lbl a1)` >>
  qabbrev_tac `a3 = SND (fail_action a2)` >>
  qabbrev_tac `a4 = SND (new_block ok a3)` >>
  qabbrev_tac `pending = {ok;fail_lbl}` >>
  `create_cut_code pending a a1` by
    simp[Abbr `a1`, Abbr `pending`, create_cut_code_emit_inst,
         create_cut_targets_def, DISJ_IMP_THM] >>
  `create_cut_code pending a1 a2 /\ {fail_lbl} SUBSET set (added_labels a1 a2)` by
    (simp[Abbr `a2`] >> Cases_on `new_block fail_lbl a1` >>
     gvs[] >> drule externalEntryShapeTheory.added_labels_new_block >> simp[]) >>
  `create_cut_code pending a2 a3` by
    (irule create_cut_code_weaken >> qexists_tac `{}` >> simp[Abbr `a3`]) >>
  `create_cut_code pending a3 a4 /\ {ok} SUBSET set (added_labels a3 a4)` by
    (simp[Abbr `a4`] >> Cases_on `new_block ok a3` >>
     gvs[] >> drule externalEntryShapeTheory.added_labels_new_block >> simp[]) >>
  `create_cut_code pending a a2 /\ {fail_lbl} SUBSET set (added_labels a a2)` by
    (match_mp_tac (SIMP_RULE bool_ss [UNION_EMPTY]
       (Q.INST [`opened1` |-> `{}`] create_cut_opens_join)) >>
     qexists_tac `a1` >> simp[]) >>
  `create_cut_code pending a a3 /\ {fail_lbl} SUBSET set (added_labels a a3)` by
    (match_mp_tac (SIMP_RULE bool_ss [UNION_EMPTY]
       (Q.INST [`opened2` |-> `{}`] create_cut_opens_join)) >>
     qexists_tac `a2` >> simp[]) >>
  `create_cut_code pending a a4 /\ ({fail_lbl} UNION {ok}) SUBSET set (added_labels a a4)` by
    (match_mp_tac create_cut_opens_join >> qexists_tac `a3` >> simp[]) >>
  `create_cut_code {} a a4` by
    (irule create_cut_opens_close >>
     qexistsl_tac [`{fail_lbl} UNION {ok}`, `pending`] >> simp[Abbr `pending`]) >>
  metis_tac[create_cut_code_join]
QED

Theorem call_cut_raw_reverting[local,simp]:
  create_cut_code {} a (SND ((do
    fail_lbl <- fresh_label "call_failed";
    ok_lbl <- fresh_label "call_ok";
    emit_inst JNZ [success; Label ok_lbl; Label fail_lbl] [];
    new_block fail_lbl;
    rds <- emit_op RETURNDATASIZE [];
    rbuf <- compile_alloc_buffer 0;
    emit_void RETURNDATACOPY [rbuf.buf_operand; Lit 0w; rds];
    emit_inst REVERT [rbuf.buf_operand; rds] [];
    new_block ok_lbl;
    if n > 0 then
      do rds2 <- emit_op RETURNDATASIZE [];
         cmp <- emit_op LT [rds2; Lit (n2w n)];
         capped <- compile_select cmp rds2 (Lit (n2w n));
         emit_void MSTORE [ov; capped];
         comp_return ov od
    else comp_return (Lit 0w)
  od) a))
Proof
  irule create_cut_code_bind >> (conj_tac >- simp[]) >> BETA_TAC >>
  irule create_cut_code_bind >> (conj_tac >- simp[]) >> BETA_TAC >>
  pure_rewrite_tac[comp_ignore_bind_def] >>
  irule (SIMP_RULE bool_ss [comp_ignore_bind_def, comp_bind_assoc, BETA_THM]
      (Q.INST [`fail_action` |-> `do rds <- emit_op RETURNDATASIZE [];
          rbuf <- compile_alloc_buffer 0;
          emit_void RETURNDATACOPY [rbuf.buf_operand; Lit 0w; rds];
          emit_inst REVERT [rbuf.buf_operand; rds] [] od`]
         call_cut_revert_arms)) >>
  call_cut_steps [compile_select_def]
QED

Theorem call_cut_raw_finish[simp]:
  create_cut_code {} a (SND (compile_raw_call_finish addr data_ptr data_len gas_op value_op
                                      call_ty n rof ov optr a))
Proof
  Cases_on `call_ty` >> simp[compile_raw_call_finish_def, LET_DEF] >>
  irule create_cut_code_bind >>
  (conj_tac >- simp[create_cut_code_emit_op, create_cut_targets_def]) >>
  Cases_on `rof` >> simp[]
  >- call_cut_steps [compile_select_def]
  >- call_cut_steps [compile_select_def]
  >> call_cut_steps [compile_select_def]
QED

Theorem call_arg_cases[local]:
  !args. args = [] \/ (?x. args = [x]) \/ (?x y. args = [x;y]) \/
         (?x y z. args = [x;y;z]) \/ (?x y z u us. args = x::y::z::u::us)
Proof
  Cases >> simp[] >>
  rename1 `xs = [] \/ _` >> Cases_on `xs` >> simp[] >>
  rename1 `xs = [] \/ _` >> Cases_on `xs` >> simp[] >>
  rename1 `xs = [] \/ _` >> Cases_on `xs` >> simp[]
QED

Theorem create_noncreate_call_case:
  bound = expr_size (Call ann target args d) + cenv_defaults_size ce /\
  (!ce' ty' e' a. expr_size e' + cenv_defaults_size ce' < bound ==>
    create_cut_code {} a (SND (f ce' ty' e' a))) /\
  (!ck hs rof ks. target <> CreateTarget ck hs rof ks) /\
  (!ce' vv a. create_cut_code {} a (SND (unwrap_value ce' vv a))) /\
  (!ce' v dst dt sty a. create_cut_code {} a
    (SND (compile_store_memory ce' v dst dt sty a))) /\
  (!mutates vv a. create_cut_code {} a (SND (compile_snapshot_vv ce mutates vv a))) /\
  (!addr vals tys args_size method_id ret_size min_size mem_bytes
    is_static value_op gas_op skip_check has_default default_op rt dt dec a.
      create_cut_code {} a
        (SND (compile_external_call_kwargs ce addr vals tys args_size method_id
          ret_size min_size mem_bytes is_static value_op gas_op skip_check
          has_default default_op rt dt dec a))) ==>
  create_cut_code {} a
    (SND (compile_call (expr_child_callback bound f) ce ret_ty ty target args d a))
Proof
  strip_tac >>
  `!ce' ty' e' s. create_cut_code {} s (SND (expr_child_callback bound f ce' ty' e' s))` by
    (rpt gen_tac >> irule create_cut_guarded_expr >> simp[]) >>
  `!kw es tys s. create_cut_code {} s
     (SND (compile_ext_call_args (expr_child_callback bound f) ce kw tys es s))` by
    (rpt gen_tac >> irule create_ext_call_args_case >> simp[]) >>
  qabbrev_tac `child = expr_child_callback bound f` >>
  `!ce' es flags tys s. create_cut_code {} s
     (SND (compile_stage_intcall_args child ce' es flags tys s))` by
    (rpt gen_tac >> irule call_cut_stage_intcall >> simp[]) >>
  `!ty e s. create_cut_code {} s (SND (lower_value child ce ty e s))` by
    (rpt gen_tac >> call_cut_steps [lower_value_def]) >>
  `!es s. create_cut_code {} s (SND (compile_multi_exprs child ce es s))` by
    (Induct >> gen_tac >> call_cut_steps [compile_multi_exprs_def, LET_DEF]) >>
  `!ty vv s. create_cut_code {} s (SND (compile_materialize_vv ce ty vv s))` by
    (rpt gen_tac >> irule call_cut_materialize >> simp[]) >>
  `!rt k e s. create_cut_code {} s (SND (compile_ext_call_kwarg child ce rt k e s))` by
    (rpt gen_tac >> irule call_cut_kwarg >> simp[]) >>
  `!rt ks es s. create_cut_code {} s (SND (compile_ext_call_kwargs child ce rt ks es s))` by
    (rpt gen_tac >> irule call_cut_kwargs >> simp[]) >>
  qpat_x_assum `bound = _` kall_tac >>
  qpat_x_assum `Abbrev (child = _)` kall_tac >>
  qpat_x_assum `!ce' ty' e' a. _ < bound ==> _` kall_tac >>
  qpat_x_assum `!ce' ty' e' s. create_cut_code {} s (SND (child ce' ty' e' s))` kall_tac >>
  qpat_x_assum `!rt k e s. create_cut_code {} s (SND (compile_ext_call_kwarg _ _ _ _ _ _))` kall_tac >>
  qpat_x_assum `!ty vv s. create_cut_code {} s (SND (compile_materialize_vv _ _ _ _))` kall_tac >>
  qpat_x_assum `!mutates vv a. create_cut_code {} a (SND (compile_snapshot_vv _ _ _ _))` kall_tac >>
  qpat_x_assum `!ce' vv a. create_cut_code {} a (SND (unwrap_value _ _ _))` kall_tac >>
  qpat_x_assum `!ce' v dst dt sty a. create_cut_code {} a (SND (compile_store_memory _ _ _ _ _ _))` kall_tac >>
  Cases_on `target` >> fs[compile_call_def]
  >~ [`ce.ce_func_info _`] >-
    (qabbrev_tac `info = ce.ce_func_info (nsid_to_string p)` >>
     PairCases_on `info` >> simp[] >> call_pair_steps [])
  >~ [`compile_call _ _ _ _ (ExtCall _ _ _ _) _ _ _`] >-
    (rename1 `create_cut_code {} _ (SND (compile_call _ _ _ _ (ExtCall _ _ siginfo _) _ _ _))` >>
     PairCases_on `siginfo` >> Cases_on `args` >>
     call_pair_steps [compile_call_def])
  >> qspec_then `args` strip_assume_tac call_arg_cases
  >> qpat_x_assum `args = _` SUBST_ALL_TAC
  >> simp[compile_selfdestruct_def, create_cut_code_emit_inst, create_cut_targets_def]
  (* Keep the generated arity cases in separate proof steps at the default
     tactic limit. The same pair-composition rules apply to each case. *)
  >- call_pair_steps []
  >- call_pair_steps []
  >- call_pair_steps []
  >- call_pair_steps []
  >- call_pair_steps []
  >- call_pair_steps []
  >- call_pair_steps []
  >> call_pair_steps []
QED
