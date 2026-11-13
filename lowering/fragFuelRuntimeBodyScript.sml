(*
 * Fuel bounds for the runtime's external entry code: the entry checks,
 * argument decoding, guarded, external, fallback and common bodies, the
 * kwarg initialisation, and the list of external function bodies.
 *
 * The bodies run under cenv_ptrs_below for the environment with the
 * decoded arguments, whose pointer variables are the ALLOCA outputs the
 * entry code emits before the body (or the kwarg buffers allocated during
 * dispatch).  The packaged environments themselves hold no pointer
 * variables (cenv_ptrs_below 0) and no constructor exit label.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_entry_checks, fuel_ok_compile_decode_args,
 *   fuel_ok_compile_register_positional_args,
 *   fuel_okS_compile_guarded_body, fuel_okS_compile_external_function_body,
 *   fuel_okS_compile_fallback_body, fuel_okS_compile_external_fn_bodies,
 *   fuel_ok_compile_init_kwargs, fuel_ok_compile_create_kwarg_allocas,
 *   compile_create_kwarg_allocas_ptrs, compile_register_kwarg_vars_ptrs,
 *   fuel_okS_compile_common_function_body,
 *   fuel_ok_next, compile_alloc_buffer_var
 *)

Theory fragFuelRuntimeBody
Ancestors
  fragFuel fragFuelStmtBase fragFuelStmtGlue fragFuelContextBase
  fragFuelContext fragFuelAbi fragFuelExprHelpers fragFuelExprCfn
  moduleLowering stmtLowering compileEnv emitHelper context venomInst
  finite_map list pred_set option
Libs
  fragFuelLib

val hstmts = ``!cenv' lctx ty ss Wv E.
    cenv_ptrs_in Wv cenv' /\ stmt_exits_in E cenv' lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv {} E
      (compile_stmts cenv' lctx ty ss)``

val hexpr = ``!c t e Wv E. fuel_ok Wv {} E (compile_expr c t e)``

(* ===== Helpers ===== *)

Theorem fuel_ok_next:
  !Wv L E m st x st'.
    fuel_ok Wv L E m /\ m st = (x, st') ==> st.cs_next_var <= st'.cs_next_var
Proof
  metis_tac[fuel_ok_def]
QED

Theorem compile_alloc_buffer_var:
  !n st b st'.
    compile_alloc_buffer n st = (b, st') ==>
    st.cs_next_var <= st'.cs_next_var /\
    !x. b.buf_operand = Var x ==> var_below st'.cs_next_var x
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac emit_op_next >> imp_res_tac emit_op_var >> simp[]
QED

(* m starts under P; the rest runs under Q of m's result. *)
Theorem fuel_okS_bind_dep[local]:
  !P Q m f Wv E.
    fuel_okS P Wv {} E m /\
    (!st x st'. P st /\ m st = (x, st') ==> Q x st') /\
    (!a. fuel_okS (Q a) Wv {} E (f a)) ==>
    fuel_okS P Wv {} E (comp_bind m f)
Proof
  rpt strip_tac >>
  `fuel_okS P Wv ({} UNION {}) E (comp_bind m f)` suffices_by simp[] >>
  match_mp_tac (Q.SPECL [`P`, `Q`, `m`, `f`, `Wv`, `{}`, `{}`, `E`, `E`, `E`]
                  fuel_okS_bind) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Theorem fuel_okS_pre_conj[local]:
  !b P Wv L E m.
    (b ==> fuel_okS P Wv L E m) ==> fuel_okS (\st. P st /\ b) Wv L E m
Proof
  Cases_on `b` >> simp[fuel_okS_def] >> metis_tac[]
QED

val ok_tac = match_mp_tac fuel_okS_of_ok

val keep_tac =
  match_mp_tac fuel_okS_ignore_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_cenv_ptrs_below

(* ===== Entry checks and argument decoding ===== *)

Theorem fuel_ok_compile_entry_checks:
  !n p Wv E. fuel_ok Wv {} E (compile_entry_checks n p)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_entry_checks_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_decode_args:
  !args cenv off load_opc hi_op base_adj Wv E.
    ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE ==>
    fuel_ok Wv {} E (compile_decode_args cenv args off load_opc hi_op base_adj)
Proof
  Induct >- simp[compile_decode_args_def, fuel_ok_return] >>
  PairCases >> rpt strip_tac >>
  `!off. fuel_ok Wv {} E
           (compile_decode_args cenv args off load_opc hi_op base_adj)` by
    (gen_tac >> first_x_assum irule >> simp[]) >>
  PURE_ONCE_REWRITE_TAC [compile_decode_args_def] >>
  PURE_REWRITE_TAC [compile_abi_arg_ptr_guard_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp_tac std_ss [option_case_def] >>
  TRY (rename1 `FLOOKUP _ _ = SOME loc` >>
       Cases_on `var_location_decode_operand loc` >>
       simp_tac std_ss [option_case_def]) >>
  fuel_auto [fuel_ok_return, fuel_ok_emit_op, fuel_ok_emit_void,
             fuel_ok_compile_abi_clamp_basetype,
             fuel_ok_compile_abi_decode_to_buf] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_decode_calldata[local]:
  !cenv args off hi adj Wv E.
    fuel_ok Wv {} E (compile_decode_args cenv args off CALLDATALOAD hi adj)
Proof
  rpt gen_tac >> irule fuel_ok_compile_decode_args >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_register_positional_args:
  !args cenv off Wv E.
    fuel_ok Wv {} E (compile_register_positional_args cenv args off)
Proof
  Induct >- simp[compile_register_positional_args_def, fuel_ok_return] >>
  PairCases >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp_tac std_ss [option_case_def] >>
  TRY (rename1 `FLOOKUP _ _ = SOME loc` >>
       Cases_on `var_location_memory_size loc` >>
       simp_tac std_ss [option_case_def]) >>
  fuel_auto [fuel_ok_return, fuel_ok_compile_alloc_buffer, fuel_ok_decode_calldata]
QED

(* The decoded arguments' buffers are allocated by the end. *)
Theorem compile_register_positional_args_ptrs[local]:
  !args cenv off st c st'.
    compile_register_positional_args cenv args off st = (c, st') /\
    cenv_ptrs_below st.cs_next_var cenv ==>
    cenv_ptrs_below st'.cs_next_var c /\
    c.ce_ctor_exit_label = cenv.ce_ctor_exit_label
Proof
  Induct
  >- (rw[compile_register_positional_args_def, comp_return_def] >> fs[]) >>
  PairCases >> rpt gen_tac >>
  simp[Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer _ st = (buf, s1)` >>
  rename1 `compile_decode_args _ _ _ _ _ _ s1 = (u, s2)` >>
  drule compile_alloc_buffer_var >> strip_tac >>
  `s1.cs_next_var <= s2.cs_next_var` by
    metis_tac[fuel_ok_next, fuel_ok_decode_calldata] >>
  first_x_assum drule >> impl_tac
  >- (match_mp_tac cenv_ptrs_below_update >>
      qexists_tac `st.cs_next_var` >> rpt conj_tac >> simp[] >>
      metis_tac[var_below_le]) >>
  simp[]
QED

(* ===== Bodies ===== *)

Theorem fuel_okS_compile_guarded_body:
  !cenv nr nkey ut iv stmts rt.
    cenv.ce_ctor_exit_label = NONE /\ ^hstmts ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) UNIV {} {}
      (compile_guarded_body cenv nr nkey ut iv stmts rt)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `rt` >>
  simp_tac std_ss [compile_guarded_body_def, option_case_def] >>
  (keep_tac >- (ok_tac >> fuel_auto [fuel_ok_context_storage])) >>
  (keep_tac
   >- (first_assum irule >> simp[cenv_ptrs_in_def, stmt_exits_in_def])) >>
  ok_tac >> fuel_auto [fuel_ok_context_storage, fuel_ok_emit_inst_any] >>
  simp[]
QED

Theorem fuel_okS_compile_external_function_body:
  !cenv args nr nkey ut iv stmts rt.
    cenv.ce_ctor_exit_label = NONE /\ ^hstmts ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) UNIV {} {}
      (compile_external_function_body cenv args nr nkey ut iv stmts rt)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [compile_external_function_body_def] >>
  match_mp_tac fuel_okS_bind_dep >>
  qexists_tac `\c st. cenv_ptrs_below st.cs_next_var c /\
                      c.ce_ctor_exit_label = NONE` >>
  rpt conj_tac
  >- (ok_tac >> MATCH_ACCEPT_TAC fuel_ok_compile_register_positional_args)
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      drule_all compile_register_positional_args_ptrs >> simp[]) >>
  qx_gen_tac `c` >> BETA_TAC >>
  ho_match_mp_tac fuel_okS_pre_conj >> strip_tac >>
  match_mp_tac fuel_okS_compile_guarded_body >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem fuel_okS_compile_fallback_body:
  !cenv p nr nkey ut iv stmts rt.
    cenv.ce_ctor_exit_label = NONE /\ ^hstmts ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) UNIV {} {}
      (compile_fallback_body cenv p nr nkey ut iv stmts rt)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [compile_fallback_body_def] >>
  (keep_tac
   >- (ok_tac >> fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >>
       simp[is_terminator_def])) >>
  match_mp_tac fuel_okS_compile_guarded_body >>
  conj_tac >> first_assum ACCEPT_TAC
QED

fun sq lm lf tac =
  match_mp_tac fuel_okS_seqQ >> qexistsl_tac [lm, lf, `\st. T`] >>
  rpt conj_tac
  >- simp[next_stable_def]
  >- simp[]
  >- simp[SUBSET_DEF]
  >- tac

val nb_tac = ok_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block

(* Every external function's code starts with the block of its entry
   label. *)
Theorem fuel_okS_compile_external_fn_bodies:
  ^hstmts ==>
  !fns.
    EVERY (\f. cenv_ptrs_below 0 (FST (SND f)) /\
               (FST (SND f)).ce_ctor_exit_label = NONE) fns ==>
    fuel_okS (\st. T) UNIV (set (MAP FST fns)) {}
      (compile_external_fn_bodies fns)
Proof
  strip_tac >> Induct
  >- (simp[compile_external_fn_bodies_def] >> ok_tac >>
      MATCH_ACCEPT_TAC fuel_ok_return) >>
  PairCases >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [compile_external_fn_bodies_def] >>
  sq `{h0}` `set (MAP FST fns)` nb_tac >>
  sq `{}` `set (MAP FST fns)`
    (ok_tac >> MATCH_ACCEPT_TAC fuel_ok_compile_entry_checks) >>
  sq `{}` `set (MAP FST fns)`
    (match_mp_tac fuel_okS_mono >>
     qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var h1`,
                   `UNIV`, `{}`, `{}`] >>
     rpt conj_tac
     >- (match_mp_tac fuel_okS_compile_external_function_body >>
         conj_tac >> first_assum ACCEPT_TAC)
     >- (rw[] >> irule cenv_ptrs_below_le >> qexists_tac `0` >> simp[]) >>
     simp[]) >>
  first_assum ACCEPT_TAC
QED

(* ===== Keyword arguments ===== *)

Theorem fuel_ok_compile_init_kwargs:
  ^hexpr ==>
  !kws cenv off k hi Wv E. fuel_ok Wv {} E (compile_init_kwargs cenv kws off k hi)
Proof
  strip_tac >> drule fuel_ok_lower_value >> strip_tac >>
  Induct >- simp[compile_init_kwargs_def, fuel_ok_return] >>
  PairCases >> rpt gen_tac >> PURE_ONCE_REWRITE_TAC [compile_init_kwargs_def] >>
  PURE_REWRITE_TAC [compile_abi_arg_ptr_guard_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void,
             fuel_ok_compile_abi_decode_to_buf, fuel_ok_context_storage] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_kwarg_allocas:
  !specs cenv Wv E. fuel_ok Wv {} E (compile_create_kwarg_allocas cenv specs)
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, fuel_ok_return] >>
  PairCases >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_create_kwarg_allocas_def] >>
  fuel_auto [fuel_ok_compile_alloc_buffer]
QED

Theorem compile_create_kwarg_allocas_ptrs:
  !specs cenv st kw st'.
    compile_create_kwarg_allocas cenv specs st = (kw, st') ==>
    st.cs_next_var <= st'.cs_next_var /\
    EVERY (\k. !x. FST (SND k) = Var x ==> var_below st'.cs_next_var x) kw
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_var >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  metis_tac[var_below_le]
QED

Theorem compile_register_kwarg_vars_ptrs:
  !kw cenv n.
    (compile_register_kwarg_vars cenv kw).ce_ctor_exit_label =
      cenv.ce_ctor_exit_label /\
    (cenv_ptrs_below n cenv /\
     EVERY (\k. !x. FST (SND k) = Var x ==> var_below n x) kw ==>
     cenv_ptrs_below n (compile_register_kwarg_vars cenv kw))
Proof
  Induct >- simp[compile_register_kwarg_vars_def] >>
  PairCases >> rpt gen_tac >> simp[compile_register_kwarg_vars_def] >>
  strip_tac >> first_x_assum (irule o GEN_ALL o CONJUNCT2 o SPEC_ALL) >> simp[] >>
  rw[cenv_ptrs_below_def, FLOOKUP_UPDATE] >> gvs[AllCaseEqs()] >>
  fs[cenv_ptrs_below_def] >> metis_tac[]
QED

(* The common body of a function with default arguments is its external
   body in the environment with the kwarg buffers registered. *)
Theorem fuel_okS_compile_common_function_body:
  !cenv args kw nr nkey ut iv stmts rt.
    cenv.ce_ctor_exit_label = NONE /\ ^hstmts ==>
    fuel_okS
      (\st. cenv_ptrs_below st.cs_next_var (compile_register_kwarg_vars cenv kw))
      UNIV {} {}
      (compile_common_function_body cenv args kw nr nkey ut iv stmts rt)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_common_function_body cenv args kw nr nkey ut iv stmts rt =
   compile_external_function_body (compile_register_kwarg_vars cenv kw)
     args nr nkey ut iv stmts rt` by
    simp[compile_common_function_body_def,
         compile_external_function_body_def] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac fuel_okS_compile_external_function_body >>
  simp[compile_register_kwarg_vars_ptrs]
QED
