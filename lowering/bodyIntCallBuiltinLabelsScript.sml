(* Supported builtin callback boundaries. *)
Theory bodyIntCallBuiltinLabels
Ancestors
  bodyIntCallExprClosure bodyIntCallExprLabels bodyIntCallLabelFrame
  bodyIntCallContextLabels bodyIntCallLabelReservations
  supportedExprForms exprLowering compileEnv builtinMath list

Theorem compiler_block_tail_env_var:
  compiler_block_tail (compile_env_var item)
Proof
  Cases_on `item` >> simp[compile_env_var_def, compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_env_var:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_env_var item) (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `item` >> simp[compile_env_var_def, compiler_label_hoare_context_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_modular:
  compiler_block_tail (compile_addmod a b c) /\
  compiler_block_tail (compile_mulmod a b c) /\
  compiler_block_tail (compile_pow_mod256 a b)
Proof
  simp[compile_addmod_def, compile_mulmod_def, compile_pow_mod256_def,
       comp_ignore_bind_def, compiler_block_tail_primitives] >>
  conj_tac >> irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_modular:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_addmod a b c) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_mulmod a b c) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_pow_mod256 a b) (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_addmod_def, compile_mulmod_def, compile_pow_mod256_def,
       comp_ignore_bind_def, compiler_label_hoare_context_primitives] >>
  conj_tac >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_result_map:
  compiler_block_tail m ==>
  compiler_block_tail (\st. (h (FST (m st)), SND (m st)))
Proof
  simp[compiler_block_tail_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`tail`, `st`] mp_tac) >>
  Cases_on `m st` >> simp[] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem compiler_label_hoare_result_map:
  compiler_label_hoare P m (\r out. P out) ==>
  compiler_label_hoare P (\st. (h (FST (m st)), SND (m st))) (\r out. P out)
Proof
  simp[compiler_label_hoare_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >>
  Cases_on `m st` >> gvs[]
QED

Theorem compiler_block_tail_as_stack_val:
  compiler_block_tail m ==> compiler_block_tail (\st. as_stack_val ty (m st))
Proof
  strip_tac >>
  `!st. as_stack_val ty (m st) = (StackValue ty (FST (m st)), SND (m st))` by
    (gen_tac >> Cases_on `m st` >> simp[as_stack_val_def]) >>
  simp[] >> irule compiler_block_tail_result_map >> simp[]
QED

Theorem compiler_label_hoare_as_stack_val:
  compiler_label_hoare P m (\r out. P out) ==>
  compiler_label_hoare P (\st. as_stack_val ty (m st)) (\r out. P out)
Proof
  strip_tac >>
  `!st. as_stack_val ty (m st) = (StackValue ty (FST (m st)), SND (m st))` by
    (gen_tac >> Cases_on `m st` >> simp[as_stack_val_def]) >>
  simp[] >> irule compiler_label_hoare_result_map >> simp[]
QED

Theorem compiler_block_tail_env_dispatch:
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (Env item) args)
Proof
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  irule compiler_block_tail_as_stack_val >>
  simp[compiler_block_tail_env_var]
QED

Theorem compiler_label_hoare_env_dispatch:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (Env item) args)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  irule compiler_label_hoare_as_stack_val >>
  simp[compiler_label_hoare_env_var]
QED

Theorem compiler_pair_bind_eq:
  (\st. (\(x,s). k x s) (m st)) = comp_bind m k
Proof
  simp[FUN_EQ_THM, comp_bind_def]
QED

Theorem compiler_block_tail_pair_bind:
  compiler_block_tail m /\ (!x. compiler_block_tail (k x)) ==>
  compiler_block_tail (\st. (\(x,s). k x s) (m st))
Proof
  rewrite_tac[compiler_pair_bind_eq] >> strip_tac >>
  irule compiler_block_tail_bind >> simp[]
QED

Theorem compiler_label_hoare_pair_bind:
  compiler_label_hoare P (m:compile_state -> 'a # compile_state) (\x st. P st) /\
  (!x. compiler_label_hoare P (k x) R) ==>
  compiler_label_hoare P (\st. (\(x,s). k x s) (m st)) R
Proof
  simp[compiler_label_hoare_def] >> rpt strip_tac >>
  Cases_on `m st` >> gvs[] >> metis_tac[]
QED

Theorem compiler_block_tail_powmod_dispatch:
  (!ce t. compiler_block_tail (cfn ce t a) /\ compiler_block_tail (cfn ce t b)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty PowMod256 [a;b])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >>
  simp[EL, HD, TL] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_as_stack_val >>
  simp[compiler_block_tail_modular]
QED

Theorem compiler_label_hoare_powmod_dispatch:
  (!ce t.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t a) (\r out. compiler_label_reservation origin pending out) /\
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t b) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty PowMod256 [a;b])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >>
  simp[EL, HD, TL] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_as_stack_val >>
  simp[compiler_label_hoare_modular]
QED
