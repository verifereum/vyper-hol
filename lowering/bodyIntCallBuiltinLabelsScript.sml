(* Supported builtin callback boundaries. *)
Theory bodyIntCallBuiltinLabels
Ancestors
  bodyIntCallExprClosure bodyIntCallExprLabels bodyIntCallLabelFrame
  bodyIntCallContextLabels bodyIntCallLabelReservations
  supportedExprForms exprLowering compileEnv builtinMath builtinMisc builtinSimple list

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

Theorem compiler_block_tail_modular_dispatch:
  (bi = AddMod \/ bi = MulMod) /\
  (!e ce t. MEM e [a;b;c] ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi [a;b;c])
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[EL, HD, TL] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
       >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
           irule compiler_block_tail_lower_value >> simp[]) >>
       gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_modular]
QED

Theorem compiler_label_hoare_modular_dispatch:
  (bi = AddMod \/ bi = MulMod) /\
  (!e ce t. MEM e [a;b;c] ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi [a;b;c])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[EL, HD, TL] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
       >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
           irule compiler_label_hoare_lower_value >> simp[]) >>
       gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_modular]
QED

Theorem compiler_block_tail_block_blob_hash:
  compiler_block_tail (compile_blockhash v) /\ compiler_block_tail (compile_blobhash v)
Proof
  simp[compile_blockhash_def, compile_blobhash_def, comp_ignore_bind_def,
       compiler_block_tail_primitives] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_block_blob_hash:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_blockhash v) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_blobhash v) (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_blockhash_def, compile_blobhash_def, comp_ignore_bind_def,
       compiler_label_hoare_context_primitives] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_block_blob_hash_dispatch:
  (bi = BlockHash \/ bi = BlobHash) /\
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi [e])
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
       irule compiler_block_tail_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >> irule compiler_block_tail_as_stack_val >>
   simp[compiler_block_tail_block_blob_hash])
QED

Theorem compiler_label_hoare_block_blob_hash_dispatch:
  (bi = BlockHash \/ bi = BlobHash) /\
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
   >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
       irule compiler_label_hoare_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >> irule compiler_label_hoare_as_stack_val >>
   simp[compiler_label_hoare_block_blob_hash])
QED

Theorem compiler_block_tail_unary:
  compiler_block_tail (compile_invert v ety cenv) /\
  compiler_block_tail (compile_neg v ety) /\
  compiler_block_tail (compile_builtin_abs v)
Proof
  conj_tac
  >- (Cases_on `ety` >> simp[compile_invert_def, compiler_block_tail_primitives]) >>
  Cases_on `type_bounds ety` >>
  simp[compile_neg_def, compile_builtin_abs_def, compile_select_def,
       comp_ignore_bind_def, compiler_block_tail_primitives] >>
  conj_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_unary:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_invert v ety cenv) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_neg v ety) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_abs v) (\r out. compiler_label_reservation origin pending out)
Proof
  conj_tac
  >- (Cases_on `ety` >> simp[compile_invert_def, compiler_label_hoare_context_primitives]) >>
  Cases_on `type_bounds ety` >>
  simp[compile_neg_def, compile_builtin_abs_def, compile_select_def,
       comp_ignore_bind_def, compiler_label_hoare_context_primitives] >>
  conj_tac >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_unary_dispatch:
  (bi = Not \/ bi = Neg \/ bi = Abs) /\
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi [e])
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
       irule compiler_block_tail_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >>
   Cases_on `expr_type e = BaseT BoolT` >> simp[] >>
   irule compiler_block_tail_as_stack_val >>
   simp[compiler_block_tail_unary, compiler_block_tail_primitives])
QED

Theorem compiler_label_hoare_unary_dispatch:
  (bi = Not \/ bi = Neg \/ bi = Abs) /\
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
   >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
       irule compiler_label_hoare_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >>
   Cases_on `expr_type e = BaseT BoolT` >> simp[] >>
   irule compiler_label_hoare_as_stack_val >>
   simp[compiler_label_hoare_unary, compiler_label_hoare_context_primitives])
QED

Theorem compiler_block_tail_as_wei:
  compiler_block_tail (compile_as_wei_value_int v scale signed) /\
  compiler_block_tail (compile_as_wei_value_decimal v scale divisor)
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, compile_as_wei_value_decimal_def,
       comp_ignore_bind_def, comp_bind_assoc, compiler_block_tail_primitives] >>
  rpt conj_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_as_wei:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_as_wei_value_int v scale signed)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_as_wei_value_decimal v scale divisor)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, compile_as_wei_value_decimal_def,
       comp_ignore_bind_def, comp_bind_assoc, compiler_label_hoare_context_primitives] >>
  rpt conj_tac >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_as_wei_dispatch:
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (AsWeiValue denom) [e])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> Cases_on `is_decimal_type (expr_type e)` >> simp[] >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_as_wei]
QED

Theorem compiler_label_hoare_as_wei_dispatch:
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (AsWeiValue denom) [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> Cases_on `is_decimal_type (expr_type e)` >> simp[] >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_as_wei]
QED
