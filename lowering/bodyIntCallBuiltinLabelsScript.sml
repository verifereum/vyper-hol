(* Supported builtin callback boundaries. *)
Theory bodyIntCallBuiltinLabels
Ancestors
  bodyIntCallExprClosure bodyIntCallExprLabels bodyIntCallLabelFrame
  bodyIntCallContextLabels bodyIntCallLabelReservations
  supportedExprForms supportedTypes exprLowering compileEnv builtinMath builtinMisc builtinSimple list

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
  simp[] >> ho_match_mp_tac compiler_block_tail_result_map >> simp[]
QED

Theorem compiler_label_hoare_as_stack_val:
  compiler_label_hoare P m (\r out. P out) ==>
  compiler_label_hoare P (\st. as_stack_val ty (m st)) (\r out. P out)
Proof
  strip_tac >>
  `!st. as_stack_val ty (m st) = (StackValue ty (FST (m st)), SND (m st))` by
    (gen_tac >> Cases_on `m st` >> simp[as_stack_val_def]) >>
  simp[] >> ho_match_mp_tac compiler_label_hoare_result_map >> simp[]
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

Theorem compiler_block_tail_acc:
  item <> Code /\ (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_acc cfn cenv e item)
Proof
  strip_tac >> Cases_on `item` >> gvs[] >>
  rewrite_tac[lambdify (oneline compile_acc_def)] >> simp[] >>
  all_tac
  >~ [`compiler_block_tail (\st. lower_value _ _ _ _ st)`]
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
  (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >>
   rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
        >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives]) >> gen_tac >> BETA_TAC) >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives])
QED

Theorem compiler_label_hoare_acc:
  item <> Code /\
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_acc cfn cenv e item) (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> Cases_on `item` >> gvs[] >>
  rewrite_tac[lambdify (oneline compile_acc_def)] >> simp[] >> all_tac
  >~ [`compiler_label_hoare _ (\st. lower_value _ _ _ _ st) _`]
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
   >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
       irule compiler_label_hoare_lower_value >> simp[]) >>
   gen_tac >> BETA_TAC >>
   rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
        >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
            simp[compiler_label_hoare_context_primitives]) >> gen_tac >> BETA_TAC) >>
   CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
   simp[compiler_label_hoare_context_primitives])
QED

Theorem compiler_block_tail_acc_dispatch:
  item <> Code /\ (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (Acc item) [e])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  irule compiler_block_tail_as_stack_val >> irule compiler_block_tail_acc >> simp[]
QED

Theorem compiler_label_hoare_acc_dispatch:
  item <> Code /\
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (Acc item) [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  irule compiler_label_hoare_as_stack_val >> irule compiler_label_hoare_acc >> simp[]
QED

Theorem compiler_block_tail_ecrecover:
  compiler_block_tail (compile_ecrecover h v r s)
Proof
  rewrite_tac[compile_ecrecover_def, comp_ignore_bind_def] >>
  simp[comp_bind_assoc] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- simp[compiler_block_tail_alloc_buffer] >>
  gen_tac >> BETA_TAC >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer] >>
    gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ecrecover:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ecrecover h v r s) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_ecrecover_def, comp_ignore_bind_def] >> simp[comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
            compiler_label_hoare_storage_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_ec_points:
  compiler_block_tail (compile_ecadd_points p q) /\
  compiler_block_tail (compile_ecmul_point p scalar)
Proof
  conj_tac >> rewrite_tac[compile_ecadd_points_def, compile_ecmul_point_def,
                         comp_ignore_bind_def] >> simp[comp_bind_assoc] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer] >>
    gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ec_points:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ecadd_points p q) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ecmul_point p scalar) (\r out. compiler_label_reservation origin pending out)
Proof
  conj_tac >> rewrite_tac[compile_ecadd_points_def, compile_ecmul_point_def,
                         comp_ignore_bind_def] >> simp[comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
            compiler_label_hoare_storage_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_ecrecover_dispatch:
  (!e ce t. MEM e [h;v;r;s] ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty ECRecover [h;v;r;s])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
    >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
    gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_ecrecover]
QED

Theorem compiler_label_hoare_ecrecover_dispatch:
  (!e ce t. MEM e [h;v;r;s] ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty ECRecover [h;v;r;s])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        irule compiler_label_hoare_lower_value >> simp[]) >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_ecrecover]
QED

Theorem compiler_block_tail_as_ptr_val:
  compiler_block_tail m ==> compiler_block_tail (\st. as_ptr_val ty loc (m st))
Proof
  strip_tac >>
  `!st. as_ptr_val ty loc (m st) =
    (LocatedValue ty (mk_ptr (FST (m st)) loc), SND (m st))` by
    (gen_tac >> Cases_on `m st` >> simp[as_ptr_val_def]) >>
  simp[] >> ho_match_mp_tac compiler_block_tail_result_map >> simp[]
QED

Theorem compiler_label_hoare_as_ptr_val:
  compiler_label_hoare P m (\r out. P out) ==>
  compiler_label_hoare P (\st. as_ptr_val ty loc (m st)) (\r out. P out)
Proof
  strip_tac >>
  `!st. as_ptr_val ty loc (m st) =
    (LocatedValue ty (mk_ptr (FST (m st)) loc), SND (m st))` by
    (gen_tac >> Cases_on `m st` >> simp[as_ptr_val_def]) >>
  simp[] >> ho_match_mp_tac compiler_label_hoare_result_map >> simp[]
QED

Theorem compiler_block_tail_ecadd_dispatch:
  (!e ce t. MEM e [p;q] ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty ECAdd [p;q])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
    >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
        simp[compiler_block_tail_unwrap_value]) >> gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_as_ptr_val >> simp[compiler_block_tail_ec_points]
QED

Theorem compiler_label_hoare_ecadd_dispatch:
  (!e ce t. MEM e [p;q] ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty ECAdd [p;q])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        simp[compiler_label_hoare_unwrap_value]) >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_as_ptr_val >> simp[compiler_label_hoare_ec_points]
QED

Theorem compiler_block_tail_ecmul_dispatch:
  (!e ce t. MEM e [p;q] ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty ECMul [p;q])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_unwrap_value]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_as_ptr_val >> simp[compiler_block_tail_ec_points]
QED

Theorem compiler_label_hoare_ecmul_dispatch:
  (!e ce t. MEM e [p;q] ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty ECMul [p;q])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD, EL] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >> simp[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      simp[compiler_label_hoare_unwrap_value]) >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_as_ptr_val >> simp[compiler_label_hoare_ec_points]
QED

Theorem compiler_block_tail_make_array_dispatch:
  (!e ce t. MEM e args ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (MakeArray et bnd) args)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `et` >> simp[] >>
  (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_alloc_buffer]) >>
   gen_tac >> BETA_TAC >> irule compiler_block_tail_as_ptr_val)
  >- (irule compiler_block_tail_make_tuple >> simp[EVERY_MEM]) >>
  irule compiler_block_tail_make_array >> simp[EVERY_MEM]
QED

Theorem compiler_label_hoare_make_array_dispatch:
  (!e ce t origin pending. MEM e args ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (MakeArray et bnd) args)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `et` >> simp[] >>
  (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
   >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
       simp[compiler_label_hoare_storage_primitives]) >>
   gen_tac >> BETA_TAC >> irule compiler_label_hoare_as_ptr_val)
  >- (irule compiler_label_hoare_make_tuple >> simp[EVERY_MEM]) >>
  irule compiler_label_hoare_make_array >> simp[EVERY_MEM]
QED

Theorem compiler_block_tail_slice_calldata:
  compiler_block_tail (compile_slice_calldata start len sz)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_calldata_def, builtinBytesTheory.compile_slice_out_buf_def,
    builtinBytesTheory.compile_assert_slice_bounds_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer] >>
    gen_tac >> BETA_TAC >> simp[comp_bind_assoc]) >>
  PairCases_on `x` >> simp[comp_bind_assoc] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_slice_calldata:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_slice_calldata start len sz) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_calldata_def, builtinBytesTheory.compile_slice_out_buf_def,
    builtinBytesTheory.compile_assert_slice_bounds_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
            compiler_label_hoare_storage_primitives] >>
    gen_tac >> BETA_TAC >> simp[comp_bind_assoc]) >>
  PairCases_on `x` >> simp[comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
    gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_calldata_slice_dispatch:
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (CalldataSlice n) [e])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_as_ptr_val >>
  simp[compiler_block_tail_slice_calldata]
QED

Theorem compiler_label_hoare_calldata_slice_dispatch:
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (CalldataSlice n) [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_as_ptr_val >>
  simp[compiler_label_hoare_slice_calldata]
QED

Theorem compiler_block_tail_uint2str:
  compiler_block_tail (compile_uint2str v n sz)
Proof
  rewrite_tac[builtinStringsTheory.compile_uint2str_def, comp_ignore_bind_def] >>
  simp[comp_bind_assoc] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer] >>
    gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_uint2str:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_uint2str v n sz) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[builtinStringsTheory.compile_uint2str_def, comp_ignore_bind_def] >>
  simp[comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
            compiler_label_hoare_storage_primitives] >> gen_tac >> BETA_TAC) >>
  ntac 6 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
    gen_tac >> BETA_TAC) >>
  ho_match_mp_tac compiler_label_hoare_new_block_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> gvs[] >>
  simp[pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT_RWT] >>
  ntac 5
    (rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
      gen_tac >> BETA_TAC) >>
     ho_match_mp_tac compiler_label_hoare_new_block_bind >> conj_tac >- simp[] >>
     gen_tac >> BETA_TAC >> simp[pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT_RWT]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_uint2str_dispatch:
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (Uint2Str n) [e])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_as_ptr_val >>
  simp[compiler_block_tail_uint2str]
QED

Theorem compiler_label_hoare_uint2str_dispatch:
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (Uint2Str n) [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >> simp[HD] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_as_ptr_val >>
  simp[compiler_label_hoare_uint2str]
QED

Theorem compiler_block_tail_safe_sub:
  compiler_block_tail (compile_safe_sub x y ty)
Proof
  rewrite_tac[compile_safe_sub_def, LET_THM] >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  Cases_on `type_bits ty < 256` >> simp[compiler_block_tail_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_safe_sub:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_sub x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_sub_def, LET_THM] >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  Cases_on `type_bits ty < 256` >> simp[compiler_label_hoare_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_mul_overflow_check:
  compiler_block_tail (compile_mul_overflow_check x y res signed bits)
Proof
  rewrite_tac[compile_mul_overflow_check_def, LET_THM] >> BETA_TAC >>
  Cases_on `signed /\ bits = 256` >> simp[comp_bind_assoc] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_mul_overflow_check:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_mul_overflow_check x y res signed bits)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_mul_overflow_check_def, LET_THM] >> BETA_TAC >>
  Cases_on `signed /\ bits = 256` >> simp[comp_bind_assoc] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_safe_mul:
  compiler_block_tail (compile_safe_mul x y ty)
Proof
  rewrite_tac[compile_safe_mul_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  Cases_on `type_bits ty > 128` >> Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_mul_overflow_check] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_clamp_and_return]
QED

Theorem compiler_label_hoare_safe_mul:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_mul x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_mul_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  Cases_on `type_bits ty > 128` >> Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
               compiler_label_hoare_mul_overflow_check] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
       compiler_label_hoare_clamp_and_return]
QED

Theorem compiler_block_tail_safe_div:
  compiler_block_tail (compile_safe_div x y ty)
Proof
  rewrite_tac[compile_safe_div_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_clamp_and_return]
QED

Theorem compiler_label_hoare_safe_div:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_div x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_div_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
       compiler_label_hoare_clamp_and_return]
QED

Theorem compiler_block_tail_safe_decimal_div:
  compiler_block_tail (compile_safe_decimal_div x y divisor ty)
Proof
  rewrite_tac[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_clamp_and_return]
QED

Theorem compiler_label_hoare_safe_decimal_div:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_decimal_div x y divisor ty)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_clamp_and_return]
QED

Theorem compiler_block_tail_safe_mod:
  compiler_block_tail (compile_safe_mod x y ty)
Proof
  rewrite_tac[compile_safe_mod_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_safe_mod:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_mod x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_mod_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_safe_pow:
  compiler_block_tail (compile_safe_pow x y ty base_literal exp_literal)
Proof
  rewrite_tac[compile_safe_pow_def, LET_THM] >> BETA_TAC >>
  Cases_on `base_literal` >> simp[]
  >- (Cases_on `exp_literal` >> simp[comp_ignore_bind_def]
      >- (irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
          gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
          simp[compiler_block_tail_clamp, compiler_block_tail_primitives]) >>
      rename1 `Num exponent_int` >>
      Cases_on `exponent_int = 0 \/ Num exponent_int = 1` >> simp[] >>
      Cases_on `is_signed_type ty` >> simp[] >>
      rpt (irule compiler_block_tail_bind >> reverse conj_tac
           >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
      simp[compiler_block_tail_primitives]) >>
  rename1 `base_int = -1` >>
  Cases_on `base_int = -1 \/ base_int = 0 \/ base_int = 1` >> simp[] >>
  Cases_on `is_signed_type ty` >> simp[comp_bind_assoc, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_safe_pow:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_safe_pow x y ty base_literal exp_literal)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_safe_pow_def, LET_THM] >> BETA_TAC >>
  Cases_on `base_literal` >> simp[]
  >- (Cases_on `exp_literal` >> simp[comp_ignore_bind_def]
      >- (irule compiler_label_hoare_preserving_bind >>
          simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
          irule compiler_label_hoare_preserving_bind >>
          simp[compiler_label_hoare_clamp, compiler_label_hoare_typed_primitives]) >>
      rename1 `Num exponent_int` >>
      Cases_on `exponent_int = 0 \/ Num exponent_int = 1` >> simp[] >>
      Cases_on `is_signed_type ty` >> simp[] >>
      rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
           >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
           gen_tac >> BETA_TAC) >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
  rename1 `base_int = -1` >>
  Cases_on `base_int = -1 \/ base_int = 0 \/ base_int = 1` >> simp[] >>
  Cases_on `is_signed_type ty` >> simp[comp_bind_assoc, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_compare:
  compiler_block_tail (compile_compare op x y ty)
Proof
  Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_ignore_bind_def, compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_compare:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_compare op x y ty) (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_ignore_bind_def, compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_wrap_truncate:
  compiler_block_tail (wrap_truncate res ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_wrap_truncate:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (wrap_truncate res ty) (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_select:
  compiler_block_tail (compile_select cond_op then_op else_op)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_select:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_select cond_op then_op else_op)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_binop:
  compiler_block_tail (compile_binop op x y ty base_literal exp_literal)
Proof
  Cases_on `op` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, LET_THM, comp_ignore_bind_def,
       compiler_block_tail_safe_add, compiler_block_tail_safe_sub,
       compiler_block_tail_safe_mul, compiler_block_tail_safe_div,
       compiler_block_tail_safe_decimal_div, compiler_block_tail_safe_mod,
       compiler_block_tail_safe_pow, compiler_block_tail_compare,
       compiler_block_tail_primitives] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_wrap_truncate,
       compiler_block_tail_select]
QED

Theorem compiler_label_hoare_binop:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_binop op x y ty base_literal exp_literal)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `op` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, LET_THM, comp_ignore_bind_def,
       compiler_label_hoare_safe_add, compiler_label_hoare_safe_sub,
       compiler_label_hoare_safe_mul, compiler_label_hoare_safe_div,
       compiler_label_hoare_safe_decimal_div, compiler_label_hoare_safe_mod,
       compiler_label_hoare_safe_pow, compiler_label_hoare_compare,
       compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
       compiler_label_hoare_wrap_truncate, compiler_label_hoare_select]
QED

Theorem compiler_block_tail_bop_dispatch:
  op <> In /\ op <> NotIn /\ ~is_bytestring_type (expr_type a) /\
  (!e ce t. MEM e [a;b] ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty (Bop op) [a;b])
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >>
  simp[HD, TL] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
       >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
           irule compiler_block_tail_lower_value >> simp[]) >> gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_binop]
QED

Theorem compiler_label_hoare_bop_dispatch:
  op <> In /\ op <> NotIn /\ ~is_bytestring_type (expr_type a) /\
  (!e ce t. MEM e [a;b] ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty (Bop op) [a;b])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_builtin_dispatch_body_def] >>
  simp[HD, TL] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
       >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
           irule compiler_label_hoare_lower_value >> simp[]) >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_binop]
QED

Theorem supported_binop_scalar_dispatch:
  supported_binop op ty rhs lit nonneg ==>
  op <> In /\ op <> NotIn /\ ~is_bytestring_type ty
Proof
  Cases_on `op` >> simp[supported_binop_def] >>
  Cases_on `ty` >> simp[supported_numeric_type_def, supported_integer_type_def,
    supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_numeric_type_def, supported_integer_type_def,
    supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, is_bytestring_type_def]
QED

Theorem compiler_block_tail_supported_builtin_general:
  supported_builtin_form tops support_ann bi es /\
  (!e ce t. MEM e es ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi es)
Proof
  strip_tac >> Cases_on `bi` >> gvs[supported_builtin_form_def, AllCaseEqs()]
  >~ [`(MakeArray elem bd)`] >- (irule compiler_block_tail_make_array_dispatch >> simp[]) >>
  qpat_x_assum `case es of [] => _ | _::_ => _` (mp_tac o EQT_INTRO) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >~ [`CalldataSlice n`] >- (irule compiler_block_tail_calldata_slice_dispatch >> simp[])
  >~ [`Uint2Str n`] >- (irule compiler_block_tail_uint2str_dispatch >> simp[])
  >~ [`ECRecover`] >- (irule compiler_block_tail_ecrecover_dispatch >> simp[] >> metis_tac[])
  >~ [`ECAdd`] >- (irule compiler_block_tail_ecadd_dispatch >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`ECMul`] >- (irule compiler_block_tail_ecmul_dispatch >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`BlockHash`] >- (irule compiler_block_tail_block_blob_hash_dispatch >> simp[])
  >~ [`BlobHash`] >- (irule compiler_block_tail_block_blob_hash_dispatch >> simp[])
  >~ [`Acc item`] >- (irule compiler_block_tail_acc_dispatch >> simp[])
  >~ [`Env item`] >- simp[compiler_block_tail_env_dispatch]
  >~ [`AsWeiValue d`] >- (irule compiler_block_tail_as_wei_dispatch >> simp[])
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ Not _`],
          irule compiler_block_tail_unary_dispatch >> simp[])
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ Neg _`],
          irule compiler_block_tail_unary_dispatch >> simp[])
  >~ [`Abs`] >- (irule compiler_block_tail_unary_dispatch >> simp[])
  >~ [`PowMod256`] >- (irule compiler_block_tail_powmod_dispatch >> simp[])
  >~ [`AddMod`] >- (irule compiler_block_tail_modular_dispatch >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`MulMod`] >- (irule compiler_block_tail_modular_dispatch >> simp[] >> first_assum ACCEPT_TAC) >>
  drule supported_binop_scalar_dispatch >> strip_tac >>
  irule compiler_block_tail_bop_dispatch >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem compiler_label_hoare_supported_builtin_general:
  supported_builtin_form tops support_ann bi es /\
  (!e ce t origin pending. MEM e es ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi es)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> Cases_on `bi` >> gvs[supported_builtin_form_def, AllCaseEqs()]
  >~ [`MakeArray elem bd`] >- (irule compiler_label_hoare_make_array_dispatch >> simp[]) >>
  qpat_x_assum `case es of [] => _ | _::_ => _` (mp_tac o EQT_INTRO) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >~ [`CalldataSlice n`] >- (irule compiler_label_hoare_calldata_slice_dispatch >> simp[])
  >~ [`Uint2Str n`] >- (irule compiler_label_hoare_uint2str_dispatch >> simp[])
  >~ [`ECRecover`] >- (irule compiler_label_hoare_ecrecover_dispatch >> simp[] >> metis_tac[])
  >~ [`ECAdd`] >- (irule compiler_label_hoare_ecadd_dispatch >> simp[] >> metis_tac[])
  >~ [`ECMul`] >- (irule compiler_label_hoare_ecmul_dispatch >> simp[] >> metis_tac[])
  >~ [`BlockHash`] >- (irule compiler_label_hoare_block_blob_hash_dispatch >> simp[])
  >~ [`BlobHash`] >- (irule compiler_label_hoare_block_blob_hash_dispatch >> simp[])
  >~ [`Acc item`] >- (irule compiler_label_hoare_acc_dispatch >> simp[])
  >~ [`Env item`] >- simp[compiler_label_hoare_env_dispatch]
  >~ [`AsWeiValue d`] >- (irule compiler_label_hoare_as_wei_dispatch >> simp[])
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ Not _`],
          irule compiler_label_hoare_unary_dispatch >> simp[])
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ Neg _`],
          irule compiler_label_hoare_unary_dispatch >> simp[])
  >~ [`Abs`] >- (irule compiler_label_hoare_unary_dispatch >> simp[])
  >~ [`PowMod256`] >- (irule compiler_label_hoare_powmod_dispatch >> simp[])
  >~ [`AddMod`] >- (irule compiler_label_hoare_modular_dispatch >> simp[] >> metis_tac[])
  >~ [`MulMod`] >- (irule compiler_label_hoare_modular_dispatch >> simp[] >> metis_tac[]) >>
  drule supported_binop_scalar_dispatch >> strip_tac >>
  irule compiler_label_hoare_bop_dispatch >> simp[] >> metis_tac[]
QED

Theorem compiler_block_tail_supported_builtin_source:
  supported_builtin_form tops ann bi es /\
  (!e ce t. MEM e es ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi es)
Proof
  metis_tac[compiler_block_tail_supported_builtin_general]
QED

Theorem compiler_block_tail_supported_builtin:
  supported_builtin_form tops ty bi es /\
  (!e ce t. MEM e es ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_builtin_dispatch_body cfn cenv ann ty bi es)
Proof
  metis_tac[compiler_block_tail_supported_builtin_general]
QED

Theorem compiler_label_hoare_supported_builtin_source:
  supported_builtin_form tops ann bi es /\
  (!e ce t origin pending. MEM e es ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi es)
    (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[compiler_label_hoare_supported_builtin_general]
QED

Theorem compiler_label_hoare_supported_builtin:
  supported_builtin_form tops ty bi es /\
  (!e ce t origin pending. MEM e es ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch_body cfn cenv ann ty bi es)
    (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[compiler_label_hoare_supported_builtin_general]
QED
