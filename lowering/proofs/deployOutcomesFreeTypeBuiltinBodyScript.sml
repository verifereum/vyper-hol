Theory deployOutcomesFreeTypeBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list builtinAbi

Theorem outcomes_free_type_builtin_constants:
  (!sz z st. Q st ==> Q (SND (compile_builtin_empty_complex sz z st))) /\
  (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty tb target_ty args s))
Proof
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_type_builtin_convert:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!sz v old st. Q st ==> Q (SND (compile_bytestring_widen_copy sz v old st))) /\
  (!v cv st. Q st ==> Q (SND (compile_type_convert v cv st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_type_builtin_args Convert target_ty (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty Convert target_ty args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_type_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
    (rpt strip_tac >>
     irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  simp[compile_type_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  rename1 `lower_value f ce _ _ s = (v, st)` >>
  `Q st` by metis_tac[pairTheory.SND] >>
  rpt IF_CASES_TAC >> simp[outcomes_free_as_stack_val] >>
  Cases_on `target_ty` >> simp[outcomes_free_as_stack_val]
QED

Theorem outcomes_free_type_builtin_extract32:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_src v st))) /\
  (!len data off st. Q st ==> Q (SND (compile_extract32_load len data off st))) /\
  (!v vt st. Q st ==> Q (SND (compile_clamp_basetype v vt st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_type_builtin_args Extract32 target_ty (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty Extract32 target_ty args s))
Proof
  strip_tac >>
  `LENGTH args = 2` by metis_tac[outcomes_free_type_builtin_arities] >>
  `EVERY (\e. well_typed_expr env e /\
    ~supported_expr_exists constructor_call_root e) args` by
    metis_tac[outcomes_free_typed_children] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (`args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `well_typed_expr env (EL 1 args) /\
   ~supported_expr_exists constructor_call_root (EL 1 args)` by
    (drule outcomes_free_select >> disch_then (qspec_then `1` mp_tac) >> simp[]) >>
  `!e ity st. (e = HD args \/ e = EL 1 args) /\ Q st ==>
    Q (SND (lower_value f ce ity e st))` by
    (rpt strip_tac >>
     irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[outcomes_free_as_stack_val] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_type_builtin_decode:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v info lo hi sz st. Q st ==>
     Q (SND (lower_abi_decode v info lo hi sz st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_type_builtin_args (AbiDecode unwrap) target_ty (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty (AbiDecode unwrap) target_ty args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_type_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[outcomes_free_as_ptr_val] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_type_builtin_encode:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!n st. Q st ==> Q (SND (compile_alloc_buffer n st))) /\
  (!op vs st. Q st ==> Q (SND (emit_void op vs st))) /\
  (!(ensure:bool) mid v info sz st. Q st ==>
     Q (SND (lower_abi_encode ensure mid v info sz st))) /\
  (!es st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_abi_encode_args f ce es st))) /\
  (!v off vs st. Q st ==> Q (SND (compile_store_abi_tuple ce v off vs st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty
    (AbiEncode ensure mid) target_ty args s))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC
  >- (`well_typed_expr env (HD args) /\
       ~supported_expr_exists constructor_call_root (HD args)` by
        (drule_all outcomes_free_typed_children >> strip_tac >>
         `args <> []` by (strip_tac >> gvs[]) >>
         drule_all outcomes_free_head >> simp[]) >>
      `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
        (rpt strip_tac >>
         irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
      IF_CASES_TAC >> rpt (pairarg_tac >> simp[]) >>
      simp[outcomes_free_as_ptr_val] >>
      metis_tac[pairTheory.SND]) >>
  rpt (pairarg_tac >> simp[]) >> simp[outcomes_free_as_ptr_val] >>
  metis_tac[pairTheory.SND]
QED

(* The ABI encoder's unused ensure parameter is polymorphic in its definition;
   fix it to bool here, as in the actual dispatch call. *)
Theorem outcomes_free_type_builtin_body:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!sz z st. Q st ==> Q (SND (compile_builtin_empty_complex sz z st))) /\
  (!sz v old st. Q st ==> Q (SND (compile_bytestring_widen_copy sz v old st))) /\
  (!v cv st. Q st ==> Q (SND (compile_type_convert v cv st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_src v st))) /\
  (!len data off st. Q st ==> Q (SND (compile_extract32_load len data off st))) /\
  (!v vt st. Q st ==> Q (SND (compile_clamp_basetype v vt st))) /\
  (!v info lo hi sz st. Q st ==> Q (SND (lower_abi_decode v info lo hi sz st))) /\
  (!n st. Q st ==> Q (SND (compile_alloc_buffer n st))) /\
  (!op vs st. Q st ==> Q (SND (emit_void op vs st))) /\
  (!(ensure:bool) mid v info sz st. Q st ==>
     Q (SND (lower_abi_encode ensure mid v info sz st))) /\
  (!es st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_abi_encode_args f ce es st))) /\
  (!v off vs st. Q st ==> Q (SND (compile_store_abi_tuple ce v off vs st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty tb target_ty args s))
Proof
  strip_tac >> Cases_on `tb`
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Convert`]
      >- (irule outcomes_free_type_builtin_convert >> simp[] >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Extract32`]
      >- (irule outcomes_free_type_builtin_extract32 >> simp[] >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiEncode _ _)`]
      >- (irule outcomes_free_type_builtin_encode >> simp[] >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiDecode _)`]
      >- (irule outcomes_free_type_builtin_decode >> simp[] >> metis_tac[]) >>
  irule outcomes_free_type_builtin_constants >> simp[]
QED
