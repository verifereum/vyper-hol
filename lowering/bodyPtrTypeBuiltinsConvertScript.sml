(* Convert composition boundaries: these do not import the signed residual. *)
Theory bodyPtrTypeBuiltinsConvert
Ancestors bodyPtrTypeBuiltinsScalarDispatch bodyPtrTypeBuiltinsMemoryContinue
  bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsBoolContinue
  bodyPtrTypeBuiltinsAddressContinue bodyPtrTypeBuiltinsFixedContinue
  bodyPtrTypeBuiltinsConvertEntry bodyPtrTypeBuiltinsOperands
  gasSummaryComposePtr fragGasPathPtr exprLowering exprLoweringProps
  bodyPtrDefs exprSimDefs exprSimHypsDefs compileEnv vyperAST vyperTypeSystem
  vyperInterpreter vyperState exprSimConvert

Theorem scalar_convert_dispatch:
  ~is_bytestring_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) ==>
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    as_stack_val ann (compile_type_convert x
      (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) typ) sm)
Proof
  strip_tac >> Cases_on `typ` >>
  simp[compile_type_builtin_dispatch_body_def]
QED

Theorem bytestring_word_convert_dispatch:
  is_bytestring_type (expr_type e) /\ is_word_type typ /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) ==>
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
       lowered_value_type cenv e = BaseT (StringT 0)
    then (StackValue ann (Lit 0w),sm)
    else as_stack_val ann (compile_type_convert x
      (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) typ) sm)
Proof
  strip_tac >> `~is_bytestring_type typ` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  Cases_on `typ` >> simp[compile_type_builtin_dispatch_body_def]
QED

Theorem bytestring_base_convert_dispatch_packet:
  is_bytestring_type (expr_type e) /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert (BaseT bt) [e] sa =
    (StackValue ann op,sb) ==>
  if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv e = BaseT (StringT 0)
  then op = Lit 0w /\ sb = sm
  else compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) sm = (op,sb)
Proof
  strip_tac >> drule_all bytestring_word_convert_dispatch >>
  disch_then (qspecl_then [`ty`,`ann`] mp_tac) >> simp[] >> disch_tac >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
    lowered_value_type cenv e = BaseT (StringT 0)` >> fs[] >>
  Cases_on `compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) sm` >>
  gvs[as_stack_val_def]
QED

Theorem bytestring_scalar_convert_shapes:
  !src dst. is_bytestring_type src /\ ~is_bytestring_type dst /\
    valid_conversion src dst /\
    ~((?n. dst = BaseT (IntT n)) \/ dst = BaseT DecimalT) ==>
    ((?n. src = BaseT (BytesT (Dynamic n))) /\
      ((?b. dst = BaseT (UintT b)) \/ dst = BaseT BoolT \/ dst = BaseT AddressT)) \/
    ((?n. src = BaseT (BytesT (Dynamic n)) \/ src = BaseT (StringT n)) /\
      (?m. dst = BaseT (BytesT (Fixed m))))
Proof
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT st)` >> Cases_on `st` >>
  simp[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  Cases_on `dst` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT dt)` >> Cases_on `dt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT (BytesT dd))` >> Cases_on `dd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
QED

Theorem convert_normal_continuation:
  expr_post ctx func cenv cx e es sa sm s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~(is_bytestring_type (expr_type e) /\
    ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    (StackValue ann op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v1,ee) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G t0) /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  body_inv tops ctx cenv cx /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) typ v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\ ptr_val_ok cx typ v op H th ss /\
      (~is_word_type typ ==> ptr_buf_ok cenv (TypeBuiltin ann Convert typ [e]) op H ss) /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- suspend "bytestring" >>
  `compile_type_convert x
    (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
     | _ => mk_convert_op (expr_type e) typ) sm = (op,sb)` by
    (drule_all scalar_convert_dispatch >>
     disch_then (qspecl_then [`typ`,`ty`,`ann`] assume_tac) >>
     Cases_on `compile_type_convert x
       (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
        | _ => mk_convert_op (expr_type e) typ) sm` >>
     gvs[as_stack_val_def]) >>
  `is_word_type typ` by
    (drule_all bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_body_word_types >> simp[]) >>
  drule_all scalar_convert_continuation >>
  disch_then (qspec_then `PG` mp_tac) >> simp[]
QED

Resume convert_normal_continuation[bytestring]:
  `~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `ptr_buf_ok cenv e x G t0` by simp[] >>
  Cases_on `is_bytestring_type typ`
  >- (drule_all memory_convert_continuation >>
      disch_then (qspec_then `PG` mp_tac) >>
      simp[gas_summary_ptr_at_def] >> metis_tac[]) >>
  drule exprSimConvertTheory.expr_body_pre_convert >> strip_tac >> gvs[] >>
  `~cx.in_deploy` by fs[bodySimTheory.body_inv_def] >>
  `well_formed_type env.type_defs ann` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  drule bytestring_scalar_convert_shapes >>
  disch_then (qspec_then `ann` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[]
  >- suspend "uint"
  >- suspend "bool"
  >- suspend "address"
  >> suspend "fixed"
QED

Resume convert_normal_continuation[uint]:
  `is_word_type (BaseT (UintT b))` by simp[is_word_type_def] >>
  qpat_assum `expr_type e = _` (fn th => fs[GSYM th] >> assume_tac th) >>
  drule_all bytestring_base_convert_dispatch_packet >> disch_tac >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule bytes_uint_continuation >> simp[] >> metis_tac[]
QED

Resume convert_normal_continuation[bool]:
  `is_word_type (BaseT BoolT)` by simp[is_word_type_def] >>
  qpat_assum `expr_type e = _` (fn th => fs[GSYM th] >> assume_tac th) >>
  drule_all bytestring_base_convert_dispatch_packet >> disch_tac >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule bytes_bool_continuation >> simp[] >> metis_tac[]
QED

Resume convert_normal_continuation[address]:
  `is_word_type (BaseT AddressT)` by simp[is_word_type_def] >>
  qpat_assum `expr_type e = _` (fn th => fs[GSYM th] >> assume_tac th) >>
  drule_all bytestring_base_convert_dispatch_packet >> disch_tac >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule bytes_address_continuation >> simp[] >> metis_tac[]
QED

Resume convert_normal_continuation[fixed]:
  markerLib.RESUME_TAC >>
  qpat_assum `expr_type e = _` (fn th => fs[GSYM th] >> assume_tac th) >>
  `is_word_type (BaseT (BytesT (Fixed m)))` by
    fs[is_word_type_def, well_formed_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule_all bytestring_base_convert_dispatch_packet >> disch_tac >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule bytestring_fixed_continuation >> simp[] >> metis_tac[]
QED

Finalise convert_normal_continuation

Theorem eval_expr_convert_action:
  (\es. (do r <- eval_expr cx (TypeBuiltin ann Convert typ [e]); read_result cx r od) es) =
  (\es. (do v <- (do r <- eval_expr cx e; read_result cx r od);
            (\st. (convert_result cx (expr_type e) typ v,st)) od) es)
Proof
  pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `(do r <- eval_expr cx (TypeBuiltin ann Convert typ [e]); read_result cx r od) x` >>
  drule exprSimConvertTheory.eval_expr_convert_cases >>
  strip_tac >> gvs[vyperStateTheory.bind_def]
QED
