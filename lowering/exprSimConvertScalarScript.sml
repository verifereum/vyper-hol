(*
 * Expression simulation for the scalar conversions (#636, Other
 * conversions)
 *
 * convert(e, t) where neither e's type nor t is a bytestring (Bytes[n],
 * String[n]) and the pair is not one exprSimConvert covers
 * (int_convert_pair): conversions to and from decimal, address, bytesM
 * and flags.
 *
 * TOP-LEVEL:
 *   compile_convert_scalar_case — expr_vv_case of such a conversion
 *)

Theory exprSimConvertScalar
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
   exprSimHypsDefs exprSimSource exprSimHyps exprSimConvert exprSimUnop compileEnv vyperAST
  convertScalarBridge convertScalarSim convertScalarTyping convertScalarDispatch
  exprSimOperators

Theorem compile_convert_scalar_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    ~is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    ~int_convert_pair (expr_type e1) t ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  rw[expr_vv_case_def] >>
  drule expr_body_pre_scalar_convert >> strip_tac >>
  `is_word_type (expr_type e1) /\ is_word_type t` by
    (drule_all scalar_conversion_word_types >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (gvs[exprs_case_def] >>
     irule expr_sim_case_apply >> conj_tac >- (qexists `env` >> simp[]) >>
     qexists `nocalls` >> simp[] >>
     metis_tac[int_calls_type_builtin_arg, listTheory.MEM]) >>
  irule scalar_convert_sim_to_vv >>
  irule compile_convert_frag_sim >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `\x. compile_type_convert x
    (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
             | _ => mk_convert_op (expr_type e1) t)` >>
  rpt conj_tac
  >~ [`lower_value _ _ _ _ _ = _`] >- metis_tac[lower_value_convert]
  >~ [`unop_frag _ _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ann`, `ann`, `e1`,
                   `es with gas_obs := gs1`, `v1`, `es1`]
        mp_tac scalar_operand_typed_frag >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all scalar_dispatch_extends >> simp[]
QED
