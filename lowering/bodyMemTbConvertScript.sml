(* Memory case of the body induction for convert.  The conversion of an
   internal call whose type widens its callee's return type is split off
   to bodyMemTbConvertWidened (held, as S1's bodySimConvertWidened); the
   rest is body_type_builtin_convert_plain_mem_case. *)
Theory bodyMemTbConvert
Ancestors
  bodyMemoryPreds bodyMemTbConvertWidened vyperContext vyperState
  bodyMemTbConvertOperand bodyMemTbConvertCompose bodyMemTbConvertIntSuffix
  bodyMemTbConvertScalarFlags bodyMemTbConvertLoadMemory
  bodyMemTbConvertScalarDispatch bodyMemTbConvertSourceDispatch
  bodyMemTbConvertDestMemory bodyMemTbConvertDestPath
  bodyMemTbConvertCopyMemory bodyMemTbConvertCastMemory

Theorem body_type_builtin_convert_plain_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Convert) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    !tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (TypeBuiltin v11 Convert typ es) st /\
      ~(?e1 a f cargs d. es = [e1] /\ e1 = Call a (IntCall f) cargs d /\
                         lowered_value_type cenv e1 <> expr_type e1) ==>
      expr_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Convert typ es) st /\
      expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Convert typ es) st
Proof
  cheat
QED

Theorem body_type_builtin_convert_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Convert) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Convert) typ es)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?e1 a f cargs d. es = [e1] /\ e1 = Call a (IntCall f) cargs d /\
                             lowered_value_type cenv e1 <> expr_type e1`
  >- (gvs[] >>
      `body_exprs_mem_ok cx [Call a (IntCall f) cargs d]` by
        (first_x_assum irule >>
         simp[type_check_def, assert_def, type_builtin_args_length_ok_def]) >>
      drule body_convert_widened_call_arg_mem >>
      disch_then (qspecl_then [`v11`, `typ`, `tops`, `ctx`, `func`, `cenv`,
                               `env`, `ty`, `es'`] mp_tac) >>
      simp[]) >>
  drule body_type_builtin_convert_plain_mem_case >>
  disch_then (qspecl_then [`v11`, `typ`, `tops`, `ctx`, `func`, `cenv`, `env`,
                           `ty`, `es'`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED
