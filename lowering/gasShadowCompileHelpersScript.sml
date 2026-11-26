Theory gasShadowCompileHelpers
Ancestors
  gasShadowCompileConvert gasShadowCompileContext
  gasShadowCompileAbi gasShadowCompileCallSupport gasShadowCompileBuiltinCreate
  gasShadowCompileMembership gasShadowCompilePure gasShadowCompileExternal
  exprLowering gasShadow gasShadowState compileEnv list vyperOriginFold vyperPinFold
  gasShadowCompileBase alist

Theorem gas_shadow_compiles_lower_value_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (lower_value f cenv ty e)
    (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))
Proof
  strip_tac >> simp[lower_value_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_unwrap_value]
QED

Theorem gas_shadow_compiles_lower_value_with_loc:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (lower_value_with_loc f cenv ty e)
    (lower_value_with_loc g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))
Proof
  strip_tac >> simp[lower_value_with_loc_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_multi_exprs_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es. gas_shadow_compiles (compile_multi_exprs f cenv es)
    (compile_multi_exprs g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> Induct >>
  simp[compile_multi_exprs_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> gvs[compile_multi_exprs_def] >> gen_tac >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (drule gas_shadow_compiles_lower_value_env >>
       metis_tac[COND_CLAUSES]) >>
   gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_expr_can_mutate:
  (!cenv e. expr_can_mutate cenv (gas_shadow_expr e) = expr_can_mutate cenv e) /\
  (!cenv es. exprs_can_mutate cenv (MAP gas_shadow_expr es) =
             exprs_can_mutate cenv es) /\
  (!cenv opt. opt_expr_can_mutate cenv (OPTION_MAP gas_shadow_expr opt) =
              opt_expr_can_mutate cenv opt) /\
  (!cenv kes. named_exprs_can_mutate cenv (MAP (I ## gas_shadow_expr) kes) =
              named_exprs_can_mutate cenv kes)
Proof
  ho_match_mp_tac expr_can_mutate_ind >>
  rw[expr_can_mutate_def, gas_shadow_expr_def, pairTheory.PAIR_MAP_THM]
QED

Theorem gas_shadow_compiles_ext_call_args:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es kw_es tys.
    gas_shadow_compiles (compile_ext_call_args f cenv kw_es tys es)
      (compile_ext_call_args g (gas_shadow_env sd cenv)
         (if sh then MAP gas_shadow_expr kw_es else kw_es) tys
         (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> Cases_on `sh` >> simp[] >> Induct >>
  rpt gen_tac >> Cases_on `tys` >>
  simp[compile_ext_call_args_def, gas_shadow_compiles_return] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (ONCE_REWRITE_TAC[GSYM MAP_APPEND] >>
       REWRITE_TAC[gas_shadow_expr_can_mutate] >>
       simp[gas_shadow_compiles_snapshot_vv]) >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_abi_encode_args_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es. gas_shadow_compiles (compile_abi_encode_args f cenv es)
    (compile_abi_encode_args g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> gen_tac >>
  `MAP (lowered_value_type cenv) (if sh then MAP gas_shadow_expr es else es) =
   MAP (lowered_value_type cenv) es` by
    (Cases_on `sh` >> simp[MAP_MAP_o, MAP_EQ_f, combinTheory.o_DEF]) >>
  simp[compile_abi_encode_args_def] >>
  drule gas_shadow_compiles_ext_call_args >>
  disch_then (qspecl_then [`sh`, `cenv`, `es`, `[]:expr list`,
                             `MAP (lowered_value_type cenv) es`] mp_tac) >>
  Cases_on `sh` >> simp[]
QED

Theorem gas_shadow_compiles_multi_vvs:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es. gas_shadow_compiles (compile_multi_vvs f cenv es)
    (compile_multi_vvs g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> Induct >>
  simp[compile_multi_vvs_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> gvs[compile_multi_vvs_def] >> gen_tac >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_make_tuple:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es tys off. gas_shadow_compiles (compile_make_tuple f cenv es tys buf_op off)
    (compile_make_tuple g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es) tys buf_op off)
Proof
  strip_tac >> Induct >>
  simp[compile_make_tuple_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> gvs[] >> rpt gen_tac >> Cases_on `tys` >>
  gvs[compile_make_tuple_def, comp_ignore_bind_def,
      gas_shadow_lowered_value_type, gas_shadow_compiles_return] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_store_memory,
                gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >> simp[])
QED

Theorem gas_shadow_compiles_make_array_elems:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es idx. gas_shadow_compiles
    (compile_make_array_elems f cenv es elem_ty elem_size has_lw buf_op idx)
    (compile_make_array_elems g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es)
      elem_ty elem_size has_lw buf_op idx)
Proof
  strip_tac >> Induct >>
  simp[compile_make_array_elems_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> gvs[compile_make_array_elems_def, comp_ignore_bind_def,
                       gas_shadow_lowered_value_type] >>
  rpt gen_tac >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_store_memory,
                gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >> simp[])
QED

Theorem gas_shadow_compiles_make_array:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (compile_make_array f cenv es elem_ty elem_size has_lw buf_op)
    (compile_make_array g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es)
      elem_ty elem_size has_lw buf_op)
Proof
  strip_tac >> Cases_on `sh` >> Cases_on `has_lw` >>
  simp[compile_make_array_def, comp_ignore_bind_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_return] >>
   gen_tac >> BETA_TAC >> drule gas_shadow_compiles_make_array_elems >>
   metis_tac[COND_CLAUSES])
QED

Theorem gas_shadow_compiles_concat_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es infos. gas_shadow_compiles (compile_concat f cenv es data_ptr infos off_ptr)
    (compile_concat g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es)
      data_ptr infos off_ptr)
Proof
  strip_tac >> Induct >>
  simp[compile_concat_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> gvs[] >> rpt gen_tac >>
  namedCases_on `infos` ["", "info more"] >>
  simp[compile_concat_def, gas_shadow_compiles_return] >>
  PairCases_on `info` >> Cases_on `info0` >>
  simp[compile_concat_def, comp_ignore_bind_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (drule gas_shadow_compiles_lower_value_env >> metis_tac[COND_CLAUSES]) >>
   gen_tac >> BETA_TAC >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void] >>
        gen_tac >> BETA_TAC) >> simp[])
QED

Theorem gas_shadow_compiles_attribute:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_attribute f cenv ret_ty ty base_e fld)
    (compile_attribute g (gas_shadow_env sd cenv) ret_ty ty
      (if sh then gas_shadow_expr base_e else base_e) fld)
Proof
  strip_tac >> Cases_on `sh` >> simp[compile_attribute_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >> gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >>
   simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_return])
QED

Theorem gas_shadow_self_addr:
  !e. is_self_addr (gas_shadow_expr e) <=> is_self_addr e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def,
                        vyperContextTheory.is_self_addr_def] >>
  Cases_on `b` >> simp[gas_shadow_builtin_def,
                        vyperContextTheory.is_self_addr_def] >>
  Cases_on `l` >> simp[gas_shadow_expr_def,
                        vyperContextTheory.is_self_addr_def] >>
  Cases_on `e` >> simp[gas_shadow_builtin_def,
                        vyperContextTheory.is_self_addr_def]
QED

Theorem gas_shadow_compiles_acc:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_acc f cenv addr_e item)
    (compile_acc g (gas_shadow_env sd cenv) (if sh then gas_shadow_expr addr_e else addr_e) item)
Proof
  strip_tac >> Cases_on `item` >>
  Cases_on `is_self_addr addr_e` >>
  `is_self_addr (if sh then gas_shadow_expr addr_e else addr_e) =
     is_self_addr addr_e` by
    (Cases_on `sh` >> simp[gas_shadow_self_addr]) >>
  simp[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_acc_def, GSYM comp_bind_def, GSYM comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  drule gas_shadow_compiles_lower_value_env >> strip_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_return, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_struct_lit:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !fields off. gas_shadow_compiles (compile_struct_lit f cenv ty fields buf_op off)
    (compile_struct_lit g (gas_shadow_env sd cenv) ty
      (if sh then MAP (I ## gas_shadow_expr) fields else fields) buf_op off)
Proof
  strip_tac >> Induct >>
  simp[compile_struct_lit_def, gas_shadow_compiles_return] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >>
  Cases_on `sh` >> gvs[compile_struct_lit_def, comp_ignore_bind_def,
                       gas_shadow_lowered_value_type] >>
  rpt gen_tac >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_store_memory,
                gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >> simp[])
QED

Theorem gas_shadow_compiles_create_salt:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_salt f cenv salt_e)
    (compile_create_salt g (gas_shadow_env sd cenv)
      (if sh then OPTION_MAP gas_shadow_expr salt_e else salt_e))
Proof
  strip_tac >> Cases_on `salt_e` >>
  simp[compile_create_salt_def, gas_shadow_compiles_return] >>
  Cases_on `sh` >> simp[compile_create_salt_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (drule gas_shadow_compiles_lower_value_env >> metis_tac[COND_CLAUSES]) >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_create_ctor_args:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es. gas_shadow_compiles (compile_create_ctor_args f cenv es)
    (compile_create_ctor_args g (gas_shadow_env sd cenv)
      (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> Cases_on `sh` >> simp[] >> Induct >>
  simp[compile_create_ctor_args_def, gas_shadow_compiles_return,
       gas_shadow_expr_can_mutate] >> gen_tac >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gas_shadow_compiles_snapshot_vv] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_ext_call_kwarg_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_ext_call_kwarg f cenv return_type k e)
    (compile_ext_call_kwarg g (gas_shadow_env sd cenv) return_type k
      (if sh then gas_shadow_expr e else e))
Proof
  strip_tac >> Cases_on `sh` >> Cases_on `k` >>
  Cases_on `is_word_type return_type` >>
  simp[compile_ext_call_kwarg_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (drule gas_shadow_compiles_lower_value_env >> metis_tac[COND_CLAUSES]) >>
   gen_tac >> BETA_TAC >> simp[gas_shadow_lowered_value_type] >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_materialize_vv] >> gen_tac >> BETA_TAC) >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_ext_call_kwargs_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !ks es. gas_shadow_compiles (compile_ext_call_kwargs f cenv return_type ks es)
    (compile_ext_call_kwargs g (gas_shadow_env sd cenv) return_type ks
      (if sh then MAP gas_shadow_expr es else es))
Proof
  strip_tac >> Induct >>
  simp[compile_ext_call_kwargs_def, gas_shadow_compiles_return] >>
  qx_gen_tac `kw` >> qx_gen_tac `es` >>
  namedCases_on `es` ["", "entry rest"] >>
  Cases_on `sh` >> gvs[compile_ext_call_kwargs_def, gas_shadow_compiles_return] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (drule gas_shadow_compiles_ext_call_kwarg_env >> metis_tac[COND_CLAUSES]) >>
   gen_tac >> pairarg_tac >> gvs[] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
   gen_tac >> pairarg_tac >> gvs[] >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_create_blueprint_args:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_blueprint_args f cenv raw_args later_es args)
    (compile_create_blueprint_args g (gas_shadow_env sd cenv) raw_args
      (if sh then MAP gas_shadow_expr later_es else later_es)
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_create_ctor_args f cenv args)
     (compile_create_ctor_args g (gas_shadow_env sd cenv)
       (if sh then MAP gas_shadow_expr args else args))`
    by (irule gas_shadow_compiles_create_ctor_args >> simp[]) >>
  Cases_on `sh` >> Cases_on `raw_args` >>
  namedCases_on `args` ["", "entry rest"] >>
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_return] >>
  namedCases_on `rest` ["", "next more"] >>
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def,
       MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss,
       gas_shadow_lowered_value_type, gas_shadow_expr_can_mutate,
       gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (simp[gas_shadow_compiles_snapshot_vv, gas_shadow_compiles_unwrap_value,
                gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_op,
                gas_shadow_compiles_abi_encode_values_to_buf] >>
           fs[FORALL_BOOL, MAP]) >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_raw_create:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_raw_create f cenv bytecode_e value_e ctor_args salt_e rof)
    (compile_raw_create g (gas_shadow_env sd cenv)
      (if sh then gas_shadow_expr bytecode_e else bytecode_e)
      (if sh then gas_shadow_expr value_e else value_e)
      (if sh then MAP gas_shadow_expr ctor_args else ctor_args)
      (if sh then OPTION_MAP gas_shadow_expr salt_e else salt_e) rof)
Proof
  strip_tac >>
  drule gas_shadow_compiles_lower_value_env >> strip_tac >>
  drule gas_shadow_compiles_create_ctor_args >> strip_tac >>
  drule gas_shadow_compiles_create_salt >> strip_tac >>
  Cases_on `sh` >> Cases_on `ctor_args = []` >>
  gvs[compile_raw_create_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss,
      comp_ignore_bind_def, gas_shadow_lowered_value_type] >>
  (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (simp[gas_shadow_compiles_create_snapshot, gas_shadow_compiles_emit_op] >>
           fs[FORALL_BOOL]) >> gen_tac >> BETA_TAC) >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- (simp[gas_shadow_compiles_alloc_buffer,
                    gas_shadow_compiles_copy_memory_dynamic,
                    gas_shadow_compiles_emit_op,
                    gas_shadow_compiles_abi_encode_values_to_buf] >>
               fs[FORALL_BOOL]) >> gen_tac >> BETA_TAC) >>
      simp[gas_shadow_compiles_return]) >>
  gen_tac >> pairarg_tac >> gvs[] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[COND_CLAUSES] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[COND_CLAUSES] >>
  simp[gas_shadow_compiles_create_dispatch])
QED


Theorem gas_shadow_compiles_create_proxy_call[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_call f cenv CreateMinimalProxy has_salt rof args)
    (compile_create_call g (gas_shadow_env sd cenv) CreateMinimalProxy has_salt rof
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `!cenv ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!cenv salt. gas_shadow_compiles (compile_create_salt f cenv salt)
     (compile_create_salt g (gas_shadow_env sd cenv) (if sh then OPTION_MAP gas_shadow_expr salt else salt))`
    by (rpt gen_tac >> irule gas_shadow_compiles_create_salt >> simp[]) >>
  qpat_assum `!cenv salt. gas_shadow_compiles (compile_create_salt f cenv salt) _` (qspecl_then [`cenv`, `NONE`] mp_tac) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!salt_e. gas_shadow_compiles (compile_create_salt f cenv (SOME salt_e))
     (compile_create_salt g (gas_shadow_env sd cenv) (SOME (if sh then gas_shadow_expr salt_e else salt_e)))`
    by (gen_tac >> qpat_assum `!cenv salt. gas_shadow_compiles (compile_create_salt f cenv salt) _`
          (qspecl_then [`cenv`, `SOME salt_e`] mp_tac) >> Cases_on `sh` >> simp[NoAsms]) >>
  namedCases_on `args` ["", "target_e tail"]
  >- simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return] >>
  namedCases_on `tail` ["", "value_e rest"]
  >- (Cases_on `sh` >> simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return]) >>
  namedCases_on `rest` ["", "salt_e more"] >>
  Cases_on `sh` >> Cases_on `has_salt` >>
  gvs[compile_create_call_def, comp_ignore_bind_def,
      gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
      gas_shadow_compiles_return] >>
  (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- (simp[gas_shadow_compiles_create_proxy_buf] >> NO_TAC) >>
        gen_tac >> BETA_TAC) >>
   simp[gas_shadow_compiles_create_dispatch])
QED

Theorem gas_shadow_compiles_create_copy_call[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_call f cenv CreateCopyOf has_salt rof args)
    (compile_create_call g (gas_shadow_env sd cenv) CreateCopyOf has_salt rof
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `!cenv ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!salt. gas_shadow_compiles (compile_create_salt f cenv salt)
     (compile_create_salt g (gas_shadow_env sd cenv) (if sh then OPTION_MAP gas_shadow_expr salt else salt))`
    by (gen_tac >> irule gas_shadow_compiles_create_salt >> simp[]) >>
  qpat_assum `!salt. gas_shadow_compiles (compile_create_salt f cenv salt) _`
    (qspec_then `NONE` mp_tac) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!salt_e. gas_shadow_compiles (compile_create_salt f cenv (SOME salt_e))
     (compile_create_salt g (gas_shadow_env sd cenv) (SOME (if sh then gas_shadow_expr salt_e else salt_e)))`
    by (gen_tac >> qpat_assum `!salt. gas_shadow_compiles (compile_create_salt f cenv salt) _`
          (qspec_then `SOME salt_e` mp_tac) >> Cases_on `sh` >> simp[NoAsms]) >>
  namedCases_on `args` ["", "target_e tail"]
  >- simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return] >>
  namedCases_on `tail` ["", "value_e rest"]
  >- (Cases_on `sh` >> simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return]) >>
  namedCases_on `rest` ["", "salt_e more"] >>
  Cases_on `sh` >> Cases_on `has_salt` >>
  gvs[compile_create_call_def, comp_ignore_bind_def,
      gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
      gas_shadow_compiles_return] >>
  (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- (simp[] >> NO_TAC) >> gen_tac >> BETA_TAC) >>
   simp[gas_shadow_compiles_create_copy])
QED

Theorem gas_shadow_compiles_raw_create_call[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_call f cenv RawCreate has_salt rof args)
    (compile_create_call g (gas_shadow_env sd cenv) RawCreate has_salt rof
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `!be ve es salt. gas_shadow_compiles (compile_raw_create f cenv be ve es salt rof)
     (compile_raw_create g (gas_shadow_env sd cenv)
       (if sh then gas_shadow_expr be else be)
       (if sh then gas_shadow_expr ve else ve)
       (if sh then MAP gas_shadow_expr es else es)
       (if sh then OPTION_MAP gas_shadow_expr salt else salt) rof)`
    by (rpt gen_tac >> irule gas_shadow_compiles_raw_create >> simp[]) >>
  namedCases_on `args` ["", "target_e tail"]
  >- simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return] >>
  namedCases_on `tail` ["", "value_e rest"]
  >- (Cases_on `sh` >> simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return]) >>
  Cases_on `has_salt`
  >- (namedCases_on `rest` ["", "salt_e more"] >>
      Cases_on `sh` >>
      gvs[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return, MAP_FRONT, LAST_MAP] >>
      qpat_assum `!be ve es salt. gas_shadow_compiles (compile_raw_create f cenv be ve es salt rof) _`
        (qspecl_then [`target_e`, `value_e`, `FRONT (salt_e::more)`,
                      `SOME (LAST (salt_e::more))`] mp_tac) >>
      simp[NoAsms, MAP_FRONT] >>
      once_rewrite_tac[GSYM MAP] >> simp[NoAsms, LAST_MAP]) >>
  qpat_assum `!be ve es salt. gas_shadow_compiles (compile_raw_create f cenv be ve es salt rof) _`
    (qspecl_then [`target_e`, `value_e`, `rest`, `NONE`] mp_tac) >>
  Cases_on `sh` >> simp[NoAsms, compile_create_call_def]
QED

Theorem gas_shadow_pin_literal_values[local]:
  !es. pin_literal_values (MAP gas_shadow_expr es) = pin_literal_values es
Proof
  Induct >> simp[pin_literal_values_def] >>
  Cases_on `h` >> simp[gas_shadow_expr_def, pin_literal_values_def]
QED

Theorem gas_shadow_pin_fold_result[local]:
  gas_shadow_expr (pin_fold_result ty e result) =
    pin_fold_result ty (gas_shadow_expr e) result
Proof
  Cases_on `result` >> simp[pin_fold_result_def] >>
  CASE_TAC >> simp[gas_shadow_expr_def]
QED

Theorem pin_fold_builtin_non_len[local]:
  bi <> Len ==>
  pin_fold_builtin (BaseT bt) bi es =
    if ~pin_foldable_builtin bi \/
       ~builtin_args_length_ok bi (LENGTH es) \/
       ~EVERY (\e. ?t. expr_type e = BaseT t) es
    then Builtin (BaseT bt) bi es
    else case pin_literal_values es of
         | NONE => Builtin (BaseT bt) bi es
         | SOME vs => pin_fold_result (BaseT bt) (Builtin (BaseT bt) bi es)
             (evaluate_builtin empty_evaluation_context empty_accounts
               (BaseT bt) bi (MAP expr_type es) vs)
Proof
  Cases_on `bi` >> simp[pin_fold_builtin_def] >>
  Cases_on `es` >> simp[]
QED

Theorem gas_shadow_pin_fold_builtin[local]:
  gas_shadow_expr (pin_fold_builtin ty bi es) =
    pin_fold_builtin ty (gas_shadow_builtin bi) (MAP gas_shadow_expr es)
Proof
  reverse (Cases_on `?bt. ty = BaseT bt`)
  >- (Cases_on `ty` >> gvs[pin_fold_builtin_def, gas_shadow_expr_def]) >>
  gvs[] >>
  Cases_on `bi = Len`
  >- (gvs[gas_shadow_builtin_def] >> Cases_on `es`
      >- simp[pin_fold_builtin_def, pin_foldable_builtin_def,
              gas_shadow_expr_def, gas_shadow_builtin_def] >>
      rename1 `h::rest` >> Cases_on `rest`
      >- (Cases_on `h` >> simp[pin_fold_builtin_def, pin_foldable_builtin_def,
                              gas_shadow_expr_def, gas_shadow_builtin_def] >>
          rename1 `Literal _ l` >> Cases_on `l` >>
          simp[pin_fold_builtin_def, pin_foldable_builtin_def,
               gas_shadow_expr_def, gas_shadow_builtin_def]) >>
      simp[pin_fold_builtin_def, pin_foldable_builtin_def,
           gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  Cases_on `bi = Env MsgGas`
  >- simp[pin_fold_builtin_non_len, pin_foldable_builtin_def,
          gas_shadow_expr_def, gas_shadow_builtin_def] >>
  simp[gas_shadow_builtin_def, pin_fold_builtin_non_len,
       gas_shadow_pin_literal_values, EXISTS_MAP, MAP_MAP_o,
       combinTheory.o_DEF, ETA_THM] >>
  IF_CASES_TAC >> Cases_on `pin_literal_values es` >>
  simp[gas_shadow_pin_fold_result, gas_shadow_expr_def, gas_shadow_builtin_def]
QED

Theorem gas_shadow_origin_fold_not[local]:
  gas_shadow_expr (origin_fold_builtin ty Not es) =
    origin_fold_builtin ty Not (MAP gas_shadow_expr es)
Proof
  namedCases_on `es` ["", "first_arg rest_args"]
  >- simp[origin_fold_builtin_def, gas_shadow_expr_def, gas_shadow_builtin_def] >>
  Cases_on `first_arg` >> Cases_on `rest_args` >>
  simp[origin_fold_builtin_def, gas_shadow_expr_def, gas_shadow_builtin_def,
       gas_shadow_pin_fold_builtin] >>
  BasicProvers.every_case_tac >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin]
QED

Theorem gas_shadow_origin_fold_bop[local]:
  gas_shadow_expr (origin_fold_builtin ty (Bop bop) es) =
    origin_fold_builtin ty (Bop bop) (MAP gas_shadow_expr es)
Proof
  Cases_on `bop` >>
  simp[origin_fold_builtin_def, gas_shadow_expr_def, gas_shadow_builtin_def,
       gas_shadow_pin_fold_builtin] >>
  namedCases_on `es` ["", "first_arg rest_args"] >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin] >>
  Cases_on `first_arg` >> Cases_on `rest_args` >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin]
QED

Theorem gas_shadow_origin_fold_builtin[local]:
  gas_shadow_expr (origin_fold_builtin ty bi es) =
    origin_fold_builtin ty (gas_shadow_builtin bi) (MAP gas_shadow_expr es)
Proof
  Cases_on `bi = Not`
  >- gvs[gas_shadow_origin_fold_not, gas_shadow_builtin_def] >>
  Cases_on `?bop. bi = Bop bop`
  >- gvs[gas_shadow_origin_fold_bop, gas_shadow_builtin_def] >>
  Cases_on `?item. bi = Env item`
  >- (gvs[origin_fold_builtin_def, gas_shadow_builtin_def] >>
      IF_CASES_TAC >>
      gvs[origin_fold_builtin_def, gas_shadow_pin_fold_builtin,
          gas_shadow_builtin_def]) >>
  Cases_on `bi` >>
  gvs[origin_fold_builtin_def, gas_shadow_builtin_def, gas_shadow_pin_fold_builtin]
QED

Theorem gas_shadow_origin_fold_value:
  (!e. origin_fold_value (gas_shadow_expr e) =
       gas_shadow_expr (origin_fold_value e)) /\
  (!es. origin_fold_values (MAP gas_shadow_expr es) =
        MAP gas_shadow_expr (origin_fold_values es))
Proof
  ho_match_mp_tac origin_fold_value_ind >>
  rw[origin_fold_value_def, gas_shadow_expr_def,
     GSYM gas_shadow_origin_fold_builtin] >>
  simp[vyperPinFoldTheory.pin_fold_expr_def, gas_shadow_expr_def,
       gas_shadow_pin_fold_result]
QED

Theorem gas_shadow_origin_int_literal[local]:
  is_int_literal (origin_fold_value (gas_shadow_expr e)) =
    is_int_literal (origin_fold_value e)
Proof
  simp[gas_shadow_origin_fold_value] >>
  Cases_on `origin_fold_value e` >>
  simp[gas_shadow_expr_def, is_int_literal_def]
QED

Theorem gas_shadow_compiles_blueprint_offset[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles
    (case origin_fold_value e of
       Literal _ (IntL i) => comp_return (Lit (i2w i))
     | _ => lower_value f cenv (expr_type e) e)
    (case origin_fold_value (if sh then gas_shadow_expr e else e) of
       Literal _ (IntL i) => comp_return (Lit (i2w i))
     | _ => lower_value g (gas_shadow_env sd cenv)
              (expr_type (if sh then gas_shadow_expr e else e))
              (if sh then gas_shadow_expr e else e))
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_value f cenv (expr_type e) e)
     (lower_value g (gas_shadow_env sd cenv) (expr_type e)
       (if sh then gas_shadow_expr e else e))`
    by (irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  Cases_on `sh` >>
  simp[gas_shadow_origin_fold_value] >>
  Cases_on `origin_fold_value e` >>
  simp[gas_shadow_expr_def, gas_shadow_compiles_return,
       gas_shadow_compiles_lower_value_env] >>
  BasicProvers.every_case_tac >>
  gvs[gas_shadow_expr_def, gas_shadow_compiles_return,
      gas_shadow_compiles_lower_value_env]
QED

Theorem gas_shadow_compiles_blueprint_call[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_call f cenv (CreateFromBlueprint raw_args) has_salt rof args)
    (compile_create_call g (gas_shadow_env sd cenv) (CreateFromBlueprint raw_args) has_salt rof
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >>
  `!cenv ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!later_es es. gas_shadow_compiles
     (compile_create_blueprint_args f cenv raw_args later_es es)
     (compile_create_blueprint_args g (gas_shadow_env sd cenv) raw_args
       (if sh then MAP gas_shadow_expr later_es else later_es)
       (if sh then MAP gas_shadow_expr es else es))`
    by (rpt gen_tac >> irule gas_shadow_compiles_create_blueprint_args >> simp[]) >>
  `!salt. gas_shadow_compiles (compile_create_salt f cenv salt)
     (compile_create_salt g (gas_shadow_env sd cenv) (if sh then OPTION_MAP gas_shadow_expr salt else salt))`
    by (gen_tac >> irule gas_shadow_compiles_create_salt >> simp[]) >>
  qpat_assum `!salt. gas_shadow_compiles (compile_create_salt f cenv salt) _`
    (qspec_then `NONE` mp_tac) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!salt_e. gas_shadow_compiles (compile_create_salt f cenv (SOME salt_e))
     (compile_create_salt g (gas_shadow_env sd cenv) (SOME (if sh then gas_shadow_expr salt_e else salt_e)))`
    by (gen_tac >> qpat_assum `!salt. gas_shadow_compiles (compile_create_salt f cenv salt) _`
          (qspec_then `SOME salt_e` mp_tac) >> Cases_on `sh` >> simp[NoAsms]) >>
  namedCases_on `args` ["", "target_e tail"]
  >- simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return] >>
  namedCases_on `tail` ["", "value_e rest"]
  >- (Cases_on `sh` >> simp[compile_create_call_def, comp_ignore_bind_def,
          gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
          gas_shadow_compiles_return]) >>
  namedCases_on `rest` ["", "first_e more"]
  >- (Cases_on `sh` >> Cases_on `has_salt` >>
      simp[compile_create_call_def, comp_ignore_bind_def,
           gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
           gas_shadow_compiles_return]) >>
  namedCases_on `more` ["", "next_e suffix"] >>
  Cases_on `sh` >> Cases_on `has_salt` >>
  gvs[compile_create_call_def, comp_ignore_bind_def,
      gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
      gas_shadow_compiles_return, gas_shadow_origin_int_literal] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (qpat_x_assum `!later_es es. gas_shadow_compiles
         (compile_create_blueprint_args f cenv raw_args later_es es) _`
         mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[MAP]) >>
   gen_tac >> pairarg_tac >> gvs[] >>
   ntac 4 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_create_blueprint_check,
                SIMP_RULE (srw_ss()) []
                  (Q.INST [`sh` |-> `T`] gas_shadow_compiles_blueprint_offset),
                SIMP_RULE (srw_ss()) []
                  (Q.INST [`sh` |-> `F`] gas_shadow_compiles_blueprint_offset)] >>
        gen_tac >> BETA_TAC) >>
   simp[gas_shadow_compiles_create_blueprint_append])
QED

Theorem gas_shadow_compiles_create_call:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_create_call f cenv ck has_salt rof args)
    (compile_create_call g (gas_shadow_env sd cenv) ck has_salt rof
      (if sh then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> Cases_on `ck`
  >- (irule gas_shadow_compiles_create_proxy_call >> simp[])
  >- (irule gas_shadow_compiles_create_copy_call >> simp[])
  >- (irule gas_shadow_compiles_blueprint_call >> simp[]) >>
  irule gas_shadow_compiles_raw_create_call >> simp[]
QED

Theorem gas_shadow_compiles_extcall_store_args:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !es tys offset. gas_shadow_compiles (compile_extcall_store_args f cenv es tys buf_op offset)
    (compile_extcall_store_args g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es)
      tys buf_op offset)
Proof
  strip_tac >>
  `!ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  Induct >> simp[compile_extcall_store_args_def, gas_shadow_compiles_return] >>
  qx_gen_tac `entry` >> qx_gen_tac `tys` >> qx_gen_tac `offset` >>
  namedCases_on `tys` ["", "ty rest_tys"] >> Cases_on `sh` >>
  Cases_on `offset = 0` >>
  gvs[compile_extcall_store_args_def, comp_ignore_bind_def] >>
  (ntac 2 (match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_op] >>
           gen_tac >> BETA_TAC) >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (rpt IF_CASES_TAC >>
       simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_store_bytestring]) >> simp[])
QED

Theorem gas_shadow_literal_int_index[local]:
  literal_int_index (gas_shadow_expr e) = literal_int_index e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, literal_int_index_def]
QED

Theorem gas_shadow_compiles_subscript:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_subscript f cenv ret_ty ty base_e idx_e)
    (compile_subscript g (gas_shadow_env sd cenv) ret_ty ty
      (if sh then gas_shadow_expr base_e else base_e)
      (if sh then gas_shadow_expr idx_e else idx_e))
Proof
  strip_tac >>
  `!ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  Cases_on `sh` >> gvs[compile_subscript_def, copies_subscript_base_def,
                       gas_shadow_literal_int_index] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (IF_CASES_TAC >>
       simp[gas_shadow_compiles_snapshot_vv, gas_shadow_compiles_return]) >>
   gen_tac >> BETA_TAC >>
   Cases_on `place_type cenv base_e`
   >- (simp[] >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC >>
       Cases_on `is_bytestring_type t` >>
       simp[gas_shadow_compiles_bind, gas_shadow_compiles_keccak256_key,
            gas_shadow_compiles_mapping_subscript, gas_shadow_compiles_return]) >>
   rename1 `place_type cenv base_e = ValPT base_ty` >>
   Cases_on `base_ty` >> simp[gas_shadow_literal_int_index] >>
   (rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
         >- (simp[gas_shadow_compiles_tuple_subscript,
                  gas_shadow_compiles_array_subscript, gas_shadow_compiles_ptr_load] >> NO_TAC) >>
         gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]))
QED

Theorem gas_shadow_compiles_get_target_ptr_env:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  !target cenv sh. gas_shadow_compiles (compile_get_target_ptr f cenv target)
    (compile_get_target_ptr g (gas_shadow_env sd cenv) (if sh then gas_shadow_target target else target))
Proof
  strip_tac >>
  `(!e:expr. T) /\ !target cenv sh.
     gas_shadow_compiles (compile_get_target_ptr f cenv target)
       (compile_get_target_ptr g (gas_shadow_env sd cenv) (if sh then gas_shadow_target target else target))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[] >>
  rpt conj_tac
  >- (rpt gen_tac >> Cases_on `sh` >> simp[compile_get_target_ptr_def, gas_shadow_expr_def] >>
      qmatch_goalsub_abbrev_tac `FLOOKUP vars ident` >>
      namedCases_on `FLOOKUP vars ident` ["", "vloc"] >> simp[gas_shadow_compiles_return] >>
      Cases_on `vloc` >> simp[gas_shadow_compiles_return])
  >- (rpt gen_tac >> Cases_on `sh` >> simp[compile_get_target_ptr_def, gas_shadow_expr_def] >>
      qmatch_goalsub_abbrev_tac `FLOOKUP vars ident` >>
      namedCases_on `FLOOKUP vars ident` ["", "vloc"] >> simp[gas_shadow_compiles_return] >>
      Cases_on `vloc` >> simp[gas_shadow_compiles_return])
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume gas_shadow_compiles_get_target_ptr_env[attribute]:
  rpt strip_tac >> Cases_on `sh` >> gvs[gas_shadow_expr_def, compile_get_target_ptr_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac >- metis_tac[COND_CLAUSES] >>
   gen_tac >> BETA_TAC >> simp[gas_shadow_compiles_bind,
                               gas_shadow_compiles_emit_op, gas_shadow_compiles_return])
QED

Resume gas_shadow_compiles_get_target_ptr_env[subscript]:
  rpt strip_tac >>
  `!ty e. gas_shadow_compiles (lower_value f cenv ty e)
     (lower_value g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  Cases_on `sh` >> gvs[gas_shadow_expr_def, compile_get_target_ptr_def] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac >- metis_tac[COND_CLAUSES] >>
   qx_gen_tac `result` >> BETA_TAC >>
   qpat_x_assum `!cenv sh. gas_shadow_compiles (compile_get_target_ptr f cenv target) _` kall_tac >>
   namedCases_on `SND (SND result)` ["", "pt"]
   >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_array_subscript,
            gas_shadow_compiles_ptr_load, gas_shadow_compiles_return] >>
   Cases_on `pt` >> simp[] >>
   rpt IF_CASES_TAC >>
   simp[gas_shadow_compiles_bind, gas_shadow_compiles_array_subscript,
        gas_shadow_compiles_ptr_load, gas_shadow_compiles_keccak256_key,
        gas_shadow_compiles_mapping_subscript, gas_shadow_compiles_return] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
   gen_tac >> BETA_TAC >>
   qmatch_goalsub_abbrev_tac `is_bytestring_type key_ty` >>
   Cases_on `is_bytestring_type key_ty` >>
   simp[gas_shadow_compiles_bind, gas_shadow_compiles_keccak256_key,
        gas_shadow_compiles_mapping_subscript, gas_shadow_compiles_return])
QED

Finalise gas_shadow_compiles_get_target_ptr_env

(* The shadow environment's defaults are the callee's shadowed defaults, and
   dropping a callee's own defaults commutes with shadowing them. *)
Theorem gas_shadow_env_without_defaults:
  cenv_without_defaults (gas_shadow_env sd cenv) name =
    gas_shadow_env sd (cenv_without_defaults cenv name)
Proof
  rw[cenv_without_defaults_def, gasShadowCompileBaseTheory.gas_shadow_env_def,
     compile_env_component_equality, rich_listTheory.FILTER_MAP,
     combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem gas_shadow_env_omitted_defaults:
  omitted_defaults (gas_shadow_env sd cenv) name n =
    if sd then MAP gas_shadow_expr (omitted_defaults cenv name n)
    else omitted_defaults cenv name n
Proof
  `ALOOKUP (MAP (I ## MAP gas_shadow_expr) cenv.ce_func_defaults) name =
   OPTION_MAP (MAP gas_shadow_expr) (ALOOKUP cenv.ce_func_defaults name)`
    by (qspec_tac (`cenv.ce_func_defaults`, `l`) >> Induct >>
        simp[pairTheory.FORALL_PROD] >> rw[]) >>
  rw[omitted_defaults_def, gas_shadow_env_defaults] >>
  Cases_on `ALOOKUP cenv.ce_func_defaults name` >> simp[MAP_DROP]
QED

Theorem gas_shadow_compiles_call_int[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty (IntCall fid) args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty (IntCall fid)
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!es flags tys. gas_shadow_compiles (compile_stage_intcall_args f cenv es flags tys)
    (compile_stage_intcall_args g (gas_shadow_env sd cenv)
       (if sh then MAP gas_shadow_expr es else es) flags tys)`
    by (irule gas_shadow_compiles_stage_intcall_args_env >> gs[]) >>
  `!ce es flags tys. gas_shadow_compiles
    (compile_stage_intcall_args f ce es flags tys)
    (compile_stage_intcall_args g (gas_shadow_env sd ce)
       (if sd then MAP gas_shadow_expr es else es) flags tys)`
    by (rpt gen_tac >> irule gas_shadow_compiles_stage_intcall_args_env >> gs[]) >>
  qabbrev_tac `info = cenv.ce_func_info (nsid_to_string fid)` >>
  PairCases_on `info` >> fs[markerTheory.Abbrev_def] >>
  qpat_x_assum `_ = cenv.ce_func_info _` (assume_tac o SYM) >>
  Cases_on `sh` >> Cases_on `sd` >>
  gvs[gas_shadow_env_omitted_defaults, gas_shadow_env_without_defaults] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, MAP_MAP_o, combinTheory.o_DEF,
       gas_shadow_env_omitted_defaults, gas_shadow_env_without_defaults,
       GSYM comp_bind_def, GSYM comp_return_def, gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (Cases_on `info0 > 0` >> Cases_on `info1 > 0` >>
       simp[SF ETA_ss, gas_shadow_compiles_return] >>
       match_mp_tac gas_shadow_compiles_bind >>
       simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return]) >>
   qx_gen_tac `rbuf_opt` >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[] >>
   qx_gen_tac `supplied_ops` >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[] >>
   qx_gen_tac `default_ops` >> BETA_TAC >>
   Cases_on `rbuf_opt` >> Cases_on `info0 > 0` >>
   simp[GSYM comp_bind_def, GSYM comp_return_def, SF ETA_ss] >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gas_shadow_compiles_emit_op, gasShadowCompileEmitTheory.gas_shadow_compiles_emit_multi_op,
                gas_shadow_compiles_emit_void, gas_shadow_compiles_store_multi_results] >>
        gen_tac >> BETA_TAC) >>
   simp[gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_call_ext[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty (ExtCall stat skip sig opts) args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty (ExtCall stat skip sig opts)
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!kw tys es. gas_shadow_compiles (compile_ext_call_args f cenv kw tys es)
    (compile_ext_call_args g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr kw else kw) tys
       (if sh then MAP gas_shadow_expr es else es))`
    by (rpt gen_tac >> irule gas_shadow_compiles_ext_call_args >> simp[]) >>
  `!t ks es. gas_shadow_compiles (compile_ext_call_kwargs f cenv t ks es)
    (compile_ext_call_kwargs g (gas_shadow_env sd cenv) t ks (if sh then MAP gas_shadow_expr es else es))`
    by (rpt gen_tac >> irule gas_shadow_compiles_ext_call_kwargs_env >> simp[]) >>
  PairCases_on `sig` >> Cases_on `args` >> Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry, GSYM MAP_TAKE, GSYM MAP_DROP,
       MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return] >>
  (pairarg_tac >> gvs[] >> pairarg_tac >> gvs[AllCaseEqs()] >>
   simp[GSYM comp_bind_def, GSYM comp_return_def,
        gasShadowCompileBaseTheory.comp_bind_uncurry] >>
   (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- (Cases_on `gas_opt` >>
        simp[SF ETA_ss, gas_shadow_compiles_emit_op, gas_shadow_compiles_return]) >>
    gen_tac >> BETA_TAC >>
    match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- simp[SF ETA_ss, MAP_MAP_o, combinTheory.o_DEF,
            gasShadowCompileExternalTheory.gas_shadow_compiles_external_call_kwargs] >>
    gen_tac >> BETA_TAC >>
    qmatch_goalsub_abbrev_tac `if no_return then _ else _` >>
    Cases_on `no_return` >> simp[SF ETA_ss, gas_shadow_compiles_return]))
QED

Theorem gas_shadow_compiles_call_send:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty (Send has_gas) args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty (Send has_gas)
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  let val finish =
  Cases_on `has_gas` >> Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
  in
    namedCases_on `args` ["", "addr rest"] >- finish >>
    namedCases_on `rest` ["", "value gas_es"] >- finish >>
    namedCases_on `gas_es` ["", "gas gas_tail"] >- finish >>
    namedCases_on `gas_tail` ["", "extra extras"] >> finish
  end
QED

Theorem gas_shadow_compiles_call_raw[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty (RawCallTarget rcf) args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty (RawCallTarget rcf)
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!t ks es. gas_shadow_compiles (compile_ext_call_kwargs f cenv t ks es)
    (compile_ext_call_kwargs g (gas_shadow_env sd cenv) t ks (if sh then MAP gas_shadow_expr es else es))`
    by (rpt gen_tac >> irule gas_shadow_compiles_ext_call_kwargs_env >> simp[]) >>
  let val invalid =
    Cases_on `sh` >>
    CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
    simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    match_mp_tac gas_shadow_compiles_bind >>
    simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_return]
  in
    namedCases_on `args` ["", "addr rest"] >- invalid >>
    namedCases_on `rest` ["", "data kws"] >- invalid
  end >>
  Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op] >> gen_tac >> BETA_TAC) >>
  pairarg_tac >> gvs[] >>
  simp[gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  (match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (Cases_on `gas_opt` >>
       simp[SF ETA_ss, gas_shadow_compiles_emit_op, gas_shadow_compiles_return]) >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_raw_call_outbuf] >>
   gen_tac >> pairarg_tac >> gvs[] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_raw_call_finish] >>
   gen_tac >> BETA_TAC >> Cases_on `rcf.rcf_max_outsize = 0` >>
   simp[SF ETA_ss, gas_shadow_compiles_return])
QED

Theorem gas_shadow_compiles_call_raw_calldata[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty (RawCallCalldataTarget rcf) args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty (RawCallCalldataTarget rcf)
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!t ks es. gas_shadow_compiles (compile_ext_call_kwargs f cenv t ks es)
    (compile_ext_call_kwargs g (gas_shadow_env sd cenv) t ks (if sh then MAP gas_shadow_expr es else es))`
    by (rpt gen_tac >> irule gas_shadow_compiles_ext_call_kwargs_env >> simp[]) >>
  Cases_on `args` >> Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return] >>
  (pairarg_tac >> gvs[] >> simp[gasShadowCompileBaseTheory.comp_bind_uncurry] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (Cases_on `gas_opt` >>
       simp[SF ETA_ss, gas_shadow_compiles_emit_op, gas_shadow_compiles_return]) >>
   gen_tac >> BETA_TAC >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_raw_call_outbuf] >>
   gen_tac >> pairarg_tac >> gvs[] >>
   match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_msg_data_to_memory] >>
   gen_tac >> pairarg_tac >> gvs[] >>
   rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
        >- simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_raw_call_finish,
                gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
   Cases_on `rcf.rcf_max_outsize = 0` >>
   simp[SF ETA_ss, gas_shadow_compiles_return])
QED

Theorem gas_shadow_raw_log_topic_exprs[local]:
  raw_log_topic_exprs (gas_shadow_expr e) =
  MAP gas_shadow_expr (raw_log_topic_exprs e)
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, raw_log_topic_exprs_def] >>
  rename1 `MAP gas_shadow_expr (raw_log_topic_exprs (Builtin _ bi _))` >>
  Cases_on `bi` >>
  rw[gas_shadow_builtin_def, raw_log_topic_exprs_def]
QED

Theorem gas_shadow_compiles_call_raw_log[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty RawLog args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty RawLog
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  `!es. gas_shadow_compiles (compile_multi_exprs f cenv es)
    (compile_multi_exprs g (gas_shadow_env sd cenv) (if sh then MAP gas_shadow_expr es else es))`
    by (gen_tac >> irule gas_shadow_compiles_multi_exprs_env >> simp[]) >>
  let val finish =
  Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry,
       gas_shadow_raw_log_topic_exprs] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
  in
    namedCases_on `args` ["", "topics_e rest"] >- finish >>
    namedCases_on `rest` ["", "data_e tail"] >- finish >>
    reverse (Cases_on `tail`) >- finish >>
    Cases_on `expr_type data_e = BaseT (BytesT (Fixed 32))` >> finish
  end
QED

Theorem gas_shadow_compiles_call_raw_revert[local]:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty RawRevert args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty RawRevert
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  let val finish =
  Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst,
               gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_raw_revert,
               gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
  in
    namedCases_on `args` ["", "data_e rest"] >- finish >>
    Cases_on `rest` >> finish
  end
QED

Theorem gas_shadow_compiles_call:
  (!cenv ty e sh. gas_shadow_compiles (f cenv ty e)
    (g (gas_shadow_env sd cenv) ty (if sh then gas_shadow_expr e else e))) ==>
  gas_shadow_compiles (compile_call f cenv ret_ty ty target args fallback)
    (compile_call g (gas_shadow_env sd cenv) ret_ty ty target
      (if sh then MAP gas_shadow_expr args else args)
      (if sh then OPTION_MAP gas_shadow_expr fallback else fallback))
Proof
  strip_tac >>
  Cases_on `target`
  >- (irule gas_shadow_compiles_call_int >> simp[])
  >- (irule gas_shadow_compiles_call_ext >> simp[])
  >- (irule gas_shadow_compiles_call_send >> simp[])
  >- (irule gas_shadow_compiles_call_raw >> simp[])
  >- (irule gas_shadow_compiles_call_raw_calldata >> simp[])
  >- (irule gas_shadow_compiles_call_raw_log >> simp[])
  >- (irule gas_shadow_compiles_call_raw_revert >> simp[])
  >- suspend "selfdestruct" >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >>
  irule gasShadowCompileNamesTheory.gas_shadow_compiles_as_stack_val >>
  irule gas_shadow_compiles_create_call >> simp[]
QED

Resume gas_shadow_compiles_call[selfdestruct]:
  `!t e. gas_shadow_compiles (lower_value f cenv t e)
    (lower_value g (gas_shadow_env sd cenv) t (if sh then gas_shadow_expr e else e))`
    by (rpt gen_tac >> irule gas_shadow_compiles_lower_value_env >> simp[]) >>
  namedCases_on `args` ["", "to_e rest"]
  >- (Cases_on `sh` >> gvs[] >>
      CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      match_mp_tac gas_shadow_compiles_bind >>
      simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_return]) >>
  Cases_on `rest` >> Cases_on `sh` >> gvs[] >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def, GSYM comp_bind_def, GSYM comp_return_def,
       gasShadowCompileBaseTheory.comp_bind_uncurry] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >>
       gen_tac >> BETA_TAC) >>
  simp[gasShadowCompileBuiltinSystemTheory.gas_shadow_compiles_selfdestruct,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_inst]
QED

Finalise gas_shadow_compiles_call

(* The same-environment forms. *)
Theorem gas_shadow_compiles_lower_value =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_lower_value_env)

Theorem gas_shadow_compiles_multi_exprs =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_multi_exprs_env)

Theorem gas_shadow_compiles_abi_encode_args =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_abi_encode_args_env)

Theorem gas_shadow_compiles_concat =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_concat_env)

Theorem gas_shadow_compiles_ext_call_kwarg =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_ext_call_kwarg_env)

Theorem gas_shadow_compiles_ext_call_kwargs =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_ext_call_kwargs_env)

Theorem gas_shadow_compiles_get_target_ptr =
  REWRITE_RULE [gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_compiles_get_target_ptr_env)

