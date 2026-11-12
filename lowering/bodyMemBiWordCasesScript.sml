(* Typed memory cases for arithmetic word builtins. *)
Theory bodyMemBiWordCases
Ancestors
  bodyMemBiWordCompose bodyMemBiWordFrag exprSimWordBuiltins bodyArgsMemory
  exprSimHypsDefs exprSimDefs exprSimWordArgs exprSimMemDefs
  exprLowering exprBopLowering freshWrites
  vyperTypeSystem vyperTyping vyperValue vyperInterpreter
  compileEnv list rich_list vyperContext

Theorem compile_pow_mod256_typed_sim_mem:
  !ctx func cenv cx env ty ann a b es.
    expr_body_pre cenv cx env (Builtin ann PowMod256 [a; b]) es /\
    (!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [a; b]) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann PowMod256 [a; b]) es
Proof
  rpt gen_tac >> strip_tac >>
  `ann = BaseT (UintT 256) /\ expr_type a = BaseT (UintT 256) /\
   expr_type b = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  irule compile_typed_word_builtin_sim_mem >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  qexistsl_tac [`\e. ty`, `\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs)`, `env`] >>
  simp[straight_fresh_compile_modular] >> conj_tac
  >- (rpt strip_tac >> drule lower_value_pow_mod256 >> strip_tac >>
      qexistsl_tac [`[x;y]`, `s2`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
  mp_tac compile_pow_mod256_typed_frag_mem >> simp[] >> disch_then irule >> simp[] >>
  qexists_tac `[x;x']` >> simp[]
QED

Theorem compile_modular_typed_sim_mem:
  !ctx func cenv cx env ty ann bt a b m es.
    (bt = AddMod \/ bt = MulMod) /\
    expr_body_pre cenv cx env (Builtin ann bt [a; b; m]) es /\
    (!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [a; b; m]) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann bt [a; b; m]) es
Proof
  rpt gen_tac >> strip_tac >> (
  `ann = BaseT (UintT 256) /\ expr_type a = BaseT (UintT 256) /\
   expr_type b = BaseT (UintT 256) /\ expr_type m = BaseT (UintT 256)` by
    (gvs[expr_body_pre_def, well_typed_expr_def] >>
     gvs[well_typed_builtin_app_def]) >>
  irule compile_typed_word_builtin_sim_mem >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  qexistsl_tac [`\e. ty`, `\xs. (if bt = AddMod then compile_addmod else compile_mulmod)
                                (EL 0 xs) (EL 1 xs) (EL 2 xs)`, `env`] >>
  conj_tac
  >- (rpt strip_tac >> drule_at Any lower_value_ternary_modular >> simp[] >> strip_tac >>
      qexistsl_tac [`[x;y;z]`, `s3`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  conj_tac
  >- (gvs[] >> simp[straight_fresh_compile_modular]) >>
  rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
  suspend "suffix")
QED
Resume compile_modular_typed_sim_mem[suffix]:
  markerLib.RESUME_TAC >~ [`compile_addmod _ _ _ _ = _`]
  >- (mp_tac (SRULE [] (Q.SPEC `F` compile_modular_typed_frag_mem)) >>
      simp[] >> disch_then irule >> simp[] >>
      qexists_tac `[x;x';x'']` >> simp[]) >>
  mp_tac (SRULE [] (Q.SPEC `T` compile_modular_typed_frag_mem)) >>
  simp[] >> disch_then irule >> simp[] >>
  qexists_tac `[x;x';x'']` >> simp[]
QED
Finalise compile_modular_typed_sim_mem

Theorem compile_floor_typed_sim_mem:
  !ctx func cenv cx env ty ann e es.
    expr_body_pre cenv cx env (Builtin ann Floor [e]) es /\
    (!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [e]) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann Floor [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  irule compile_typed_word_builtin_sim_mem >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  qexistsl_tac [`\e. ty`, `(\xs. compile_floor (EL 0 xs) 10000000000)`, `env`] >>
  simp[straight_fresh_floor] >> conj_tac
  >- (rpt strip_tac >> drule lower_value_floor >> strip_tac >>
      qexistsl_tac [`[x]`, `s1`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  mp_tac compile_floor_word_frag_mem >> simp[] >> disch_then irule >> simp[] >>
  qexists_tac `[x]` >> simp[]
QED

Theorem compile_as_wei_value_typed_sim_mem:
  !ctx func cenv cx env ty ann d e es.
    expr_body_pre cenv cx env (Builtin ann (AsWeiValue d) [e]) es /\
    (!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [e]) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (AsWeiValue d) [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `?k. expr_type e = BaseT (UintT k) /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
        is_uint_type_def] >>
  irule compile_typed_word_builtin_sim_mem >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  qexistsl_tac [`expr_type`, `\xs. compile_as_wei_value_int (EL 0 xs) (denomination_multiplier d) F`, `env`] >>
  simp[straight_fresh_as_wei_value_int] >> conj_tac
  >- (rpt strip_tac >> drule_at Any lower_value_as_wei_value >> simp[] >> strip_tac >>
      qexistsl_tac [`[x]`, `s1`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
  drule_all uint_value_word_rep >> strip_tac >> gvs[] >>
  qpat_assum `v = IntV _` (fn th => once_rewrite_tac[th]) >>
  mp_tac compile_as_wei_value_word_frag_mem >> simp[] >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `[x]` >> simp[] >> metis_tac[]
QED
