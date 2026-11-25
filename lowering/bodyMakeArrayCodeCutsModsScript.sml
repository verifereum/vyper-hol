(* Compiler cuts for the allocation, optional length write and tuple loop. *)
Theory bodyMakeArrayCodeCutsMods
Ancestors
  bodyMakeElementsContractMods exprSimAggregateLayout exprSimAggregateLoops
  exprOperandVar exprLoweringProps gasShadowCompileContext gasShadowCompileBase
  gasShadowState gasShadow fragExec compileEnv exprLowering
Libs
  pairLib

Theorem array_compile_cuts[local]:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) n) args) sa = (vv,sb) ==>
  let h = (case n of Dynamic _ => T | _ => F) in
  ?ba sm sh.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (ba,sm) /\
    (if h then emit_void MSTORE [ba.buf_operand; Lit (n2w (LENGTH args))]
     else return ()) sm = ((),sh) /\
    compile_make_tuple compile_expr ce args (REPLICATE (LENGTH args) et)
      ba.buf_operand (if h then 32 else 0) sh = (ba.buf_operand,sb) /\
    vv = LocatedValue ann (mk_ptr ba.buf_operand LocMemory)
Proof
  strip_tac >> drule compile_array_literal_inv >> strip_tac >>
  drule compiler_make_array_result >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_make_array_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >>
  rename1 `(if _ then _ else _) _ = (x,sh)` >>
  Cases_on `x` >> gvs[compile_make_array_elems_as_tuple] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem shadow_array_alloc_result[local]:
  gas_shadow_state sa sha /\
  compile_alloc_buffer cap sa = (ba,sm) /\
  compile_alloc_buffer cap sha = (bba,ssm) ==>
  bba = ba /\ gas_shadow_state sm ssm
Proof
  strip_tac >>
  mp_tac (Q.INST [`nbytes` |-> `cap`] gas_shadow_compiles_alloc_buffer) >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]
QED

Theorem shadow_array_header_result[local]:
  gas_shadow_state sm ssm /\
  (if h then emit_void MSTORE [root; Lit (n2w k)] else return ()) sm = ((),sh) /\
  (if h then emit_void MSTORE [root; Lit (n2w k)] else return ()) ssm = ((),ssh) ==>
  gas_shadow_state sh ssh
Proof
  reverse (Cases_on `h`) >- (simp[comp_return_def] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MSTORE`, `ops` |-> `[root; Lit (n2w k)]`]
     gas_shadow_compiles_emit_void) >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sm`,`ssm`] mp_tac) >> simp[]
QED

Theorem array_compile_intervals[local]:
  compile_alloc_buffer cap sa = (ba,sm) /\
  (if h then emit_void MSTORE [ba.buf_operand; Lit (n2w k)]
   else return ()) sm = ((),sh) /\
  compile_make_tuple compile_expr ce args tys ba.buf_operand off sh = (ba.buf_operand,sb) /\
  fn_has_code sa sb func ==>
  ci_mono sa sm /\ ci_mono sm sh /\ ci_mono sh sb /\
  fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh sb func
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `cap` (qspec_then `sa` mp_tac) ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sh` by
    (Cases_on `h` >> gvs[comp_return_def, ci_mono_refl] >>
     qspecl_then [`MSTORE`,`[ba.buf_operand; Lit (n2w k)]`,`sm`] mp_tac
       ci_mono_emit_void >> simp[]) >>
  `ci_mono sh (SND (compile_make_tuple compile_expr ce args tys ba.buf_operand off sh))` by
    (irule ci_mono_compile_make_tuple_cfn >> simp[compile_expr_ci_mono]) >>
  `ci_mono sh sb` by
    (qpat_x_assum `ci_mono sh (SND _)` mp_tac >>
     qpat_assum `compile_make_tuple _ _ _ _ _ _ _ = _` (fn th => simp[th])) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >>
     irule cs_extends_trans >> qexists `sh` >> simp[]) >>
  `fn_has_code sm sh func /\ fn_has_code sh sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  simp[]
QED

Theorem make_array_code_cuts_mods:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin ann (MakeArray (SOME et) n) args)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  let h = (case n of Dynamic _ => T | _ => F) in
  let k = LENGTH args in
  let off = if h then 32 else 0 in
  ?ba sm ssm sh ssh.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (ba,sm) /\
    compile_alloc_buffer (type_memory_bytes ce ann) sha = (ba,ssm) /\
    (if h then emit_void MSTORE [ba.buf_operand; Lit (n2w k)]
     else return ()) sm = ((),sh) /\
    (if h then emit_void MSTORE [ba.buf_operand; Lit (n2w k)]
     else return ()) ssm = ((),ssh) /\
    gas_shadow_state sm ssm /\ gas_shadow_state sh ssh /\
    compile_make_tuple compile_expr ce args (REPLICATE k et) ba.buf_operand off sh =
      (ba.buf_operand,sb) /\
    compile_make_tuple compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr args)
      (REPLICATE k et) ba.buf_operand off ssh = (ba.buf_operand,shb) /\
    make_elements_code_mods func shadow_func sh sb ssh shb /\
    ci_mono sa sm /\ ci_mono sm sh /\ ci_mono sh sb /\
    ci_mono sha ssm /\ ci_mono ssm ssh /\ ci_mono ssh shb /\
    fn_has_code sa sm func /\ fn_has_code sm sh func /\
    fn_has_code sha ssm shadow_func /\ fn_has_code ssm ssh shadow_func /\
    vv = LocatedValue ann (mk_ptr ba.buf_operand LocMemory)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >>
  qpat_assum `compile_expr _ _ (Builtin _ _ _) _ = _`
    (mp_tac o MATCH_MP array_compile_cuts) >>
  simp[SimpLHS] >> disch_then (qx_choosel_then [`ba`,`sm`,`sh`] strip_assume_tac) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[SimpLHS, Once gas_shadow_expr_def, gas_shadow_builtin_def] >>
  disch_then (mp_tac o MATCH_MP array_compile_cuts) >>
  simp[SimpLHS, type_memory_bytes_gas_shadow_env] >>
  disch_then (qx_choosel_then [`bba`,`ssm`,`ssh`] strip_assume_tac) >>
  `bba = ba /\ gas_shadow_state sm ssm` by
    (irule shadow_array_alloc_result >>
     qexistsl_tac [`type_memory_bytes ce ann`,`sa`,`sha`] >> simp[]) >>
  qpat_x_assum `bba = ba` SUBST_ALL_TAC >>
  `gas_shadow_state sh ssh` by
    (irule shadow_array_header_result >>
     qexistsl_tac [`case n of Dynamic _ => T | _ => F`, `LENGTH args`,
                   `ba.buf_operand`, `sm`, `ssm`] >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sm sh /\ ci_mono sh sb /\
   fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh sb func` by
    (irule array_compile_intervals >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ci_mono sha ssm /\ ci_mono ssm ssh /\ ci_mono ssh shb /\
   fn_has_code sha ssm shadow_func /\ fn_has_code ssm ssh shadow_func /\
   fn_has_code ssh shb shadow_func` by
    (irule array_compile_intervals >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl_tac [`ssm`,`ssh`] >>
  simp[make_elements_code_mods_def]
QED
