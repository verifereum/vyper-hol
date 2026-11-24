Theory runtimeSymSrcGetterExpr
Ancestors
  runtimeSymSrcOpenPlaces runtimeSymSrcContextComplete
  runtimeSymSrcSubscriptGenerators runtimeSymSrcSubscriptPrimitives
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcLiteralEnv exprLowering vyperGetter
  vyperAST compileEnv context list venomInst stackPlanTypes

Theorem runtime_sym_getter_lower_value_raw[local]:
  (!s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce (ty : type) (e : expr) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
  lower_value cfn ce ty e s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_all runtime_sym_unwrap_value >> simp[]
QED

Theorem runtime_sym_getter_subscript_raw:
  (!t s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce t be s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!t s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce t key s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_subscript cfn ce rt ty be key s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `cfn` |-> `cfn`, `ce` |-> `ce`,
    `rt` |-> `rt`, `ty` |-> `ty`, `be` |-> `be`, `key` |-> `key`,
    `s` |-> `s`, `v` |-> `v`, `s'` |-> `s'`] runtime_sym_subscript_step) >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp_tac bool_ss [])
      >- (map_every qx_gen_tac [`kt`,`st`,`op`,`next`] >> strip_tac >>
          qpat_assum `!t s v s'. _ /\ _ /\ cfn ce t key s = (v,s') ==> _`
            (qspec_then `kt` assume_tac) >>
          mp_tac (Q.INST [`tops` |-> `tops`, `cfn` |-> `cfn`, `ce` |-> `ce`,
            `ty` |-> `kt`, `e` |-> `key`, `s` |-> `st`, `op` |-> `op`,
            `s'` |-> `next`] runtime_sym_getter_lower_value_raw) >> asm_rewrite_tac[])
      >- metis_tac[runtime_sym_keccak256_key]
      >- metis_tac[runtime_sym_mapping_subscript]
      >- metis_tac[runtime_sym_tuple_subscript]
      >> ACCEPT_TAC runtime_sym_array_subscript) >>
  disch_then match_mp_tac >> asm_rewrite_tac[]
QED

Theorem runtime_sym_getter_name_raw:
  runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty (Name rt n) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  metis_tac[runtime_sym_compile_name]
QED

Theorem runtime_sym_getter_topname_raw:
  runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty (TopLevelName rt ns) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  mp_tac (Q.INST [`tops` |-> `tops`, `ce` |-> `ce`, `ty` |-> `ty`,
    `rt` |-> `rt`, `ns` |-> `ns`, `s` |-> `s`, `v` |-> `v`, `s'` |-> `s'`]
    runtime_sym_compile_topname) >>
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def]
QED

Theorem runtime_sym_getter_subscript_expr_raw:
  (!ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty be s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty key s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) ==>
  !ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty (Subscript rt be key) s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def, expr_type_def] >> strip_tac >>
  drule_at (Pos last) runtime_sym_getter_subscript_raw >> simp[] >>
  disch_then irule >> metis_tac[]
QED

Theorem runtime_sym_build_getter_expr:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) /\
    (!ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
       compile_expr ce ty e s = (v,s') ==>
       EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) ==>
    !ce ty s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
       compile_expr ce ty exp s = (v,s') ==>
       EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  pure_rewrite_tac[LET_THM] >>
  BETA_TAC >> Cases_on `is_ArrayT vt` >> asm_rewrite_tac[] >>
  simp_tac std_ss [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
  rpt (pairarg_tac >>
       qpat_assum `build_getter _ _ _ _ = (_,_,_)` (fn th =>
         simp_tac std_ss [th, pairTheory.PAIR_EQ, pairTheory.UNCURRY_DEF])) >>
  strip_tac >> qpat_x_assum `_ = exp` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!vn. _` (mp_tac o Q.SPEC `num_to_dec_string n`) >>
  asm_simp_tac std_ss [pairTheory.PAIR_EQ]
  >>~- ([`build_getter _ _ _ _ = _`],
         disch_then ho_match_mp_tac >>
         ho_match_mp_tac runtime_sym_getter_subscript_expr_raw >>
         conj_tac >- (first_assum ACCEPT_TAC) >>
         rpt gen_tac >> strip_tac >> drule_all runtime_sym_getter_name_raw >> simp[]) >>
  ho_match_mp_tac runtime_sym_getter_subscript_expr_raw >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> drule_all runtime_sym_getter_name_raw >> simp[]
QED
