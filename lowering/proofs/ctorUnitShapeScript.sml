Theory ctorUnitShape
Ancestors
  list rich_list string
  ctorGeneratorShape loweringShapeProps loweringShapeDefs vyperCompiler
  moduleLowering compileEnv context emitHelper unitShapeDefs venomInst

Theorem deploy_label_names[local]:
  ~jump_label_ok "__deploy" /\ ~reserved_label "__deploy"
Proof
  simp[jump_label_ok_def, reserved_label_def] >>
  strip_tac >> drule compiler_label_prefix >> simp[]
QED

Theorem deploy_internal_label_separate:
  !n entry.
    internal_label_ok n /\ entry <> [] /\
    (HD entry).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry)) ==>
    ~compiler_label n /\ ~MEM n (MAP (\bb. bb.bb_label) entry)
Proof
  rpt gen_tac >> strip_tac >>
  `?rest. n = "internal " ++ rest` by
    (qpat_x_assum `internal_label_ok n` mp_tac >>
     REWRITE_TAC[internal_label_ok_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >> drule compiler_label_prefix >> simp[] >> gvs[]) >>
  Cases_on `entry` >> gvs[EVERY_MEM, MEM_MAP] >>
  gen_tac >> disch_tac >> conj_tac
  >- (strip_tac >> gvs[]) >>
  metis_tac[jump_label_ok_names]
QED

Theorem deploy_unit_reservation_shape[local]:
  !ctx data data' len.
    o1_source_unit_ok <|cu_context := ctx; cu_data_segment := data|> ==>
    o1_source_unit_ok
      <|cu_context := install_immutable_reservation len ctx;
        cu_data_segment := data'|>
Proof
  simp[install_immutable_reservation_def, o1_source_unit_ok_def,
       unit_shape_ok_def, entry_fn_first_def, internal_termination_ok_def]
QED

Theorem run_deploy_lowering_source_unit_ok:
  !has_constructor rpolicy runtime_bytecode immutables_len constructor_args
   data_size ctor_internal_fns cenv body is_payable is_nonreentrant nkey
   use_transient unit.
    run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
      constructor_args data_size ctor_internal_fns cenv body is_payable
      is_nonreentrant nkey use_transient "__deploy" = SOME unit /\
    (has_constructor ==>
      cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
      ~supported_stmts_expr_exists expr_shape_root body) /\
    (~has_constructor ==> ctor_internal_fns = []) /\
    EVERY internal_fn_shape_ok ctor_internal_fns /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors ctor_internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns)) ==>
    o1_source_unit_ok unit
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  `(if has_constructor then ctor_internal_fns else []) = ctor_internal_fns`
    by (Cases_on `has_constructor` >> gvs[]) >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _`
       mp_tac >> rw[run_deploy_lowering_def]) >>
  Cases_on `compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
    immutables_len constructor_args data_size ctor_internal_fns cenv ss
    is_payable is_nonreentrant nkey use_transient
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (u, st1)` >> Cases_on `u` >>
  drule compile_generate_deploy_shape >> simp[] >> strip_tac >>
  drule_all shape_state_source_certificates >> strip_tac >>
  drule_all raw_checked_internal_segments >> strip_tac >>
  `package_internal_blocks (internal_fn_descriptors ctor_internal_fns)
     (entry_blocks ++ FLAT segs) =
   SOME (entry_blocks,
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors ctor_internal_fns)
              segs)`
    by (irule package_internal_blocks_segments >> asm_rewrite_tac [] >>
        REWRITE_TAC[EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
        irule deploy_internal_label_separate >> fs[EVERY_MEM]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks st1 = _`
    (assume_tac o REWRITE_RULE[all_blocks_def]) >>
  gs[run_deploy_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[] >>
  irule deploy_unit_reservation_shape >> qexists_tac `[]` >>
  irule entry_unit_source_ok >> simp[deploy_label_names] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
