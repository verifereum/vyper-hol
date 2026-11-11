(* Deployment counterpart of the runtime selected internal code boundary. *)
Theory bodyIntCallDeployCode
Ancestors
  bodyIntCallExtractCode ctorDeployLoweringCode ctorDeployLoweringCodeShape
  ctorDeployShape loweringShapeProps loweringShapeDefs loweringShapeRules moduleLowering
  compileEnv compileVyper fragExec vyperCompiler venomWf venomInst list ctorShapeProps ctorRegisterShape unitShapeDefs
  emitHelper context

(* View-general copy of ctorGeneratorShape's local constructor prefix shape:
   the deploy lock/unlock take the constructor's view flag. *)
Theorem dc_fixed_region_plain[local]:
  !sz. shape_step F compiler_label (\st. T)
    (compile_fixed_region_with_id sz)
    (\p st. plain_operand st (SND p).buf_operand)
Proof
  gen_tac >> simp[compile_fixed_region_with_id_def] >>
  irule shape_step_bind >> qexists_tac `\id st. T` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_id >> simp[shape_stable_def]) >>
  qx_gen_tac `id` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\out st. plain_operand st (Var out)` >> reverse conj_tac
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`]
        shape_step_fresh_var) >> simp[shape_stable_def]) >>
  qx_gen_tac `out` >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st (Var out)` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  `shape_stable (\st. plain_operand st (Var out))` by
    (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  mp_tac (Q.SPECL [`F`, `compiler_label`,
    `\st. plain_operand st (Var out)`,
    `mk_inst id ASSIGN [Lit 0w] [out]`] shape_step_emit) >>
  simp[label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, operand_case_not_label,
    is_terminator_def, is_param_opcode_def]
QED

Theorem dc_cenv_exit_shape[local]:
  cenv_shape_ok st cenv /\ cenv.ce_return_pc = NONE /\ jump_label_ok lbl ==>
  cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)
Proof
  strip_tac >> gvs[cenv_shape_ok_def] >> metis_tac[]
QED



Theorem dc_fallthrough_shape[local]:
  !lbl. jump_label_ok lbl ==>
    shape_step F compiler_label (\st. T)
      (do cs <- comp_get;
          if block_is_terminated cs then return ()
          else emit_inst JMP [Label lbl] [] od) (\x st. T)
Proof
  rpt strip_tac >>
  irule shape_step_bind >> qexists_tac `\cs st. T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_return >> simp[]) >>
      mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`,
        `JMP`, `[Label lbl]`, `[]`] shape_step_emit_inst) >>
      simp[shape_stable_def, label_or_plain_def,
           stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
           mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
           inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
           label_positions_ok_def, operand_case_not_label, is_param_opcode_def]) >>
  simp[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem dc_constructor_tail_shape:
  !cenv body imm nr key trans vw runtime_size immutables_len.
    cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label
      (\st. cenv_shape_ok st cenv /\ plain_operand st imm)
      (do (if nr then compile_nonreentrant_lock key trans vw else return ());
          exit_lbl <- fresh_label "ctor_exit";
          compile_stmts (cenv with ce_ctor_exit_label := SOME exit_lbl)
            NoLoop NoneT body;
          cs <- comp_get;
          (if block_is_terminated cs then return ()
           else emit_inst JMP [Label exit_lbl] []);
          new_block exit_lbl;
          (if nr then compile_nonreentrant_unlock key trans vw else return ());
          compile_constructor_epilogue runtime_size immutables_len imm od)
      (\u st. T)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ plain_operand st imm` >>
  reverse conj_tac >- suspend "lock" >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\lbl st. (cenv_shape_ok st cenv /\ plain_operand st imm) /\
    compiler_label lbl` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >> ho_match_mp_tac shape_stable_conj >>
      simp[cenv_shape_ok_stable] >> rw[shape_stable_def] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `lbl` >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac >- suspend "body" >>
  gen_tac >> BETA_TAC >> suspend "finish"
QED

Resume dc_constructor_tail_shape[lock]:
  Cases_on `nr` >> simp[]
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `key`, `trans`, `vw`]
        compile_nonreentrant_lock_shape) >>
      simp[shape_step_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      `cenv_shape_ok st' cenv` by
        (mp_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
         rw[shape_stable_def] >> metis_tac[]) >>
      metis_tac[plain_operand_mono]) >>
  irule shape_step_return >> simp[]
QED

Resume dc_constructor_tail_shape[body]:
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  qspecl_then [`cenv with ce_ctor_exit_label := SOME lbl`,
    `NoLoop`, `NoneT`, `ss`] mp_tac (CONJUNCT2 compile_stmt_shape) >>
  simp[shape_step_def, loop_ctx_shape_ok_def] >>
  rpt strip_tac >>
  `cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)` by
    (irule dc_cenv_exit_shape >> simp[] >>
     gvs[jump_label_ok_def]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Resume dc_constructor_tail_shape[finish]:
  irule shape_step_bind >>
  qexists_tac `\cs st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac
  >- simp[shape_step_def, comp_get_def, shape_extends_refl] >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac
  >- (IF_CASES_TAC >- (irule shape_step_return >> simp[]) >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded >>
      qexists_tac `\st. plain_operand st imm /\ compiler_label lbl` >>
      qexists_tac `compiler_label` >> simp[] >> conj_tac
      >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        jump_label_ok_def, label_positions_ok_def, is_terminator_def,
        is_read0_opcode_def, operand_case_not_label, is_param_opcode_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm` >>
  reverse conj_tac
  >- (`shape_stable (\st. plain_operand st imm)` by
        (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. plain_operand st imm`, `lbl`]
        shape_step_new_block) >>
      simp[shape_step_def] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      metis_tac[plain_operand_mono, shape_stable_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm` >> reverse conj_tac
  >- (Cases_on `nr` >> simp[]
      >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `key`, `trans`, `vw`]
            compile_nonreentrant_unlock_shape) >>
          simp[shape_step_def] >> rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >> metis_tac[plain_operand_mono]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compile_constructor_epilogue_shape
QED

Finalise dc_constructor_tail_shape[local]

Theorem dc_constructor_prefix_shape:
  !cenv body pay nr key trans vw runtime_size immutables_len args data_size.
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label (\st. T)
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if immutables_len > 0 then
                    do p <- compile_fixed_region_with_id immutables_len;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca :=
              (if immutables_len > 0 then SOME imm else NONE)) args 0 data_size;
          (if nr then compile_nonreentrant_lock key trans vw else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT body;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans vw else return ());
          compile_constructor_epilogue runtime_size immutables_len imm od)
      (\u st. T)
Proof
  ntac 11 gen_tac >> strip_tac >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. T` >> reverse conj_tac >- suspend "pay" >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\imm st. plain_operand st imm` >> reverse conj_tac
  >- suspend "allocate" >>
  qx_gen_tac `imm` >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\ce st. cenv_shape_ok st ce /\ plain_operand st imm /\
    ce.ce_return_pc = NONE` >> reverse conj_tac >- suspend "register" >>
  qx_gen_tac `ce` >> BETA_TAC >>
  irule shape_step_conseq >> irule_at Any extbodies_assume >>
  qexists_tac `ce.ce_return_pc = NONE` >>
  qexists_tac `\u st. T` >>
  qexists_tac `\st. cenv_shape_ok st ce /\ plain_operand st imm` >>
  qexists_tac `compiler_label` >> simp[] >>
  strip_tac >> irule dc_constructor_tail_shape >> simp[]
QED

Resume dc_constructor_prefix_shape[pay]:
  Cases_on `pay` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_bind >> qexists_tac `\cv st. plain_operand st cv` >>
  reverse conj_tac
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`, `CALLVALUE`, `[]`]
        shape_step_emit_op) >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
        is_param_opcode_def]) >>
  qx_gen_tac `cv` >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op_guarded >>
      qexists_tac `\st. plain_operand st cv` >>
      qexists_tac `compiler_label` >> simp[] >> conj_tac
      >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
        is_param_opcode_def, operand_case_not_label, plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `v` >> BETA_TAC >>
  rewrite_tac[extbodies_emit_inst_void |> GSYM] >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded >>
  qexists_tac `\st. plain_operand st v` >> qexists_tac `compiler_label` >>
  simp[] >> conj_tac
  >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
    is_param_opcode_def, operand_case_not_label, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED
Resume dc_constructor_prefix_shape[allocate]:
  IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st (SND p).buf_operand` >>
      reverse conj_tac >- irule dc_fixed_region_plain >>
      gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED
Resume dc_constructor_prefix_shape[register]:
  qmatch_goalsub_abbrev_tac `compile_register_constructor_args ce0 args 0 data_size` >>
  `!st. plain_operand st imm ==> cenv_shape_ok st ce0` by
    (rpt strip_tac >> simp[Abbr `ce0`] >>
     irule cenv_shape_ok_install_imm_alloca >> simp[] >>
     metis_tac[cenv_static_ok_shape_ok]) >>
  `ce0.ce_return_pc = NONE` by simp[Abbr `ce0`] >>
  qspecl_then [`args`, `ce0`, `0`, `data_size`] mp_tac
    compile_register_constructor_args_shape >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Finalise dc_constructor_prefix_shape[local]


Theorem dc_lock_flag_select[local]:
  !p f. (\(a:bool,b:num,c:bool,d:bool). f d) p = f (SND (SND (SND p)))
Proof
  PairCases >> simp[]
QED

Theorem compile_deploy_internal_start:
  compile_generate_deploy T runtime_size cap args data_size ints ce ss
    pay nr key trans (initial_compile_state "__deploy") = ((),final) /\
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ss ==>
  ?start.
    shape_state start /\
    compile_internal_fn_bodies ints start = ((),final) /\
    all_blocks start <> [] /\ (HD (all_blocks start)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >> drule_all dc_constructor_prefix_shape >>
  disch_then (qspecl_then [`pay`, `nr`, `key`, `trans`,
                          `SND (SND (SND ce.ce_nonreentrant))`, `runtime_size`,
                          `cap`, `args`, `data_size`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `shape_step F compiler_label (\st. T) prefix _` >>
  `compile_generate_deploy T runtime_size cap args data_size ints ce ss
     pay nr key trans = comp_ignore_bind prefix (compile_internal_fn_bodies ints)`
    by (rewrite_tac[compile_generate_deploy_def, LET_THM, dc_lock_flag_select] >>
        simp[Abbr `prefix`, comp_ignore_bind_def, comp_bind_assoc]) >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__deploy")` >>
  rename1 `prefix _ = (u,start)` >> Cases_on `u` >>
  simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >> simp[shape_step_def] >>
  disch_then drule >> simp[shape_state_initial_compile_state] >> strip_tac >>
  `shape_extends F jump_label_ok (initial_compile_state "__deploy") start` by
    (irule shape_extends_LP_mono >>
     qexists_tac `compiler_label` >> simp[jump_label_ok_def]) >>
  drule initial_entry_blocks_shape >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem run_deploy_lowering_selected_internal_code:
  run_deploy_lowering T policy runtime_bc cap args data_size
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)
    ctor_ce ctor_ss pay ctor_nr ctor_key ctor_trans "__deploy" = SOME unit /\
  cenv_static_ok ctor_ce /\ ctor_ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ctor_ss /\
  EVERY internal_fn_shape_ok
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys))) ==>
  ?func before old st0 after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr key trans view ctor ilen
      ss ret st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  Cases_on `compile_generate_deploy T (LENGTH runtime_bc) cap args data_size
    (xs ++ [(label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret)] ++ ys)
    ctor_ce ctor_ss pay ctor_nr ctor_key ctor_trans
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule_all compile_deploy_internal_start >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
   EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)) ctx.ctx_functions /\
   ctx_inst_ids_distinct ctx` by
    (fs[lowering_context_ok_def, install_immutable_reservation_def,
        ctx_fn_names_def, fn_labels_def, ctx_inst_ids_distinct_def, EVERY_MEM] >>
     simp[]) >>
  drule extract_context_selected_internal_code >>
  disch_then (qspec_then `start` mp_tac) >> simp[] >> strip_tac >>
  simp[install_immutable_reservation_def, ctx_inst_ids_distinct_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> fs[ctx_inst_ids_distinct_def]
QED

Theorem lower_vyper_deploy_unit_selected_internal_code:
  supported_program tops /\ lower_vyper_deploy_unit tops policy runtime_bc = SOME unit /\
  IS_SOME (SND (SND (SND (classify_functions tops)))) /\
  MEM (FunctionDecl Internal mut isnr rr name args dflts ret ss) tops /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) T
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops)
      (mut,isnr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,compiled_ss,rty) ==>
  ?func before old st0 after.
    lookup_function label unit.cu_context.ctx_functions = SOME func /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr key trans view ctor ilen
      compiled_ss rty st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,cf)` >>
  Cases_on `cf` >> gvs[] >> rename1 `_ = (exts,ints,fb,SOME cf)` >>
  `MEM (mut,isnr,rr,name,args,dflts,ret,ss) ints` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >> strip_tac >>
  `SND (SND (SND (classify_functions tops))) = SOME cf` by simp[] >>
  drule_all package_constructor_shape_ok >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_deploy_lowering T _ _ _ _ _ pkgs _ _ _ _ _ _ _` >>
  `EVERY internal_fn_shape_ok pkgs /\
   EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors pkgs) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors pkgs))` by
    (irule deploy_internal_package_certificates >>
     qexistsl_tac [`compute_immutables_len
                     (get_struct_fields (make_struct_fields_map tops)) tops`,
                   `T`, `K global_nonreentrant_slot`, `policy.rpol_target`, `tops`, `T`] >>
     simp[Abbr `pkgs`]) >>
  `MEM (label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,compiled_ss,rty) pkgs` by
    (simp[Abbr `pkgs`, MEM_MAP] >>
     qexists_tac `(mut,isnr,rr,name,args,dflts,ret,ss)` >> simp[]) >>
  qpat_x_assum `MEM _ pkgs`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >> gvs[] >>
  drule (PURE_REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]
    run_deploy_lowering_selected_internal_code) >> simp[]
QED
