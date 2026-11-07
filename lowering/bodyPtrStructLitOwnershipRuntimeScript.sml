Theory bodyPtrStructLitOwnershipRuntime
Ancestors
  bodyPtrStructLitOwnershipFunctionLists bodyPtrStructLitOwnershipGuarded
  bodyPtrStructLitOwnershipDispatch bodyPtrStructLitOwnershipControlFrame
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  loweringShapeProps loweringShapeDefs loweringShapeRules
  moduleLowering compileEnv context unitShapeDefs venomInst

Theorem alloc_run_fallback_shape_fresh:
  !ce pay nr key tr view stmts rt.
  fallback_shape_ok (SOME (ce,pay,nr,key,tr,view,stmts,rt)) /\ ce.ce_alloca_locals ==>
  alloc_run shape_state (compile_fallback_body ce pay nr key tr view stmts rt)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt strip_tac >> irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
  irule_at Any compile_fallback_body_shape >> simp[] >>
  irule_at Any alloc_run_compile_fallback_body >>
  gvs[fallback_shape_ok_def] >> simp[cenv_static_ok_shape_ok]
QED

Theorem alloc_run_fallback_option:
  !fb.
  fallback_shape_ok fb /\
  (case fb of NONE => T | SOME (ce,pay,nr,key,tr,view,stmts,rt) => ce.ce_alloca_locals) ==>
  alloc_run shape_state
    (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) => compile_fallback_body ce pay nr key tr view stmts rt)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  Cases
  >- (simp[fallback_shape_ok_def] >> irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
      irule_at Any alloc_run_emit_empty_fresh >>
      irule_at Any shape_step_emit_inst >> qexistsl [`F`, `\s. T`] >>
      simp[shape_stable_def, shape_state_def, shape_base_fresh_outputs,
        label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
        label_positions_ok_def, operand_case_not_label, is_param_opcode_def]) >>
  PairCases_on `x` >> simp[alloc_run_fallback_shape_fresh]
QED

Theorem alloc_run_pure_pre:
  (b ==> alloc_run P f Q) ==> alloc_run (\s. P s /\ b) f Q
Proof
  rw[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_generate_runtime_linear:
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt).
    external_fn_shape_ok (lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt) /\ ce.ce_alloca_locals) exts /\
  EVERY (\(lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt).
    internal_fn_shape_ok (lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt) /\ internal_label_ok lbl) ints /\
  fallback_shape_ok fb /\
  (case fb of NONE => T | SOME (ce,pay,nr,key,tr,view,stmts,rt) => ce.ce_alloca_locals) ==>
  alloc_run shape_state (compile_generate_runtime sels exts ints fb Linear buckets metadata dense info)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  strip_tac >> simp[compile_generate_runtime_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\lbl s. shape_state s /\ compiler_label lbl /\ label_sfx "fallback" lbl` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_pure_pre >> strip_tac >>
  irule alloc_run_bind >> qexists `\u s. shape_state s` >> conj_tac
  >- (gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\u s. shape_state s` >> conj_tac
      >- (gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\u s. shape_state s` >> conj_tac
          >- (gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\u s. shape_state s` >> conj_tac
              >- (gen_tac >> simp[] >> irule alloc_run_bind >>
                  qexists `\u s. shape_state s /\ fresh_outputs s` >> conj_tac
                  >- (gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
                  simp[SF ETA_ss] >> irule alloc_run_compile_internal_fn_bodies >> simp[]) >>
              irule alloc_run_conseq >> irule_at Any alloc_run_fallback_option >> simp[]) >>
          irule alloc_run_conseq >> irule_at Any alloc_run_new_block_exact >> simp[]) >>
      irule alloc_run_conseq >> irule_at Any alloc_run_compile_external_fn_bodies >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_selector_dispatch_linear >>
  simp[listTheory.EVERY_MAP, pairTheory.FORALL_PROD, jump_label_ok_def] >>
  conj_tac
  >- (gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  strip_tac >>
  mp_tac (Q.INST [`s1` |-> `"fallback"`, `s2` |-> `"dispatch"`,
    `l1` |-> `v`, `l2` |-> `v`] label_sfx_distinct) >> simp[]
QED
