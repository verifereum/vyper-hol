Theory entryRuntimeBodyCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryModuleScaffoldCode
  moduleLowering compileEnv

Theorem entry_code_guarded_body:
  (!ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmts ce lc rt fbody)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_guarded_body ce F key trans view fbody ret)
Proof
  strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return, entry_code_get] >>
    rpt gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[entry_code_return] >>
  Cases_on `ret` >> irule entry_code_bind >>
  simp[entry_code_return, entry_code_emit_inst]
QED

Theorem entry_code_external_function_body:
  (!ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmts ce lc rt fbody)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_external_function_body ce args F key trans view fbody ret)
Proof
  strip_tac >> simp[compile_external_function_body_def] >>
  irule entry_code_bind >>
  simp[entry_code_register_positional_args, entry_code_guarded_body]
QED

Theorem entry_code_fallback_body:
  (!ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmts ce lc rt fbody)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_fallback_body ce payable F key trans view fbody ret)
Proof
  strip_tac >> simp[compile_fallback_body_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_void]) >>
  simp[entry_code_guarded_body]
QED

Theorem entry_code_internal_function:
  (!ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_stmts ce lc rt fbody)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_internal_function ce params has_buf F key trans view F 0
      fbody ret)
Proof
  strip_tac >> simp[compile_internal_function_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      irule entry_code_bind >> simp[entry_code_emit_op, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return, entry_code_internal_param_decls,
            entry_code_emit_op, entry_code_materialize_internal_params] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `ret` >> simp[entry_code_return] >>
      IF_CASES_TAC >> simp[entry_code_return] >>
      irule entry_code_bind >> simp[entry_code_alloc_buffer, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_return, entry_code_get] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      Cases_on `ret` >> irule entry_code_bind >>
      simp[entry_code_return, entry_code_emit_inst]) >>
  simp[entry_code_return]
QED

Theorem entry_code_external_fn_bodies:
  !pkgs. EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_external_function_body ce args nr key tr vw fb rt)) pkgs ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_external_fn_bodies pkgs)
Proof
  Induct >> simp[compile_external_fn_bodies_def, entry_code_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_new_block, entry_code_entry_checks] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_internal_fn_bodies:
  !pkgs. EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_internal_function ce ps buf nr key tr vw ctor im fb rt)) pkgs ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_internal_fn_bodies pkgs)
Proof
  Induct >> simp[compile_internal_fn_bodies_def, entry_code_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_new_block] >> rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_generate_runtime:
  EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_external_function_body ce args nr key tr vw fb rt)) exts /\
  EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_internal_function ce ps buf nr key tr vw ctor im fb rt)) ints /\
  (case fallback of NONE => T
   | SOME (ce,pay,nr,key,tr,vw,fb,rt) =>
       entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
         (compile_fallback_body ce pay nr key tr vw fb rt)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_generate_runtime sels exts ints fallback strategy n_buckets
      bytes buckets info)
Proof
  strip_tac >> simp[compile_generate_runtime_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_fresh_label] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `strategy` >>
      simp[entry_code_selector_dispatch_linear, entry_code_selector_dispatch_sparse,
           entry_code_selector_dispatch_dense]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_external_fn_bodies, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `fallback` >- simp[entry_code_emit_inst] >>
      rename1 `SOME pkg` >> PairCases_on `pkg` >> gvs[]) >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_internal_fn_bodies, entry_code_return]
QED
