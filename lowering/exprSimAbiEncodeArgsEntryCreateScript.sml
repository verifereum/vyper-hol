Theory exprSimAbiEncodeArgsEntryCreate
Ancestors
  exprSimAbiEncodeArgsEntryCall externalEntryShape exprLowering
  context compileEnv emitHelper builtinCreate
  exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim

Theorem abi_args_entry_create_snapshot:
  !ce vv ty a x b. compile_create_snapshot ce vv ty a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 3 gen_tac >> simp[compile_create_snapshot_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >>
  Cases_on `vv_location vv` >>
  gvs[] >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, comp_return_labels,
            compile_copy_memory_dynamic_labels]) >>
  Cases_on `x` >> simp[] >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, comp_return_labels,
            contextTheory.compile_slot_to_memory_def,
            compile_word_copy_loop_labels, compile_imm_copy_to_memory_labels,
            compile_copy_memory_dynamic_labels])
QED

Theorem abi_args_entry_create_blueprint_args:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce raw es a x b. compile_create_blueprint_args cfn ce raw es a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> ntac 3 gen_tac >> Cases_on `raw` >>
  simp[compile_create_blueprint_args_def]
  >- (namedCases_on `es` ["", "head tail"] >> simp[]
      >- (rewrite_tac[comp_ignore_bind_def] >>
          ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- (rpt gen_tac >> strip_tac >> `INVALID <> PHI` by simp[] >>
              metis_tac[fragExecTheory.cs_extends_emit_inst,
                        abi_args_entry_safe_emit_inst]) >>
          metis_tac[abi_args_entry_safe_return]) >>
      Cases_on `tail` >> simp[]
      >- (ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- (rpt strip_tac >> `MLOAD <> PHI /\ ADD <> PHI` by simp[] >>
              metis_tac[abi_args_entry_emit_op, abi_args_entry_safe_def]) >>
          gen_tac >> ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
          >- (rpt strip_tac >> `MLOAD <> PHI /\ ADD <> PHI` by simp[] >>
              metis_tac[abi_args_entry_emit_op, abi_args_entry_safe_def]) >>
          metis_tac[abi_args_entry_safe_return]) >>
      rewrite_tac[comp_ignore_bind_def] >>
      ho_match_mp_tac abi_args_entry_safe_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >> `INVALID <> PHI` by simp[] >>
          metis_tac[fragExecTheory.cs_extends_emit_inst,
                    abi_args_entry_safe_emit_inst]) >>
      metis_tac[abi_args_entry_safe_return]) >>
  IF_CASES_TAC >> simp[]
  >- metis_tac[abi_args_entry_safe_return] >>
  ho_match_mp_tac abi_args_entry_safe_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  gen_tac >> irule abi_args_entry_extends_bind >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule abi_args_entry_extends_bind >> conj_tac >>
      simp[comp_return_labels, cj 2 compile_abi_encode_labels]) >>
  gen_tac >> Cases_on `compile_create_ctor_tuple cfn ce es s` >> simp[] >>
  metis_tac[abi_args_entry_create_ctor_tuple]
QED

Theorem abi_args_entry_raw_create:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce code value es salt rof a x b.
    compile_raw_create cfn ce code value es salt rof a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 6 gen_tac >> simp[compile_raw_create_def] >>
  ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_create_snapshot] >>
  gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, comp_return_labels, compile_alloc_buffer_labels,
            compile_copy_memory_dynamic_labels, cj 2 compile_abi_encode_labels,
            compile_create_dispatch_labels])
  >~ [`lower_value`] >- (irule abi_args_entry_extends_result >>
      metis_tac[abi_args_entry_lower_value])
  >~ [`if es = [] then _ else _`] >-
    (Cases_on `es = []` >> simp[comp_return_labels] >>
     rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
                 irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
          rpt gen_tac >> BETA_TAC >>
          simp[emit_op_labels, comp_return_labels, compile_alloc_buffer_labels,
               compile_copy_memory_dynamic_labels, cj 2 compile_abi_encode_labels]) >>
     irule abi_args_entry_extends_result >>
     metis_tac[abi_args_entry_create_ctor_tuple]) >>
  pairarg_tac >> gvs[] >> irule abi_args_entry_extends_bind >> conj_tac
  >- simp[compile_create_dispatch_labels] >>
  irule abi_args_entry_extends_result >>
  metis_tac[abi_args_entry_create_salt]
QED

Theorem abi_args_entry_create_proxy_buf:
  !target a x b. compile_create_proxy_buf target a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> simp[compile_create_proxy_buf_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels, comp_return_labels])
QED

Theorem abi_args_entry_create_blueprint_check:
  !target offset a x b. compile_create_blueprint_check target offset a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 2 gen_tac >> simp[compile_create_blueprint_check_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> `EXTCODESIZE <> PHI` by simp[] >>
      metis_tac[abi_args_entry_emit_op]) >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind >> conj_tac,
              irule abi_args_entry_extends_ignore_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels, comp_return_labels])
QED

Theorem abi_args_entry_create_copy:
  !target value salt rof a x b. compile_create_copy target value salt rof a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 4 gen_tac >> simp[compile_create_copy_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> `EXTCODESIZE <> PHI` by simp[] >>
      metis_tac[abi_args_entry_emit_op]) >>
  ntac 2 gen_tac >>
  qmatch_goalsub_abbrev_tac `SND (suffix b)` >>
  `!b. cs_extends b (SND (suffix b)) /\
       EVERY (isPREFIX "@") (added_labels b (SND (suffix b)))`
    suffices_by metis_tac[] >>
  simp[Abbr `suffix`] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels, comp_return_labels,
            compile_alloc_dynamic_labels, compile_check_create_result_labels]) >>
  FIRST [Cases_on `salt`, Cases_on `rof`] >>
  simp[emit_op_labels, emit_void_labels, comp_return_labels]
QED

Theorem abi_args_entry_create_dispatch:
  !ptr len value salt rof a x b.
    compile_create_dispatch ptr len value salt rof a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 5 gen_tac >> simp[compile_create_dispatch_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (Cases_on `salt` >> simp[] >> rpt gen_tac >> strip_tac >>
      `CREATE <> PHI /\ CREATE2 <> PHI` by simp[] >>
      metis_tac[abi_args_entry_emit_op]) >>
  simp[compile_check_create_result_labels]
QED

Theorem abi_args_entry_invalid_return:
  !v a x b.
    (do emit_inst INVALID [] []; comp_return v od) a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> `INVALID <> PHI` by simp[] >>
      metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]) >>
  simp[comp_return_labels]
QED

Theorem abi_args_entry_create_call:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce ck salt rof es a x b.
    compile_create_call cfn ce ck salt rof es a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >> namedCases_on `es` ["", "target rest"]
  >- (simp[compile_create_call_def] >>
      metis_tac[abi_args_entry_invalid_return]) >>
  namedCases_on `rest` ["", "value tail"]
  >- (simp[compile_create_call_def] >>
      metis_tac[abi_args_entry_invalid_return]) >>
  simp[compile_create_call_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[abi_args_entry_invalid_return] >>
  Cases_on `ck`
  >- suspend "proxy"
  >- suspend "copy"
  >- suspend "blueprint"
  >> simp[] >> metis_tac[abi_args_entry_raw_create]
QED

Resume abi_args_entry_create_call[proxy]:
  simp[] >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_create_proxy_buf] >>
  gen_tac >> irule abi_args_entry_extends_bind >> conj_tac
  >- simp[compile_create_dispatch_labels] >>
  irule abi_args_entry_extends_result >> metis_tac[abi_args_entry_create_salt]
QED

Resume abi_args_entry_create_call[copy]:
  simp[] >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_create_salt] >>
  metis_tac[abi_args_entry_create_copy]
QED

Resume abi_args_entry_create_call[blueprint]:
  simp[] >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_create_salt] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_suffix_bind >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_create_blueprint_check] >>
  gen_tac >> irule abi_args_entry_extends_bind >> conj_tac
  >- (gen_tac >> pairarg_tac >> simp[compile_create_blueprint_append_labels]) >>
  irule abi_args_entry_extends_result >>
  metis_tac[abi_args_entry_create_blueprint_args]
QED

Finalise abi_args_entry_create_call

Theorem abi_args_entry_create_target:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty ck salt rof mode es d a vv b.
    compile_call cfn ce rt ty (CreateTarget ck salt rof mode) es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `compile_create_call cfn ce ck salt rof es a` >>
  simp[compile_call_def, as_stack_val_def] >> strip_tac >> gvs[] >>
  metis_tac[abi_args_entry_create_call]
QED

Theorem abi_args_entry_selfdestruct_target:
  !cfn ce rt ty es d a vv b.
    compile_call cfn ce rt ty SelfDestructTarget es d a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  rpt gen_tac >> simp[compile_call_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> `INVALID <> PHI` by simp[] >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]
QED
