(* Compositional production-layout certificates for CREATE preparation and call. *)
Theory createSizeCreateLayoutCode
Ancestors
  createSizeCutCode exprLowering builtinCreate emitHelper compileEnv venomInst pair
  createSizeLocationCode context

Theorem create_preparation_segments_case:
  create_cut_code {} a (SND (m a)) /\
  (!v b. create_cut_code {} b (SND (k v b))) ==>
  create_cut_code {} a (SND (comp_bind m k a))
Proof
  Cases_on `m a` >> simp[comp_bind_def] >>
  metis_tac[create_cut_code_join]
QED

Theorem create_invalid_call_cut:
  !a. create_cut_code {} a
    (SND ((\(_0,cs'). (Lit 0w,cs')) (emit_inst INVALID [] [] a)))
Proof
  rpt gen_tac >>
  `create_cut_code {} a (SND (emit_inst INVALID [] [] a))` by
    (irule create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  pairarg_tac >> gvs[]
QED

Theorem create_dispatch_cut:
  (!created rof a. create_cut_code {} a
     (SND (compile_check_create_result created rof a))) ==>
  !ptr len value salt rof a.
    create_cut_code {} a
      (SND (compile_create_dispatch ptr len value salt rof a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `salt` >>
  simp[compile_create_dispatch_def] >> irule create_preparation_segments_case >>
  (conj_tac >- simp[]) >>
  irule create_cut_code_emit_op >> simp[create_cut_targets_def]
QED

Theorem create_ctor_args_cut:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
  (!ce copy vv a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))) ==>
  !cenv es a. create_cut_code {} a (SND (compile_create_ctor_args cfn cenv es a))
Proof
  strip_tac >> gen_tac >> Induct >> simp[compile_create_ctor_args_def] >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >>
  (reverse conj_tac >- simp[]) >> rpt gen_tac >> simp[] >>
  irule create_preparation_segments_case >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >> simp[]
QED

Theorem create_blueprint_args_cut:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
  (!ce copy vv a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))) /\
  (!ce dst rows a. create_cut_code {} a
     (SND (compile_abi_encode_values_to_buf ce dst rows a))) ==>
  !cenv raw_args later_es args a.
    create_cut_code {} a (SND (compile_create_blueprint_args cfn cenv raw_args later_es args a))
Proof
  strip_tac >> rpt gen_tac >> simp[] >> Cases_on `raw_args`
  >- (Cases_on `args` >-
        (simp[compile_create_blueprint_args_def] >> irule create_cut_code_ignore_bind >>
         simp[create_cut_code_emit_inst,create_cut_targets_def]) >>
      rename1 `compile_create_blueprint_args _ _ T _ (e::es) _` >> Cases_on `es`
      >- (simp[compile_create_blueprint_args_def] >>
          irule create_preparation_segments_case >> (reverse conj_tac >- simp[]) >>
          rpt gen_tac >> simp[] >> irule create_preparation_segments_case >>
          (reverse conj_tac >- simp[]) >> rpt gen_tac >> simp[] >>
          irule create_preparation_segments_case >>
          (reverse conj_tac >- simp[create_unwrap_cut_code]) >> rpt gen_tac >> simp[] >>
          irule create_preparation_segments_case >>
          (reverse conj_tac >- simp[create_cut_code_emit_op,create_cut_targets_def]) >>
          rpt gen_tac >> simp[] >> irule create_preparation_segments_case >>
          simp[create_cut_code_emit_op,create_cut_targets_def]) >>
      simp[compile_create_blueprint_args_def] >> irule create_cut_code_ignore_bind >>
      simp[create_cut_code_emit_inst,create_cut_targets_def]) >>
  Cases_on `args` >> simp[compile_create_blueprint_args_def,LET_THM] >>
  irule create_preparation_segments_case >>
  (reverse conj_tac >- metis_tac[create_ctor_args_cut]) >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >>
  (reverse conj_tac >-
    (simp[compile_alloc_buffer_def] >> irule create_preparation_segments_case >>
     simp[create_cut_code_emit_op,create_cut_targets_def])) >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >> simp[]
QED

Theorem create_copy_call_cut:
  (!ce ty e a. create_cut_code {} a (SND (lower_value cfn ce ty e a))) /\
  (!ce salt a. create_cut_code {} a (SND (compile_create_salt cfn ce salt a))) /\
  (!target value salt rof a.
     create_cut_code {} a (SND (compile_create_copy target value salt rof a))) ==>
  !has_salt target_e value_e rest rof a.
    ~(LENGTH rest < (if has_salt then 1 else 0)) ==>
    create_cut_code {} a
      (SND (compile_create_call cfn cenv CreateCopyOf has_salt rof
                (target_e::value_e::rest) a))
Proof
  rpt strip_tac >> simp[compile_create_call_def] >>
  irule create_preparation_segments_case >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> simp[] >> irule create_preparation_segments_case >> simp[]
QED

Theorem create_minimal_proxy_call_cut:
  (!ce ty e a. create_cut_code {} a (SND (lower_value cfn ce ty e a))) /\
  (!ce salt a. create_cut_code {} a (SND (compile_create_salt cfn ce salt a))) /\
  (!target a. create_cut_code {} a (SND (compile_create_proxy_buf target a))) /\
  (!created rof a. create_cut_code {} a
     (SND (compile_check_create_result created rof a))) ==>
  !has_salt target_e value_e rest rof a.
    ~(LENGTH rest < (if has_salt then 1 else 0)) ==>
    create_cut_code {} a
      (SND (compile_create_call cfn cenv CreateMinimalProxy has_salt rof
             (target_e::value_e::rest) a))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `has_salt` >> fs[compile_create_call_def] >>
  rpt (irule create_preparation_segments_case >>
       (reverse conj_tac >- simp[]) >> rpt gen_tac >> BETA_TAC) >>
  irule create_dispatch_cut >> simp[]
QED

Theorem create_blueprint_call_cut:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
  (!ce vv ty a. create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))) /\
  (!ce copy vv a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))) /\
  (!ce dst rows a. create_cut_code {} a
     (SND (compile_abi_encode_values_to_buf ce dst rows a))) /\
  (!ce ty e a. create_cut_code {} a (SND (lower_value cfn ce ty e a))) /\
  (!ce salt a. create_cut_code {} a (SND (compile_create_salt cfn ce salt a))) /\
  (!target value salt rof a.
     create_cut_code {} a (SND (compile_create_copy target value salt rof a))) /\
  (!target value salt offset code args_ptr args_len rof a.
     create_cut_code {} a
       (SND (compile_create_blueprint_append target value salt offset code args_ptr args_len rof a))) /\
  (!target a. create_cut_code {} a (SND (compile_create_proxy_buf target a))) /\
  (!created rof a. create_cut_code {} a
     (SND (compile_check_create_result created rof a))) ==>
  !raw_args has_salt target_e value_e rest rof a.
    ~(LENGTH rest < 1 + (if has_salt then 1 else 0)) ==>
    create_cut_code {} a
      (SND (compile_create_call cfn cenv (CreateFromBlueprint raw_args)
             has_salt rof (target_e::value_e::rest) a))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `~(LENGTH rest < (if has_salt then 1 else 0) + 1)` by
    (Cases_on `has_salt` >> gvs[]) >>
  simp[compile_create_call_def,LET_THM] >>
  irule create_preparation_segments_case >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> BETA_TAC >> irule create_preparation_segments_case >>
  (reverse conj_tac >- (irule create_blueprint_args_cut >> simp[])) >>
  qx_gen_tac `payload` >> PairCases_on `payload` >> gen_tac >> simp[] >>
  irule create_preparation_segments_case >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> BETA_TAC >>
  irule create_preparation_segments_case >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> BETA_TAC >>
  irule create_preparation_segments_case >>
  (reverse conj_tac >- rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  rpt gen_tac >> BETA_TAC >>
  irule create_preparation_segments_case >> (conj_tac >- simp[]) >>
  qmatch_goalsub_rename_tac `compile_create_blueprint_check lit target off st` >>
  Cases_on `lit` >> simp[compile_create_blueprint_check_def] >>
  rpt (irule create_preparation_segments_case >>
       (reverse conj_tac >- simp[create_cut_code_emit_op,create_cut_targets_def]) >>
       rpt gen_tac >> BETA_TAC) >>
  irule create_cut_code_ignore_bind >> simp[create_cut_code_emit_void,create_cut_targets_def]
QED

Theorem create_raw_call_cut:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
  (!ce vv ty a. create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))) /\
  (!ce copy vv a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))) /\
  (!ce dst rows a. create_cut_code {} a
     (SND (compile_abi_encode_values_to_buf ce dst rows a))) /\
  (!ce ty e a. create_cut_code {} a (SND (lower_value cfn ce ty e a))) /\
  (!ce salt a. create_cut_code {} a (SND (compile_create_salt cfn ce salt a))) /\
  (!created rof a. create_cut_code {} a (SND (compile_check_create_result created rof a))) ==>
  !has_salt target_e value_e rest rof a.
    ~(LENGTH rest < (if has_salt then 1 else 0)) ==>
    create_cut_code {} a
      (SND (compile_create_call cfn cenv RawCreate has_salt rof
               (target_e::value_e::rest) a))
Proof
  strip_tac >>
  `!ctor_args salt_e bytecode_e value_e rof a.
     create_cut_code {} a
       (SND (compile_raw_create cfn cenv bytecode_e value_e ctor_args salt_e rof a))`
    suffices_by
      (strip_tac >> rpt gen_tac >> strip_tac >>
       Cases_on `has_salt` >> fs[compile_create_call_def]) >>
  rpt gen_tac >> simp[compile_raw_create_def,LET_THM] >>
  ntac 4 (irule create_preparation_segments_case >>
          (reverse conj_tac >- simp[create_cut_code_emit_op,create_cut_targets_def]) >>
          rpt gen_tac >> BETA_TAC) >>
  irule create_preparation_segments_case >> reverse conj_tac
  >- (Cases_on `ctor_args = []` >> simp[] >>
      irule create_preparation_segments_case >>
      (reverse conj_tac >- simp[create_ctor_args_cut]) >>
      rpt gen_tac >> BETA_TAC >> irule create_preparation_segments_case >>
      (reverse conj_tac >-
        (simp[compile_alloc_buffer_def] >> irule create_preparation_segments_case >>
         simp[create_cut_code_emit_op,create_cut_targets_def])) >>
      rpt gen_tac >> BETA_TAC >> irule create_cut_code_ignore_bind >>
      simp[compile_copy_memory_dynamic_def,create_cut_code_emit_void,create_cut_targets_def] >>
      ntac 3 (irule create_preparation_segments_case >>
              (reverse conj_tac >- simp[create_cut_code_emit_op,create_cut_targets_def]) >>
              rpt gen_tac >> BETA_TAC) >> simp[]) >>
  Cases >> gen_tac >> simp[] >>
  ntac 2 (irule create_preparation_segments_case >>
          (reverse conj_tac >- simp[]) >> rpt gen_tac >> BETA_TAC) >>
  irule create_dispatch_cut >> simp[]
QED

Theorem create_create_call_case:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
  (!ce vv ty a. create_cut_code {} a
     (SND (compile_create_snapshot ce vv ty a))) /\
  (!ce copy vv a. create_cut_code {} a
     (SND (compile_snapshot_vv ce copy vv a))) /\
  (!ce dst rows a. create_cut_code {} a
     (SND (compile_abi_encode_values_to_buf ce dst rows a))) /\
  (!ce ty e a. create_cut_code {} a
     (SND (lower_value cfn ce ty e a))) /\
  (!ce salt a. create_cut_code {} a
     (SND (compile_create_salt cfn ce salt a))) /\
  (!target value salt rof a. create_cut_code {} a
     (SND (compile_create_copy target value salt rof a))) /\
  (!target value salt offset code args_ptr args_len rof a.
     create_cut_code {} a
       (SND (compile_create_blueprint_append target value salt offset code
          args_ptr args_len rof a))) /\
  (!target a. create_cut_code {} a (SND (compile_create_proxy_buf target a))) /\
  (!created rof a. create_cut_code {} a
     (SND (compile_check_create_result created rof a))) ==>
  create_cut_code {} a
    (SND (compile_create_call cfn cenv ck has_salt rof args a))
Proof
  strip_tac >> Cases_on `args`
  >- simp[compile_create_call_def,comp_ignore_bind_def,comp_bind_def,
          comp_return_def,create_invalid_call_cut] >>
  rename1 `compile_create_call _ _ _ _ _ (_::rest) _` >> Cases_on `rest`
  >- simp[compile_create_call_def,comp_ignore_bind_def,comp_bind_def,
          comp_return_def,create_invalid_call_cut] >>
  rename1 `compile_create_call _ _ _ _ _ (_::_::rest) _` >>
  Cases_on `LENGTH rest < (if has_salt then 1 else 0) +
             (case ck of CreateFromBlueprint _ => 1 | _ => 0)`
  >- simp[compile_create_call_def,comp_ignore_bind_def,comp_bind_def,
          comp_return_def,create_invalid_call_cut] >>
  Cases_on `ck` >> fs[] >>
  FIRST (map irule [create_minimal_proxy_call_cut, create_copy_call_cut,
                    create_blueprint_call_cut, create_raw_call_cut]) >>
  simp[] >> Cases_on `has_salt` >> fs[]
QED
