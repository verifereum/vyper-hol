(* Fixed, callback-free preparation intervals for CREATE forms. *)
Theory createSizeFixedPreparation
Ancestors
  createSizeCutCode createSizeCutOpens createSizeConcreteSnapshots createSizeEncodeCode
  createSizeCreateLayoutCode createSizeLocationCode createSizeTypedCopyCode
  dallocaCreateGeometry builtinCreate exprLowering context compileEnv emitHelper
  venomInst pair list

fun fixed_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_THM,
                  create_cut_code_emit_inst, create_cut_code_emit_op,
                  create_cut_code_emit_void, create_cut_targets_def])),
              irule create_alloc_buffer_cut_code, irule create_cut_code_bind,
              irule create_cut_code_ignore_bind, conj_tac]);

Theorem create_fixed_preparation_intervals:
  (!ce vv ty a.
    create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))) /\
  (!cfn.
    (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) ==>
    !cenv es a.
      create_cut_code {} a (SND (compile_create_ctor_args cfn cenv es a))) /\
  (!cfn.
    (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) /\
    (!ce copy vv a. create_cut_code {} a
      (SND (compile_snapshot_vv ce copy vv a))) /\
    (!ce dst rows a. create_cut_code {} a
      (SND (compile_abi_encode_values_to_buf ce dst rows a))) ==>
    !cenv raw_args later_es args a.
      create_cut_code {} a
        (SND (compile_create_blueprint_args cfn cenv raw_args later_es args a))) /\
  (!ce target a.
    create_cut_code {} a (SND (compile_create_proxy_buf target a))) /\
  (!is_lit target off a.
    create_cut_code {} a
      (SND (compile_create_blueprint_check is_lit target off a))) /\
  (!ce dst rows a.
    create_cut_code {} a
      (SND (compile_abi_encode_values_to_buf ce dst rows a)))
Proof
  rpt conj_tac
  >- simp[create_bytecode_snapshot_cut_code]
  >- (rpt gen_tac >> disch_tac >> rpt gen_tac >>
      irule create_ctor_args_cut >>
      (conj_tac >- simp[create_vv_snapshot_cut_code] >- metis_tac[]))
  >- (rpt gen_tac >> disch_tac >> irule create_blueprint_args_cut >>
      simp[create_bytecode_snapshot_cut_code, create_vv_snapshot_cut_code,
           create_encode_values_cut_code])
  >- (rpt gen_tac >> fixed_steps [compile_create_proxy_buf_def])
  >- (rpt gen_tac >> Cases_on `is_lit` >> rw[compile_create_blueprint_check_def] >>
      irule create_cut_code_bind >>
      (conj_tac >- (irule create_cut_code_emit_op >> simp[create_cut_targets_def])
       >- (rpt gen_tac >> BETA_TAC >> fixed_steps [])))
  >> simp[create_encode_values_cut_code]
QED
