(* Guarded mutual branch confinement, conditional on the CREATE layout rule. *)
Theory createSizeOperandMutual
Ancestors
  createSizeExprBodyCode createSizeBuiltinBodyCode createSizeTypeBuiltinCode
  createSizeCallCode createSizeExternalReturnCode createSizeConcreteSnapshots
  createSizeEncodeCode createSizeDecodeCode createSizeLocationCode
  createSizeTypedCopyCode createSizeCutCode exprLowering exprCallBounds

Theorem create_operand_mutual_if_create:
  (!cfn cenv ck has_salt rof args a.
     (!ce ty e u. create_cut_code {} u (SND (cfn ce ty e u))) ==>
     create_cut_code {} a (SND (compile_create_call cfn cenv ck has_salt rof args a))) ==>
  ((!ce ty e a. create_cut_code {} a (SND (compile_expr ce ty e a))) /\
   (!ce ret_ty ty bi args a.
      create_cut_code {} a (SND (compile_builtin_dispatch ce ret_ty ty bi args a))) /\
   (!ce vv_ty ty tb rt args a.
      create_cut_code {} a (SND (compile_type_builtin_dispatch ce vv_ty ty tb rt args a))))
Proof
  strip_tac >> ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume create_operand_mutual_if_create[expr]:
  simp_tac std_ss [Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule create_expr_body_cut_code >>
  simp_tac std_ss [create_unwrap_cut_code, create_store_memory_cut_code,
                   create_vv_snapshot_cut_code] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
      irule create_noncreate_call_case >>
      simp_tac std_ss [create_unwrap_cut_code, create_store_memory_cut_code,
                       create_vv_snapshot_cut_code] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (rpt gen_tac >> irule create_external_kwargs_case >>
          simp[create_encode_values_cut_code, create_decode_to_buf_cut_code,
               create_store_memory_cut_code, create_cut_targets_def]) >>
      qexists_tac `ann` >> REFL_TAC) >>
  rpt gen_tac >> strip_tac >> first_assum irule >>
  rpt gen_tac >> simp_tac std_ss [expr_child_callback_def] >>
  IF_CASES_TAC >- metis_tac[] >>
  simp[invalid_expr_call_def, LET_DEF, pairTheory.UNCURRY_VAR,
       create_cut_code_emit_inst, create_cut_targets_def]
QED

Resume create_operand_mutual_if_create[builtin]:
  simp_tac std_ss [Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule create_builtin_body_cut_code >>
  simp[create_unwrap_cut_code, create_store_memory_cut_code]
QED

Resume create_operand_mutual_if_create[type_builtin]:
  simp_tac std_ss [Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule create_type_builtin_body_cut_code >>
  simp[create_unwrap_cut_code, create_encode_payload_cut_code,
       create_decode_to_buf_cut_code, create_cut_targets_def] >>
  rpt gen_tac >> irule create_ext_call_args_case >>
  simp[create_vv_snapshot_cut_code]
QED

Finalise create_operand_mutual_if_create
