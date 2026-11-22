(* Branch confinement for ABI value-row and payload encoding. *)
Theory createSizeEncodeRowsCode
Ancestors
  createSizeCutCode exprLowering context builtinAbi emitHelper pair list

fun encode_row_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_op,
                  create_cut_code_emit_void, create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac, IF_CASES_TAC]);

Theorem create_encode_rows_case[local]:
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!src dst ty src_ty a. create_cut_code {} a
      (SND (compile_store_memory ce src dst ty src_ty a))) /\
  (!dst src info a. create_cut_code {} a
      (SND (compile_abi_encode_to_buf dst src info a))) ==>
  !rows dst cursor static_ofst a. create_cut_code {} a
     (SND (compile_abi_encode_value_rows ce dst cursor static_ofst rows a))
Proof
  strip_tac >> Induct >> simp[compile_abi_encode_value_rows_def] >>
  Cases >> rpt strip_tac >>
  encode_row_steps [compile_abi_encode_value_rows_def]
QED

Theorem create_encode_values_case:
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!src dst ty src_ty a. create_cut_code {} a
      (SND (compile_store_memory ce src dst ty src_ty a))) /\
  (!dst src info a. create_cut_code {} a
      (SND (compile_abi_encode_to_buf dst src info a))) ==>
  create_cut_code {} a (SND (compile_abi_encode_values_to_buf ce dst rows a))
Proof
  strip_tac >> drule_all create_encode_rows_case >> strip_tac >>
  encode_row_steps [compile_abi_encode_values_to_buf_def, compile_alloc_buffer_def]
QED

Theorem create_encode_payload_case:
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!src dst ty src_ty a. create_cut_code {} a
      (SND (compile_store_memory ce src dst ty src_ty a))) /\
  (!dst src info a. create_cut_code {} a
      (SND (compile_abi_encode_to_buf dst src info a))) ==>
  create_cut_code {} a (SND (compile_abi_encode_payload ce single vals tys dst a))
Proof
  strip_tac >> Cases_on `single` >> simp[compile_abi_encode_payload_def]
  >- encode_row_steps [] >>
  irule create_encode_values_case >> simp[]
QED
