Theory bodyPtrStructLitOwnershipCallStaging
Ancestors bodyPtrStructLitOwnershipConsumers bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipAbiEncode
  bodyPtrStructLitOwnershipAbiDecode bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipPrimitives
  exprLowering context compileEnv list

Theorem alloc_run_store_multi_results:
  !ops buf off.
  alloc_run fresh_outputs (store_multi_results buf ops off)
    (\v s. fresh_outputs s)
Proof
  Induct >> rpt gen_tac >>
  simp[store_multi_results_def, comp_ignore_bind_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
    gen_tac >> simp[]) >>
  first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]
QED

Theorem alloc_run_compile_extcall_store_values:
  !vals buf off.
  alloc_run fresh_outputs (compile_extcall_store_values ce vals buf off)
    (\v s. fresh_outputs s)
Proof
  Induct
  >- simp[compile_extcall_store_values_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_ignore_bind_def] >>
  ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_unwrap_value] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
           SRULE [SF ETA_ss] alloc_run_compile_store_bytestring]) >>
  gen_tac >> first_x_assum (mp_tac o SRULE [SF ETA_ss]) >>
  simp[SF ETA_ss]
QED

Theorem alloc_run_compile_return_value_decode:
  alloc_run fresh_outputs (compile_return_value_decode buf minsz maxsz)
    (\v s. fresh_outputs s)
Proof
  simp[compile_return_value_decode_def, comp_ignore_bind_def] >>
  ntac 6 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_select] >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_extcodesize_check:
  alloc_run fresh_outputs (compile_extcodesize_check addr)
    (\v s. fresh_outputs s)
Proof
  simp[compile_extcodesize_check_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
       SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_stage_intcall_args:
  !vals flags tys.
  alloc_run fresh_outputs (compile_stage_intcall_args ce vals flags tys)
    (\v s. fresh_outputs s)
Proof
  Induct
  >- simp[compile_stage_intcall_args_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  rpt gen_tac >> namedCases_on `flags` ["", "flag flags_tail"] >>
  Cases_on `tys` >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def] >>
  TRY (Cases_on `flag` >>
       simp[compile_stage_intcall_args_def, comp_ignore_bind_def]) >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
   reverse conj_tac
   >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_unwrap_value] >>
   gen_tac >> simp[]) 
  >~ [`compile_alloc_buffer _`] >- suspend "memory" >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
   reverse conj_tac
   >- (first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Resume alloc_run_compile_stage_intcall_args[memory]:
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >>
  gen_tac >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
           SRULE [SF ETA_ss] alloc_run_compile_store_memory] >>
      irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_bytestring] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Finalise alloc_run_compile_stage_intcall_args

Theorem alloc_run_compile_default_return_path:
  alloc_run fresh_outputs
    (compile_default_return_path ce rt dt buf result def addr skip minsz maxsz info)
    (\v s. fresh_outputs s)
Proof
  Cases_on `skip` >>
  simp[compile_default_return_path_def, comp_ignore_bind_def] >>
  (ntac 15 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss, EVERY_DEF]
          (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
        SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
        SRULE [SF ETA_ss] alloc_run_new_block_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_store_memory,
        SRULE [SF ETA_ss] alloc_run_compile_extcodesize_check,
        SRULE [SF ETA_ss] alloc_run_compile_return_value_decode,
        SRULE [SF ETA_ss] alloc_run_compile_abi_decode_to_buf] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_compile_external_call_kwargs:
  alloc_run fresh_outputs
    (compile_external_call_kwargs ce addr vals tys memsz abisz mid retsz
      minsz retmem static value gas skip hasdef def rt dt encinfo decinfo)
    (\v s. fresh_outputs s)
Proof
  simp[compile_external_call_kwargs_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss, EVERY_DEF]
          (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
        SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
        SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
    gen_tac >> simp[comp_ignore_bind_def, comp_bind_assoc]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- suspend "args" >> gen_tac >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (rpt IF_CASES_TAC >> simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss, EVERY_DEF]
          (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
        SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
        SRULE [SF ETA_ss] alloc_run_new_block_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_extcodesize_check] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[comp_ignore_bind_def, comp_bind_assoc]) >>
  suspend "result"
QED

Resume alloc_run_compile_external_call_kwargs[args]:
  IF_CASES_TAC
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  ntac 4 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_compile_extcall_store_values,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_abi_encode_to_buf] >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_compile_external_call_kwargs[result]:
  Cases_on `retsz = 0`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  Cases_on `hasdef` >> simp[] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_compile_return_value_decode,
        SRULE [SF ETA_ss] alloc_run_compile_abi_decode_to_buf] >>
    gen_tac >> simp[]) >>
   simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_default_return_path] >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED
Finalise alloc_run_compile_external_call_kwargs
