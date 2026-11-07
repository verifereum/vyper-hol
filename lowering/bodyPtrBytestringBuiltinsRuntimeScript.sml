Theory bodyPtrBytestringBuiltinsRuntime
Ancestors
  bodyPtrBytestringBuiltinsPtrFrame bodyPtrDefs valueEncodingProofs

Theorem order_ptr_runtime_tx_obstruction:
  order_ptr_cx.txn.block_number = 0 /\
  ~tx_env_ok order_ptr_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_ptr_runtime_no_state_rel:
  ~state_rel func order_ptr_env order_ptr_cx es s
Proof
  simp[compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def,
       order_ptr_runtime_tx_obstruction]
QED

(* Separate witness constants preserve the checked zero-block experiment. *)
Definition order_runtime_cx_def:
  order_runtime_cx = order_ptr_cx with txn :=
    order_ptr_cx.txn with <|block_number := 1; block_hashes := [0w]|>
End

Definition order_runtime_start_def:
  order_runtime_start = order_ptr_start with vs_block_ctx :=
    order_ptr_start.vs_block_ctx with bc_number := 1w
End

Theorem order_runtime_tx_ok:
  tx_env_ok order_runtime_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_runtime_call_context:
  call_ctx_rel order_runtime_cx.txn order_runtime_start.vs_call_ctx
    order_runtime_start.vs_tx_ctx order_runtime_start.vs_block_ctx
Proof
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem order_runtime_array_wf:
  val_wf (ArrayTV (BaseTV AddressT) (Dynamic 2))
    (ArrayV (DynArrayV [AddressV 1w; AddressV 2w]))
Proof
  EVAL_TAC
QED

Theorem order_runtime_array_memory:
  val_in_memory (ArrayTV (BaseTV AddressT) (Dynamic 2))
    (ArrayV (DynArrayV [AddressV 1w; AddressV 2w]))
    128 order_runtime_start.vs_memory
Proof
  simp_tac pure_ss [order_runtime_start_def,
    venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  simp[valueEncodingTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def,
       valueEncodingPropsTheory.mem_word_at_eq_mload,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_array] >>
  simp[valueEncodingTheory.typed_val_to_w256_def,
       GSYM valueEncodingProofsTheory.word_to_bytes_w2w_address,
       byteTheory.word_of_bytes_be_def,
       vfmTypesTheory.word_to_bytes_word_of_bytes_256, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  simp[bitTheory.BITS_THM, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem order_runtime_local_ptrs:
  local_ptrs_rel func order_ptr_env order_ptr_source.scopes order_runtime_start
Proof
  simp[compileEnvTheory.local_ptrs_rel_def,
       compileEnvTheory.local_region_def,
       bodyPtrBytestringBuiltinsPtrFrameTheory.order_ptr_source_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_env_def,
       vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> qexists_tac `128w` >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256,
       order_runtime_array_wf, order_runtime_array_memory,
       valueEncodingTheory.type_memory_size_def] >>
  simp[compileEnvTheory.local_backed_def, order_runtime_start_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_def,
       bodyPtrBytestringBuiltinsOrderRunTheory.order_run_start_def,
       venomStateTheory.init_venom_state_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_runtime_state_rel:
  state_rel func order_ptr_env order_runtime_cx order_ptr_source order_runtime_start
Proof
  simp[compileEnvTheory.state_rel_def, order_runtime_local_ptrs,
       order_runtime_call_context] >>
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem order_runtime_body_inv:
  body_inv [] order_frame_unit.cu_context order_ptr_env order_runtime_cx
Proof
  mp_tac order_ptr_body_inv >>
  simp[bodySimTheory.body_inv_def, order_runtime_cx_def,
       vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def]
QED

Theorem order_runtime_sim_inv:
  exprSimHypsDefs$expr_sim_inv order_ptr_env order_runtime_cx
    order_ptr_tenv order_ptr_source
Proof
  mp_tac order_ptr_sim_inv >>
  simp[exprSimHypsDefsTheory.expr_sim_inv_def, order_runtime_cx_def,
       vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def] >>
  strip_tac >> simp[] >> EVAL_TAC >> rw[] >> gvs[AllCaseEqs()] >>
  fs[vyperStateTheory.lookup_flag_def,
     vyperInterpreterTheory.lookup_function_def] >>
  EVAL_TAC >> simp[finite_mapTheory.FUNION_FEMPTY_1, wordsTheory.dimword_def]
QED

Theorem order_runtime_call_safety:
  call_evaluation_safe order_runtime_cx []
Proof
  simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
       order_runtime_cx_def, order_ptr_cx_def] >>
  qexists_tac `[]` >> EVAL_TAC >> rw[] >> gvs[AllCaseEqs()] >>
  fs[vyperInterpreterTheory.lookup_function_def] >>
  simp[relationTheory.irreflexive_def, Once relationTheory.TC_CASES1,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem order_runtime_body_pre:
  exprSimHypsDefs$expr_body_pre order_ptr_env order_runtime_cx order_ptr_tenv
    bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr order_ptr_source
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, order_runtime_sim_inv,
       order_ptr_frame_expr_typed, order_runtime_call_safety,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_no_internal_calls,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_byte_widths,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_alloc_limits,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_no_evm_run] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[order_runtime_cx_def, order_ptr_cx_def,
       bodyPtrBytestringBuiltinsSourceFrameTheory.order_frame_cx_def,
       gasContextTheory.cx_tops_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def] >>
  EVAL_TAC >> simp[]
QED

Theorem order_runtime_ghost:
  ghost_inv NONE order_ptr_env order_runtime_cx order_ptr_source
    (FEMPTY |+ ("arr_ptr",(128,96))) entry_taint order_runtime_start
Proof
  simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
       ptrDisciplineTheory.entry_taint_def,
       bodyPtrBytestringBuiltinsPtrFrameTheory.order_ptr_source_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_env_def,
       bodyPtrBytestringBuiltinsOrderRunTheory.order_run_env_def,
       vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[ptrDisciplineTheory.op_taint_def] >-
   (simp[ptr_covers_def, ptrDisciplineTheory.op_taint_def,
         order_runtime_start_def,
         bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
         wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  gvs[order_runtime_start_def,
      bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  simp[order_runtime_array_wf] >>
  qexistsl_tac [`96`, `order_runtime_start.vs_memory`] >>
  simp[order_runtime_array_wf, order_runtime_array_memory,
       valueEncodingTheory.type_memory_size_def, order_runtime_start_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_def] >>
  irule listTheory.LIST_EQ >>
  simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at] >> rpt strip_tac >>
  fs[mem_agree_outside_def] >>
  first_x_assum (qspec_then `128 + x` mp_tac) >>
  simp[listTheory.LIST_EQ_REWRITE, valueEncodingProofsTheory.EL_mem_bytes_at]
QED

(* The corrected runtime uses the pointer-based emitted fragment, with STOP
   solely as an observation continuation. *)
Definition order_runtime_fn_def:
  order_runtime_fn = mk_raw_function "f"
    [<|bb_label := "entry";
       bb_instructions := (SND order_ptr_compiled).cs_current_insts ++
         [mk_inst 22 STOP [] []]|>]
End

Theorem order_runtime_function_absent:
  lookup_function order_runtime_fn.fn_name
    order_frame_unit.cu_context.ctx_functions = NONE
Proof
  EVAL_TAC >> simp[listTheory.INDEX_FIND_def]
QED

Theorem order_runtime_no_stmt_state:
  ~stmt_state_rel order_frame_unit.cu_context order_runtime_fn order_ptr_env
    order_runtime_cx order_ptr_source s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.alloca_room_def, order_runtime_function_absent]
QED
