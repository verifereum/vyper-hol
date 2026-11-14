(* Operand exclusion for external-call primitives, literals and conversions. *)
Theory runtimeLabelExprPrimitives
Ancestors
  runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_extcodesize_check:
  rb_operand_ok addr ==> rb_step (K T) (compile_extcodesize_check addr)
Proof
  strip_tac >> pure_rewrite_tac[compile_extcodesize_check_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_compile_return_value_decode:
  rb_step rb_operand_ok (compile_return_value_decode min_size max_size)
Proof
  pure_rewrite_tac[compile_return_value_decode_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_select]
QED

(* Decoder antecedent: conjunct 1 of runtimeLabelABI$rb_abi_decode. *)
Theorem rb_compile_default_return_path:
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
     rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_operand_ok buf /\ rb_operand_ok result /\ rb_operand_ok default_op /\
  rb_operand_ok addr ==>
  rb_step rb_operand_ok
    (compile_default_return_path ce rty dty buf result default_op addr
       skip min_size max_size info)
Proof
  strip_tac >> pure_rewrite_tac[compile_default_return_path_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_store_memory] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `skip` >> simp[rb_step_return, rb_compile_extcodesize_check]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_return_value_decode] >>
  gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_new_block, rb_step_return]
QED

Theorem rb_compile_multi_vvs:
  !es. (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_value_ok) (compile_multi_vvs cfn ce es)
Proof
  Induct >> simp[compile_multi_vvs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_extcall_store_values:
  !args buf off. rb_env_ok ce /\ EVERY (rb_value_ok o FST) args /\
  rb_operand_ok buf ==>
  rb_step (K T) (compile_extcall_store_values ce args buf off)
Proof
  Induct >> simp[compile_extcall_store_values_def, rb_step_return] >>
  gen_tac >> gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  pure_rewrite_tac[compile_extcall_store_values_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[] >>
  Cases_on `is_word_type h1` >> simp[rb_emit_void] >>
  Cases_on `is_bytestring_type h1` >>
  simp[rb_emit_void, rb_compile_store_bytestring]
QED

(* ABI antecedents are rb_abi_encode conjunct 2 and rb_abi_decode conjunct 1. *)
Theorem rb_compile_external_call_kwargs:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\
     rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_env_ok ce /\ EVERY (rb_value_ok o FST) (ZIP (avs,tys)) /\ rb_operand_ok addr /\
  rb_operand_ok value /\ rb_operand_ok gas /\ rb_operand_ok default_op ==>
  rb_step rb_operand_ok
    (compile_external_call_kwargs ce addr avs tys msz asz mid rsz minsz rmsz
       static value gas skip has_default default_op rty dty enc_info dec_info)
Proof
  strip_tac >> pure_rewrite_tac[compile_external_call_kwargs_def, LET_THM] >>
  BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- suspend "args" >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `rty = NoneT /\ ~skip` >>
      simp[rb_step_return, rb_compile_extcodesize_check]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `static` >> simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  suspend "result"
QED

Resume rb_compile_external_call_kwargs[args]:
  Cases_on `avs = []` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (irule rb_compile_extcall_store_values >> simp[]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_emit_op]
QED

Resume rb_compile_external_call_kwargs[result]:
  Cases_on `rty = NoneT` >> simp[rb_step_return] >>
  Cases_on `has_default` >> simp[]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_compile_default_return_path >> simp[]) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_return_value_decode] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_step_return]
QED

Finalise rb_compile_external_call_kwargs

Theorem rb_compile_dynarray_append:
  !base v ce ws sz dty sty cap prim loc.
  rb_operand_ok base /\ rb_operand_ok v /\
  (case ce.ce_imm_alloca of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step (K T)
    (compile_dynarray_append ce base v ws sz dty sty cap prim loc)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_dynarray_append_def, LET_THM] >>
  BETA_TAC >>
  irule rb_bind_ptr_load >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `prim` >> simp[rb_compile_ptr_store] >>
      Cases_on `loc = LocMemory` >> simp[]
      >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_memory, rb_step_return]) >>
      Cases_on `loc = LocCode` >> simp[rb_compile_imm_store_words, cj 1 rb_slots]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_compile_ptr_store]
QED

Theorem rb_compile_dynarray_pop:
  !base imm ws sz ctor loc. rb_operand_ok base /\ (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step rb_operand_ok (compile_dynarray_pop base ws sz ctor imm loc)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_dynarray_pop_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_ptr_load] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_ptr_store] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_store_multi_results:
  !ops buf off. EVERY rb_operand_ok ops /\ rb_operand_ok buf ==>
  rb_step (K T) (store_multi_results buf ops off)
Proof
  Induct >> simp[store_multi_results_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void]
QED

Theorem rb_compile_array_subscript:
  !base idx dyn count ws sz signed loader.
  rb_operand_ok base /\ rb_operand_ok idx /\
  (!p. rb_operand_ok p ==> rb_step rb_operand_ok (loader p)) ==>
  rb_step rb_operand_ok
    (compile_array_subscript base idx dyn count ws sz signed loader)
Proof
  rpt strip_tac >> pure_rewrite_tac[compile_array_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `dyn` >> simp[rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `signed` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `dyn` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_tuple_subscript:
  !base off. rb_operand_ok base ==>
  rb_step rb_operand_ok (compile_tuple_subscript base off)
Proof
  simp[compile_tuple_subscript_def, rb_emit_op]
QED

Theorem rb_compile_store_byte_chunks:
  !p bs off. rb_operand_ok p ==>
  rb_step (K T) (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def, rb_step_return] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void] >>
  gvs[]
QED

Theorem rb_compile_bytelike_literal:
  rb_step rb_buffer_ok (compile_bytelike_literal bs maxlen)
Proof
  pure_rewrite_tac[compile_bytelike_literal_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_byte_chunks, rb_step_return,
                          rb_buffer_ok_def]
QED

Theorem rb_compile_literal_vv:
  !ty lit. rb_step rb_value_ok (compile_literal_vv ty lit)
Proof
  gen_tac >> Cases >> simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def]
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def])
  >- (Cases_on `ty` >> simp[compile_literal_vv_def] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      simp[rb_compile_bytelike_literal, rb_step_return, rb_buffer_ok_def,
           base_ptr_def, rb_value_ok_def, rb_ptr_ok_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[compile_literal_vv_def, rb_step_return, rb_value_ok_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  simp[rb_compile_bytelike_literal, rb_step_return, rb_buffer_ok_def,
       base_ptr_def, rb_value_ok_def, rb_ptr_ok_def]
QED

Theorem rb_compile_name_vv:
  rb_env_ok ce ==> rb_step rb_value_ok (compile_name_vv ce ty id)
Proof
  strip_tac >> pure_rewrite_tac[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return, rb_value_ok_def]) >>
  rename1 `SOME loc` >>
  `rb_location_ok loc` by (gvs[rb_env_ok_def] >> metis_tac[]) >>
  Cases_on `loc` >>
  gvs[rb_location_ok_def, rb_step_return, rb_value_ok_def, rb_mk_ptr] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return, rb_value_ok_def]
QED

Theorem rb_compile_env_var:
  !ev. rb_step rb_operand_ok (compile_env_var ev)
Proof
  Cases >> simp[compile_env_var_def, rb_emit_op] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_load_bytestring_as_word:
  rb_operand_ok v ==>
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (load_bytestring_as_word v opc)
Proof
  strip_tac >> pure_rewrite_tac[load_bytestring_as_word_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `opc = SAR` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_int_clamp:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_int_clamp signed bits v)
Proof
  strip_tac >> Cases_on `signed` >>
  simp[compile_int_clamp_def]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_bytestring_widen_copy:
  rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_bytestring_widen_copy dst_size v src_size)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_widen_copy_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_copy_memory, rb_step_return]
QED

Theorem rb_compile_neg:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_neg v ty)
Proof
  strip_tac >> simp[compile_neg_def] >>
  Cases_on `type_bounds ty` >> simp[] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED


Theorem rb_compile_store_words:
  !vs buf off. EVERY rb_operand_ok vs /\ rb_operand_ok buf ==>
  rb_step (K T) (compile_store_words buf vs off)
Proof
  Induct >> simp[compile_store_words_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `off = 0` >> simp[rb_step_return, rb_emit_op]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void]
QED

Theorem rb_compile_invert:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_invert v ty ce)
Proof
  Cases_on `ty` >> simp[compile_invert_def, rb_emit_op]
QED

Theorem rb_compile_type_convert:
  !conv v. rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_type_convert v conv)
Proof
  Cases >> rpt strip_tac
  >~ [`compile_type_convert v ConvIdentity`] >- simp[compile_type_convert_def, rb_step_return]
  >~ [`compile_type_convert v ConvToBool`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBoolToDecimal n)`]
  >- simp[compile_type_convert_def, rb_emit_op]
  >~ [`compile_type_convert v (ConvToFlag n)`]
  >- (Cases_on `n < 256` >> simp[compile_type_convert_def, rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v ConvToAddress`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytestringCast n m)`]
  >- (simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesMToBytesM n m)`]
  >- (simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v ConvBytestringToBool`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBytestringToBytesM n)`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[rb_emit_op])
  >~ [`compile_type_convert v (ConvBytestringToInt b n m)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >> IF_CASES_TAC >>
      simp[rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesToInt m b n)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> IF_CASES_TAC >> simp[rb_compile_int_clamp, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesToAddress n)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToBytesM b n m)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      conj_tac >- simp[rb_emit_op] >>
      Cases_on `n > m * 8` >> simp[rb_step_return] >>
      Cases_on `b` >> simp[] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToInt b n c m)`]
  >- (Cases_on `b` >> Cases_on `c` >>
      Cases_on `m < n` >> simp[compile_type_convert_def] >>
      simp[rb_compile_int_clamp, rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytesMToDecimal m d lo hi)`]
  >- (pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvBytestringToDecimal d lo hi n)`]
  >- (pure_rewrite_tac[compile_type_convert_def] >>
      irule rb_step_bind >>
      qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >>
      BETA_TAC >> reverse conj_tac >- simp[rb_load_bytestring_as_word] >>
      Cases >> simp[] >> strip_tac >> IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return])
  >~ [`compile_type_convert v (ConvIntToDecimal b n d lo hi)`]
  >- suspend "int_decimal"
  >> suspend "decimal_int"
QED

Resume rb_compile_type_convert[int_decimal]:
  pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  simp[rb_emit_op]
QED

Resume rb_compile_type_convert[decimal_int]:
  pure_rewrite_tac[compile_type_convert_def, LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_void]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- (Cases_on `b` >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  simp[rb_emit_op]
QED
Finalise rb_compile_type_convert
