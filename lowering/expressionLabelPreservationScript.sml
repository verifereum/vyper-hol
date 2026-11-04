(* Expression helper compilation preserves only the CFG extension and labels. *)
Theory expressionLabelPreservation
Ancestors
  decoderLabelPreservation entryLabelPreservation exprLowering compileEnv
  loweringShapeDefs emitHelper list abiEncoder

val label_simps = [label_preserving_return, label_preserving_emit_inst,
  label_preserving_emit_op, label_preserving_emit_void];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;

Theorem label_preserving_compile_clamp:
  !s r t. compile_clamp v ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_clamp_def] >>
  simp_tac pure_ss [LET_THM] >> pairarg_tac >>
  asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  IF_CASES_TAC
  >- (ntac 5 LABEL_BIND >> LABEL_LEAF) >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_clamp_and_return:
  !s r t. clamp_and_return v ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[clamp_and_return_def] >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_compile_clamp] >> LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_compile_clamp,
  label_preserving_clamp_and_return];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;

Theorem label_preserving_safe_add_sub:
  (!s r t. compile_safe_add x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) /\
  (!s r t. compile_safe_sub x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t))
Proof
  conj_tac >> rewrite_tac[compile_safe_add_def, compile_safe_sub_def] >>
  simp_tac pure_ss [LET_THM] >> LABEL_BIND >> IF_CASES_TAC
  >- LABEL_LEAF
  >- (IF_CASES_TAC
      >- (ntac 3 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF) >>
      ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF)
  >- LABEL_LEAF >>
  IF_CASES_TAC
  >- (ntac 3 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF) >>
  ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_mul_overflow_check:
  !s r t. compile_mul_overflow_check x y res signed bits s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_mul_overflow_check_def] >>
  simp_tac pure_ss [LET_THM] >> ntac 4 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (ntac 5 LABEL_BIND >> LABEL_LEAF) >> LABEL_LEAF) >>
  gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_safe_decimal_div:
  !s r t. compile_safe_decimal_div x y divisor ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_safe_decimal_div_def] >> ntac 3 LABEL_BIND >>
  LABEL_IGNORE >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_safe_mul:
  !s r t. compile_safe_mul x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_safe_mul_def] >> simp_tac pure_ss [LET_THM] >>
  LABEL_BIND >> ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- metis_tac[label_preserving_mul_overflow_check] >> LABEL_LEAF) >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >>
  gen_tac >> IF_CASES_TAC >> LABEL_LEAF
QED

Theorem label_preserving_safe_div:
  !s r t. compile_safe_div x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_safe_div_def] >> ntac 2 LABEL_BIND >>
  LABEL_IGNORE >> IF_CASES_TAC
  >- (LABEL_BIND >> IF_CASES_TAC
      >- (ntac 5 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF) >>
      IF_CASES_TAC >> LABEL_LEAF) >> LABEL_LEAF
QED

Theorem label_preserving_safe_mod:
  !s r t. compile_safe_mod x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_safe_mod_def] >> ntac 2 LABEL_BIND >>
  LABEL_IGNORE >> IF_CASES_TAC >> LABEL_LEAF
QED

Theorem label_preserving_safe_pow:
  !s r t. compile_safe_pow x y ty base_lit exp_lit s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_safe_pow_def] >> simp_tac pure_ss [LET_THM] >>
  Cases_on `base_lit`
  >- (simp_tac (srw_ss()) [LET_THM] >> Cases_on `exp_lit`
      >- (simp_tac (srw_ss()) [LET_THM] >> LABEL_BIND >>
          ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
          >- metis_tac[label_preserving_compile_clamp] >> LABEL_LEAF) >>
      simp_tac (srw_ss()) [LET_THM] >> IF_CASES_TAC
      >- (LABEL_IGNORE >> LABEL_LEAF) >> IF_CASES_TAC
      >- (simp_tac pure_ss [LET_THM] >> ntac 5 LABEL_BIND >>
          LABEL_IGNORE >> LABEL_LEAF) >>
      ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF) >>
  simp_tac (srw_ss()) [LET_THM] >> IF_CASES_TAC
  >- (ho_match_mp_tac label_preserving_bind >> conj_tac
      >- (IF_CASES_TAC >- (LABEL_BIND >> LABEL_LEAF) >> LABEL_LEAF) >>
      gen_tac >> LABEL_IGNORE >> LABEL_LEAF) >>
  simp_tac pure_ss [LET_THM] >> ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_select:
  !s r t. compile_select c x y s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinSimpleTheory.compile_select_def] >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_wrap_truncate:
  !s r t. wrap_truncate v ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[wrap_truncate_def] >> IF_CASES_TAC
  >- (IF_CASES_TAC >> LABEL_LEAF) >> LABEL_LEAF
QED

Theorem label_preserving_compare:
  !s r t. compile_compare op x y ty s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp_tac (srw_ss()) [compile_compare_def, LET_THM,
                       comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_safe_add_sub,
  label_preserving_safe_mul, label_preserving_safe_div,
  label_preserving_safe_decimal_div, label_preserving_safe_mod,
  label_preserving_safe_pow, label_preserving_wrap_truncate,
  label_preserving_compare, label_preserving_select];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;

Theorem label_preserving_binop:
  !s r t. compile_binop op x y ty bl el s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `op` >>
  simp_tac (srw_ss()) [compile_binop_def, LET_THM,
                       comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_bytestring_hash:
  !s r t. compile_bytestring_hash p s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_bytestring_hash_def] >> ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_list_membership:
  (!s r t. compile_list_membership_in needle xs s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) /\
  (!s r t. compile_list_membership_notin needle xs s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t))
Proof
  Induct_on `xs` >> simp_tac (srw_ss())
    [compile_list_membership_in_def, compile_list_membership_notin_def]
  >- (conj_tac >> LABEL_LEAF) >>
  Cases_on `xs` >> simp_tac (srw_ss())
    [compile_list_membership_in_def, compile_list_membership_notin_def]
  >- (gen_tac >> conj_tac >> rpt LABEL_BIND >> LABEL_LEAF) >>
  gen_tac >> conj_tac >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_mapping_subscript:
  !s r t. compile_mapping_subscript slot key s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_mapping_subscript_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_abi_alloc_buffer] >> gen_tac >>
  simp_tac pure_ss [LET_THM] >> LABEL_IGNORE >> LABEL_BIND >>
  LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_keccak256_key:
  !s r t. compile_keccak256_key key is_bytes32 s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_keccak256_key_def] >> IF_CASES_TAC
  >- (ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_abi_alloc_buffer] >> gen_tac >>
      simp_tac pure_ss [LET_THM] >> LABEL_IGNORE >> LABEL_LEAF) >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

val label_simps = [label_preserving_return, label_preserving_emit_inst,
  label_preserving_emit_op, label_preserving_emit_void,
  label_preserving_fresh_var, label_preserving_new_block,
  label_preserving_abi_alloc_buffer];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;
val LABEL_FRESH = ho_match_mp_tac
    (Q.ISPEC `jump_label_ok` label_preserving_bind_result) >> conj_tac
  >- metis_tac[label_preserving_fresh_label] >> gen_tac >> strip_tac;

Theorem label_preserving_array_membership_loop:
  (!v s r t. loader v s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_array_membership_loop needle arr len sz off loader isin s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_array_membership_loop_def] >>
  LABEL_BIND >> ntac 6 LABEL_FRESH >>
  rewrite_tac[comp_ignore_bind_def] >> ntac 11 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >>
  rpt LABEL_BIND >> IF_CASES_TAC >> LABEL_LEAF
QED

Theorem label_preserving_ptr_load:
  !s r t. compile_ptr_load ctor imm loc v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp_tac (srw_ss()) [contextTheory.compile_ptr_load_def,
                       contextTheory.compile_imm_load_word_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_var_array_membership:
  !s r t. compile_var_array_membership cenv needle vv ty isin s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_var_array_membership_def] >>
  simp_tac pure_ss [LET_THM] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC
      >- metis_tac[label_preserving_ptr_load] >>
      Cases_on `ty` >> simp_tac (srw_ss()) []
      >- (pop_assum kall_tac >> rpt strip_tac >>
          drule label_preserving_return >> simp[])
      >- (pop_assum kall_tac >> rpt strip_tac >>
          drule label_preserving_return >> simp[])
      >- (Cases_on `b` >> simp_tac (srw_ss()) [] >>
          pop_assum kall_tac >> rpt strip_tac >>
          drule label_preserving_return >> simp[]) >>
      pop_assum kall_tac >> rpt strip_tac >>
          drule label_preserving_return >> simp[]) >>
  gen_tac >> ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (Cases_on `ty` >>
          CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
            (RATOR_CONV (SIMP_CONV (srw_ss()) [])))))
          >- (pop_assum kall_tac >> LABEL_LEAF)
          >- (pop_assum kall_tac >> LABEL_LEAF)
          >- (Cases_on `b` >>
              CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
                (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >>
              pop_assum kall_tac >> rpt LABEL_BIND >> LABEL_LEAF) >>
          pop_assum kall_tac >> LABEL_LEAF) >> LABEL_LEAF) >>
  ho_match_mp_tac label_preserving_array_membership_loop >>
  metis_tac[label_preserving_ptr_load]
QED

Theorem label_preserving_extcodesize_check:
  !s r t. compile_extcodesize_check addr s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_extcodesize_check_def] >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_return_value_decode:
  !s r t. compile_return_value_decode buf lo hi s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_return_value_decode_def, comp_ignore_bind_def] >>
  ntac 5 LABEL_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_select] >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_ptr_store:
  !s r t. compile_ptr_store ctor imm loc dst v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  pure_rewrite_tac [contextTheory.compile_ptr_store_def,
                   contextTheory.compile_imm_store_word_def] >>
  CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
    (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_word_copy_loop:
  !s r t. compile_word_copy_loop src dst n lloc sloc ctor s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_word_copy_loop_def] >>
  simp_tac pure_ss [LET_THM] >> ntac 3 LABEL_FRESH >>
  rewrite_tac[comp_ignore_bind_def] >> ntac 7 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_ptr_load] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_ptr_store] >> gen_tac >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_lit_byte_offset:
  !s r t. compile_lit_byte_offset v off s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_lit_byte_offset_def] >> IF_CASES_TAC
  >- LABEL_LEAF >> Cases_on `v` >> simp_tac (srw_ss()) [] >> LABEL_LEAF
QED

Theorem label_preserving_imm_copy_to_memory:
  !off s r t. compile_imm_copy_to_memory ctor imm src dst n off s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Induct_on `n` >> rewrite_tac[contextTheory.compile_imm_copy_to_memory_def]
  >- (gen_tac >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_lit_byte_offset] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_ptr_load, contextTheory.compile_ptr_load_def] >>
  gen_tac >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_lit_byte_offset] >> gen_tac >>
  LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_ensure_in_memory:
  !s r t. compile_ensure_in_memory v loc bytes n ctor imm s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `loc` >>
  rewrite_tac[contextTheory.compile_ensure_in_memory_def,
    contextTheory.compile_storage_to_memory_def,
    contextTheory.compile_transient_to_memory_def] >>
  CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
    (RATOR_CONV (SIMP_CONV (srw_ss()) [])))))
  >- LABEL_LEAF
  >- (LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >- (LABEL_BIND >> LABEL_LEAF) >>
          ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
          >- metis_tac[label_preserving_word_copy_loop] >> LABEL_LEAF) >> LABEL_LEAF)
  >- (LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >- (LABEL_BIND >> LABEL_LEAF) >>
          ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
          >- metis_tac[label_preserving_word_copy_loop] >> LABEL_LEAF) >> LABEL_LEAF)
  >- (LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
      >- metis_tac[label_preserving_imm_copy_to_memory] >> LABEL_LEAF) >>
  ntac 2 LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  LABEL_IGNORE >> ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_copy_memory:
  !s r t. compile_copy_memory dst src n s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `n` >> rewrite_tac[contextTheory.compile_copy_memory_def] >> LABEL_LEAF
QED

Theorem label_preserving_copy_memory_dynamic:
  !s r t. compile_copy_memory_dynamic dst src n s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_copy_memory_dynamic_def] >> LABEL_LEAF
QED

Theorem label_preserving_with_byte_offset:
  !s r t. compile_with_byte_offset v off s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_with_byte_offset_def] >>
  IF_CASES_TAC >> LABEL_LEAF
QED

Theorem label_preserving_bytestring_copy_len:
  !s r t. compile_bytestring_copy_len v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_bytestring_copy_len_def] >>
  ntac 2 LABEL_BIND >> simp_tac pure_ss [LET_THM] >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_store_bytestring:
  !s r t. compile_store_bytestring v dst s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_store_bytestring_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_bytestring_copy_len] >> gen_tac >> LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_copy_memory,
  label_preserving_copy_memory_dynamic, label_preserving_with_byte_offset,
  label_preserving_store_bytestring];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;

Theorem label_preserving_typed_copy_mutual:
  (!cenv dst dt src st s r t.
    compile_store_memory_typed cenv dst dt src st s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!cenv dst src dts sts doff soff s r t.
    compile_typed_copy_fields cenv dst src dts sts doff soff s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!cenv dst dt src st n s r t.
    compile_copy_sarray_typed cenv dst dt src st n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!cenv dst dt cap src st s r t.
    compile_copy_dynarray_typed cenv dst dt cap src st s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!cenv dst src dfs sfs doff soff s r t.
    compile_struct_typed_copy cenv dst src dfs sfs doff soff s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t))
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  conj_tac >- (rpt gen_tac >> rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >> LABEL_LEAF) >>
  conj_tac >- (rpt gen_tac >> rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >> LABEL_LEAF) >>
  conj_tac >- suspend "fields" >>
  conj_tac >- suspend "sarray" >>
  conj_tac >- suspend "dynarray" >>
  conj_tac >- (rpt gen_tac >> rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >> LABEL_LEAF) >>
  suspend "struct"
QED

Resume label_preserving_typed_copy_mutual[fields]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >>
  ntac 2 LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  LABEL_IGNORE >> LABEL_LEAF
QED

Resume label_preserving_typed_copy_mutual[struct]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >>
  simp_tac pure_ss [LET_THM] >> pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  ntac 2 LABEL_BIND >> LABEL_IGNORE >> LABEL_LEAF
QED

Resume label_preserving_typed_copy_mutual[sarray]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >>
  simp_tac pure_ss [LET_THM] >> IF_CASES_TAC >- LABEL_LEAF >>
  ntac 3 LABEL_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_typed_copy_mutual[dynarray]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >>
  simp_tac pure_ss [LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >> ntac 7 LABEL_BIND >>
  IF_CASES_TAC >- (LABEL_BIND >> LABEL_LEAF) >>
  ntac 3 LABEL_FRESH >> rewrite_tac[comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_typed_copy_mutual[dispatch]:
  ntac 5 gen_tac >> strip_tac >>
  rewrite_tac[Once contextTheory.compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (LABEL_BIND >> LABEL_LEAF) >>
  IF_CASES_TAC >- LABEL_LEAF >> IF_CASES_TAC >- LABEL_LEAF >>
  Cases_on `dt` >> Cases_on `st` >> gvs[] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac label_preserving_copy_memory >> gvs[] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[] >>
  metis_tac[label_preserving_copy_memory]
QED
Finalise label_preserving_typed_copy_mutual

Theorem label_preserving_store_memory:
  !s r t. compile_store_memory cenv src dst dt st s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[contextTheory.compile_store_memory_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  metis_tac[label_preserving_emit_void, label_preserving_store_bytestring,
    label_preserving_typed_copy_mutual, label_preserving_copy_memory]
QED

val label_simps = label_simps @ [label_preserving_store_memory,
  label_preserving_extcodesize_check, label_preserving_return_value_decode,
  label_preserving_abi_decode, label_preserving_ensure_in_memory,
  label_preserving_ptr_load];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- LABEL_LEAF;

Theorem label_preserving_default_return_path:
  !s r t. compile_default_return_path cenv rt dt buf res def addr skip lo hi info s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_default_return_path_def] >>
  ntac 2 LABEL_BIND >> ntac 3 LABEL_FRESH >>
  rewrite_tac[comp_ignore_bind_def] >> ntac 3 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >>
  LABEL_BIND >> LABEL_BIND >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt gen_tac >> Cases_on `r` >> metis_tac[label_preserving_abi_decode]) >>
  gen_tac >> LABEL_BIND >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_unwrap_value:
  !s r t. unwrap_value cenv vv s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `vv` >> rewrite_tac[unwrap_value_def] >- LABEL_LEAF >>
  IF_CASES_TAC >- LABEL_LEAF >> Cases_on `p.ptr_location` >>
  CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
    (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >>
  simp_tac pure_ss [LET_THM] >>
  rpt strip_tac >> metis_tac[label_preserving_return,
    label_preserving_ensure_in_memory]
QED

Theorem label_preserving_extcall_store_values:
  !vals buf off s r t.
    compile_extcall_store_values cenv vals buf off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct_on `vals` >- (rewrite_tac[compile_extcall_store_values_def] >> LABEL_LEAF) >>
  gen_tac >> PairCases_on `h` >> ntac 2 gen_tac >>
  rewrite_tac[compile_extcall_store_values_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_unwrap_value] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_multi_vvs:
  (!env ty e s r t. cfn env ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es s r t. compile_multi_vvs cfn cenv es s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct_on `es` >> rewrite_tac[compile_multi_vvs_def]
  >- LABEL_LEAF >> gen_tac >> LABEL_BIND >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_abi_encode_static:
  !s r t. compile_abi_encode_static dst src s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  LABEL_BIND >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_abi_encode_static_info:
  !s r t. compile_abi_encode_static_info dst src info s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `info` >> rewrite_tac[compile_abi_encode_static_info_def]
  >- metis_tac[label_preserving_abi_encode_static]
  >- LABEL_LEAF
  >- (rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >> LABEL_LEAF)
  >- LABEL_LEAF
  >- LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_abi_encode_static,
  label_preserving_abi_encode_static_info, label_preserving_abi_alloc_buffer];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;

Theorem label_preserving_abi_encode_dyn_static_loop:
  !s r t. compile_abi_encode_dyn_static_loop dst src info asz msz len s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >> ntac 3 LABEL_FRESH >>
  LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >>
  LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >>
  LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >>
  LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >> LABEL_BIND >>
  LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_abi_encode_mutual:
  (!dst cp ci dyn off dp s r t.
    compile_abi_encode_child dst cp ci dyn off dp s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!dst src info s r t.
    compile_abi_encode_to_buf dst src info s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!dst src elems so ho dp s r t.
    compile_abi_encode_complex_elems dst src elems so ho dp s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!dst src info asz msz len s r t.
    compile_abi_encode_dyn_loop dst src info asz msz len s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  conj_tac >- suspend "child" >>
  conj_tac >- (ntac 2 gen_tac >> rewrite_tac[Once compile_abi_encode_child_def] >> LABEL_LEAF) >>
  conj_tac >- (ntac 3 gen_tac >> rewrite_tac[Once compile_abi_encode_child_def,
    comp_ignore_bind_def] >> ntac 9 LABEL_BIND >> LABEL_LEAF) >>
  conj_tac >- (ntac 3 gen_tac >> rewrite_tac[Once compile_abi_encode_child_def,
    comp_ignore_bind_def] >> LABEL_BIND >> LABEL_LEAF) >>
  conj_tac >- suspend "array" >>
  conj_tac >- (rpt gen_tac >> rewrite_tac[Once compile_abi_encode_child_def] >> LABEL_LEAF) >>
  conj_tac >- suspend "complex" >>
  conj_tac >- (rpt gen_tac >> rewrite_tac[Once compile_abi_encode_child_def] >> LABEL_LEAF) >>
  conj_tac >- suspend "elems" >> suspend "loop"
QED

Resume label_preserving_abi_encode_mutual[child]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  LABEL_BIND >> IF_CASES_TAC >- LABEL_LEAF >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_abi_encode_mutual[array]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >> ntac 3 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> rpt strip_tac >>
      metis_tac[label_preserving_abi_encode_dyn_static_loop]) >>
  gen_tac >> ntac 3 LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_abi_encode_mutual[complex]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> IF_CASES_TAC
  >- (LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      rewrite_tac[comp_ignore_bind_def] >> ntac 2 LABEL_BIND >> LABEL_LEAF) >>
  rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_abi_encode_mutual[elems]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Resume label_preserving_abi_encode_mutual[loop]:
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_abi_encode_child_def] >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >>
  simp_tac pure_ss [LET_THM] >> ntac 3 LABEL_BIND >> ntac 3 LABEL_FRESH >>
  ntac 10 LABEL_BIND >> ntac 10 LABEL_BIND >> ntac 6 LABEL_BIND >> LABEL_LEAF
QED
Finalise label_preserving_abi_encode_mutual

val label_simps = label_simps @ [label_preserving_abi_encode_mutual,
  label_preserving_default_return_path, label_preserving_extcall_store_values];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;

Theorem label_preserving_external_call_kwargs:
  !s r t. compile_external_call_kwargs cenv addr vals tys memsz abisz mid
    retsz minsz retmem static value gas skip def dop rt dt enc_info dec_info s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_external_call_kwargs_def] >> simp_tac pure_ss [LET_THM] >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- LABEL_LEAF >>
      LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      ntac 3 LABEL_BIND >> LABEL_LEAF) >> gen_tac >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >> ntac 2 LABEL_FRESH >>
  ntac 3 LABEL_BIND >> LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (LABEL_BIND >> LABEL_LEAF) >> gen_tac >>
  LABEL_BIND >> IF_CASES_TAC >- LABEL_LEAF >>
  IF_CASES_TAC
  >- (LABEL_BIND >> simp_tac pure_ss [LET_THM] >> LABEL_LEAF) >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt gen_tac >> Cases_on `r` >> metis_tac[label_preserving_abi_decode]) >>
  gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_dynarray_pop:
  !s r t. compile_dynarray_pop base_op scale sz load_opc store_opc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> ntac 8 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_dynarray_append:
  !s r t. compile_dynarray_append cenv base_op v scale sz dt st cap prim load_opc store_opc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_dynarray_append_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> ntac 6 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- LABEL_LEAF >> IF_CASES_TAC
      >- (ho_match_mp_tac label_preserving_bind >> conj_tac
          >- metis_tac[label_preserving_store_memory] >> gen_tac >> LABEL_LEAF) >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_word_copy_loop] >> gen_tac >> LABEL_LEAF) >>
  gen_tac >> LABEL_BIND >> LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_unwrap_value];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;

Theorem label_preserving_stage_intcall_args:
  !vals flags tys s r t.
    compile_stage_intcall_args cenv vals flags tys s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  qid_spec_tac `cenv` >>
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- (rpt gen_tac >> rewrite_tac[compile_stage_intcall_args_def] >> LABEL_LEAF)
  >- (rpt gen_tac >> strip_tac >>
      rewrite_tac[compile_stage_intcall_args_def] >> ntac 2 LABEL_BIND >> LABEL_LEAF)
  >- (rpt gen_tac >> strip_tac >>
      rewrite_tac[compile_stage_intcall_args_def] >> simp_tac pure_ss [LET_THM] >>
      ntac 2 LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
      rewrite_tac[comp_ignore_bind_def] >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- (IF_CASES_TAC >- LABEL_LEAF >> IF_CASES_TAC
          >- (LABEL_BIND >> LABEL_LEAF) >> LABEL_LEAF) >>
      gen_tac >> LABEL_BIND >> LABEL_LEAF) >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_stage_intcall_args_def] >> ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_store_multi_results:
  !ops buf off s r t. store_multi_results buf ops off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct_on `ops` >> rewrite_tac[store_multi_results_def, comp_ignore_bind_def]
  >- LABEL_LEAF >> ntac 3 gen_tac >> ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_array_subscript:
  (!ptr s r t. loader ptr s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_array_subscript arr idx dyn n scale sz signed loader s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_array_subscript_def, comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> LABEL_LEAF) >> gen_tac >> ntac 5 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >> LABEL_LEAF) >>
  gen_tac >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_store_byte_chunks:
  !ptr bs off s r t. compile_store_byte_chunks ptr bs off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> conj_tac
  >- (rpt gen_tac >> rewrite_tac[compile_store_byte_chunks_def] >> LABEL_LEAF) >>
  rpt gen_tac >> strip_tac >> rewrite_tac[Once compile_store_byte_chunks_def] >>
  simp_tac pure_ss [LET_THM] >> rewrite_tac[comp_ignore_bind_def] >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_bytelike_literal:
  !s r t. compile_bytelike_literal bs n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_bytelike_literal_def] >> simp_tac pure_ss [LET_THM] >>
  LABEL_BIND >> simp_tac pure_ss [LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_store_byte_chunks] >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_env_var:
  !s r t. compile_env_var ev s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `ev` >> rewrite_tac[compile_env_var_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_name_vv:
  !s r t. compile_name_vv cenv ty id s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_name_vv_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >-
    (simp_tac (srw_ss()) [] >> rewrite_tac[comp_ignore_bind_def] >>
     LABEL_BIND >> LABEL_LEAF) >>
  Cases_on `x` >> rewrite_tac[comp_ignore_bind_def] >>
  CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
    (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_literal_vv:
  !s r t. compile_literal_vv ty lit s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `lit` >> rewrite_tac[compile_literal_vv_def]
  >- (Cases_on `b` >> rewrite_tac[compile_literal_vv_def] >> LABEL_LEAF)
  >- (ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_bytelike_literal] >> gen_tac >> LABEL_LEAF)
  >- (Cases_on `ty`
      >- (Cases_on `b` >>
          CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
            (RATOR_CONV (SIMP_CONV (srw_ss()) [])))))
          >- LABEL_LEAF >- LABEL_LEAF >- LABEL_LEAF
          >- LABEL_LEAF >- LABEL_LEAF
          >- (Cases_on `b'` >>
              CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
                (RATOR_CONV (SIMP_CONV (srw_ss()) [])))))
              >- LABEL_LEAF >>
              ho_match_mp_tac label_preserving_bind >> conj_tac
              >- metis_tac[label_preserving_bytelike_literal] >> gen_tac >> LABEL_LEAF) >>
          LABEL_LEAF) >>
      CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
        (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >> LABEL_LEAF)
  >- LABEL_LEAF >> LABEL_LEAF
QED

Theorem label_preserving_load_bytestring_as_word:
  !s r t. load_bytestring_as_word v opc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[load_bytestring_as_word_def] >> ntac 6 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_int_clamp:
  !s r t. compile_int_clamp signed bits v s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_int_clamp_def] >> IF_CASES_TAC >>
  simp_tac pure_ss [LET_THM] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

val label_simps = label_simps @ [label_preserving_int_clamp,
  label_preserving_load_bytestring_as_word];
val LABEL_LEAF = rpt strip_tac >> metis_tac label_simps;
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- LABEL_LEAF >> gen_tac;

val CONVERT_LEAF = rpt strip_tac >> metis_tac[label_preserving_return,
  label_preserving_emit_op, label_preserving_emit_void,
  label_preserving_int_clamp, label_preserving_load_bytestring_as_word];
val CONVERT_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- CONVERT_LEAF >> gen_tac;

Theorem label_preserving_type_convert:
  !s r t. compile_type_convert v cop s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `cop` >> rewrite_tac[compile_type_convert_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> rpt IF_CASES_TAC >>
  simp_tac pure_ss [LET_THM] >>
  rpt CONVERT_BIND >> rpt IF_CASES_TAC >>
  simp_tac pure_ss [LET_THM] >> rpt CONVERT_BIND >>
  all_tac >>~- ([`!s r t. emit_op opc ops s = (r,t) ==> cs_extends s t /\ EVERY jump_label_ok (added_labels s t)`], CONVERT_LEAF) >>
  all_tac >>~- ([`!s r t. comp_return x s = (r,t) ==> cs_extends s t /\ EVERY jump_label_ok (added_labels s t)`], CONVERT_LEAF) >>
  all_tac >>~- ([`!s r t. compile_int_clamp sg n x s = (r,t) ==> cs_extends s t /\ EVERY jump_label_ok (added_labels s t)`], CONVERT_LEAF) >>
  rpt (BETA_TAC >> pure_rewrite_tac[comp_bind_assoc] >> CONVERT_BIND) >>
  BETA_TAC >>
  all_tac >>~- ([`!s r t. emit_op opc ops s = (r,t) ==> cs_extends s t /\ EVERY jump_label_ok (added_labels s t)`], CONVERT_LEAF) >>
  PairCases_on `r` >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  rpt IF_CASES_TAC >> rpt CONVERT_BIND >> CONVERT_LEAF
QED

Theorem label_preserving_bytestring_widen_copy:
  !s r t. compile_bytestring_widen_copy ds v sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_neg:
  !s r t. compile_neg v ty s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_neg_def] >> simp_tac pure_ss [LET_THM] >> pairarg_tac >>
  asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  rewrite_tac[comp_ignore_bind_def] >> rpt CONVERT_BIND >> CONVERT_LEAF
QED

Theorem label_preserving_lower_value:
  (!s r t. cfn cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. lower_value cfn cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >>
  rpt strip_tac >> metis_tac[label_preserving_unwrap_value]
QED

Theorem label_preserving_lower_value_with_loc:
  (!s r t. cfn cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. lower_value_with_loc cfn cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[lower_value_with_loc_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- first_assum MATCH_ACCEPT_TAC >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt strip_tac >> metis_tac[label_preserving_unwrap_value]) >>
  gen_tac >> CONVERT_LEAF
QED

val CALLBACK_LEAF = rpt strip_tac >> metis_tac[label_preserving_return,
  label_preserving_emit_op, label_preserving_emit_void,
  label_preserving_unwrap_value, label_preserving_store_memory,
  label_preserving_lower_value];
val CALLBACK_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- CALLBACK_LEAF >> gen_tac;

Theorem label_preserving_concat[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es dp infos off s r t.
    compile_concat cfn cenv es dp infos off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct >> ntac 3 gen_tac
  >- (rewrite_tac[compile_concat_def] >> CALLBACK_LEAF) >>
  Cases_on `infos`
  >- (rewrite_tac[compile_concat_def] >> CALLBACK_LEAF) >>
  PairCases_on `h'` >> rewrite_tac[compile_concat_def, comp_ignore_bind_def] >>
  gen_tac >> IF_CASES_TAC >> rpt CALLBACK_BIND >> CALLBACK_LEAF
QED

Theorem label_preserving_make_tuple[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es buf off s r t.
    compile_make_tuple cfn cenv es buf off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_make_tuple_def] >> CONVERT_LEAF) >>
  ntac 3 gen_tac >>
  rewrite_tac[compile_make_tuple_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> rpt CALLBACK_BIND >> CALLBACK_LEAF
QED

Theorem label_preserving_make_array_elems[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es et sz haslen buf idx s r t.
    compile_make_array_elems cfn cenv es et sz haslen buf idx s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_make_array_elems_def] >> CONVERT_LEAF) >>
  ntac 6 gen_tac >>
  rewrite_tac[compile_make_array_elems_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> rpt CALLBACK_BIND >> CALLBACK_LEAF
QED

Theorem label_preserving_multi_exprs[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es s r t. compile_multi_exprs cfn cenv es s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_multi_exprs_def] >> CONVERT_LEAF) >>
  gen_tac >> rewrite_tac[compile_multi_exprs_def] >>
  simp_tac pure_ss [LET_THM] >> rpt CALLBACK_BIND >> CALLBACK_LEAF
QED

Theorem label_preserving_make_array[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_make_array cfn cenv es et sz hl buf s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_make_array_def, comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> CONVERT_LEAF) >> gen_tac >>
  metis_tac[label_preserving_make_array_elems]
QED

Theorem label_preserving_struct_lit[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !fields buf off s r t.
    compile_struct_lit cfn cenv ty fields buf off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_struct_lit_def] >> CONVERT_LEAF) >>
  ntac 3 gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_struct_lit_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> rpt CALLBACK_BIND >> CALLBACK_LEAF
QED

Theorem label_preserving_store_abi_tuple[local]:
  !vals buf off s r t.
    compile_store_abi_tuple cenv buf off vals s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct
  >- (rewrite_tac[compile_store_abi_tuple_def] >> CONVERT_LEAF) >>
  ntac 3 gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  LABEL_BIND >> IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_materialize_vv[local]:
  !s r t. compile_materialize_vv cenv ty vv s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_extcall_store_args[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !es tys buf off s r t.
    compile_extcall_store_args cfn cenv es tys buf off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_extcall_store_args_def] >> CONVERT_LEAF) >>
  ntac 4 gen_tac >> Cases_on `tys` >>
  rewrite_tac[compile_extcall_store_args_def, comp_ignore_bind_def] >>
  simp_tac pure_ss [LET_THM] >> CALLBACK_BIND >> rpt IF_CASES_TAC >>
  rpt CONVERT_BIND >> rpt IF_CASES_TAC >> rpt CONVERT_BIND >>
  all_tac >>~- ([`compile_store_bytestring v dst`],
    ho_match_mp_tac label_preserving_bind >> conj_tac
    >- metis_tac[label_preserving_store_bytestring] >> gen_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem label_preserving_ext_call_kwarg[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_ext_call_kwarg cfn cenv rt k e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- CALLBACK_LEAF
  >- (gen_tac >> ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[label_preserving_materialize_vv] >> gen_tac >> CONVERT_LEAF)
  >- CALLBACK_LEAF >> gen_tac >> CONVERT_LEAF
QED

Theorem label_preserving_ext_call_kwargs[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !ks es s r t. compile_ext_call_kwargs cfn cenv rt ks es s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Induct
  >- (rewrite_tac[compile_ext_call_kwargs_def] >> CONVERT_LEAF) >>
  ntac 2 gen_tac >> Cases_on `es`
  >- (rewrite_tac[compile_ext_call_kwargs_def] >> CONVERT_LEAF) >>
  rewrite_tac[compile_ext_call_kwargs_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_ext_call_kwarg] >>
  gen_tac >> PairCases_on `r` >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- CALLBACK_LEAF >> gen_tac >> PairCases_on `r` >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> CONVERT_LEAF
QED

Theorem label_preserving_attribute[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_attribute cfn cenv rt ty e fld s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_attribute_def] >> CALLBACK_BIND >>
  simp_tac pure_ss [LET_THM] >> rpt CONVERT_BIND >> CONVERT_LEAF
QED

Theorem label_preserving_subscript[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_subscript cfn cenv rt ty be ie s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_subscript_def] >> CALLBACK_BIND >>
  simp_tac pure_ss [LET_THM] >> Cases_on `place_type cenv be`
  >- (CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
        (RATOR_CONV (SIMP_CONV (srw_ss()) []))))) >>
      CALLBACK_BIND >> IF_CASES_TAC >>
      ntac 2 (ho_match_mp_tac label_preserving_bind >> conj_tac
        >- metis_tac[label_preserving_return, label_preserving_keccak256_key,
                    label_preserving_mapping_subscript] >> gen_tac) >> CONVERT_LEAF) >>
  rename1 `ValPT vt` >> Cases_on `vt` >>
  CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (LAND_CONV
    (RATOR_CONV (SIMP_CONV (srw_ss()) [compile_tuple_subscript_def]))))) >>
  all_tac >>~- ([`lower_value cfn cenv ty ie`],
    CALLBACK_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
    >- (ho_match_mp_tac label_preserving_array_subscript >>
        rpt strip_tac >> metis_tac[label_preserving_ptr_load]) >>
    gen_tac >> CONVERT_LEAF) >>
  CONVERT_BIND >> CONVERT_LEAF
QED
