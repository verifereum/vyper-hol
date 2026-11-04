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

val CALLBACK_LET = ho_match_mp_tac
  (PURE_REWRITE_RULE [comp_bind_def] label_preserving_bind) >> conj_tac
  >- CALLBACK_LEAF >> gen_tac;
val CONVERT_LET = ho_match_mp_tac
  (PURE_REWRITE_RULE [comp_bind_def] label_preserving_bind) >> conj_tac
  >- CONVERT_LEAF >> gen_tac;

Theorem label_preserving_acc[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. compile_acc cfn cenv e acc s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> Cases_on `acc` >> rewrite_tac[compile_acc_def] >>
  all_tac >- CALLBACK_LEAF
  >- (CALLBACK_LET >> CONVERT_LEAF)
  >- (CALLBACK_LET >> CONVERT_LEAF)
  >- (CALLBACK_LET >> CONVERT_LEAF)
  >- (CALLBACK_LET >> CONVERT_LET >> CONVERT_LEAF) >>
  ho_match_mp_tac (PURE_REWRITE_RULE [comp_bind_def] label_preserving_bind) >>
  conj_tac >- metis_tac[label_preserving_emit_inst] >>
  rpt strip_tac >> gvs[] >> metis_tac[label_preserving_return, comp_return_def]
QED

Theorem label_preserving_store_words[local]:
  !vals buf off s r t. compile_store_words buf vals off s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct
  >- (rewrite_tac[compile_store_words_def] >> CONVERT_LEAF) >>
  ntac 3 gen_tac >> rewrite_tac[compile_store_words_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> rpt CONVERT_BIND >> metis_tac[]
QED

Theorem label_preserving_invert[local]:
  !s r t. compile_invert v ty cenv s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `ty` >> rewrite_tac[compile_invert_def] >>
  simp_tac pure_ss [LET_THM] >> CONVERT_LEAF
QED

Theorem label_preserving_as_stack_val[local]:
  (!s r t. f s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s r t. as_stack_val ty (f s) = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `f s` >>
  simp[as_stack_val_def] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem label_preserving_mod_names[local]:
  (!s r t. compile_addmod_names cenv rt aty a bty b mty m s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!s r t. compile_mulmod_names cenv rt aty a bty b mty m s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!s r t. compile_powmod256_names cenv rt aty a bty b s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t))
Proof
  rpt conj_tac >> rewrite_tac[compile_addmod_names_def,
    compile_mulmod_names_def, compile_powmod256_names_def] >>
  ntac 4 (ho_match_mp_tac (PURE_REWRITE_RULE [comp_bind_def]
    label_preserving_bind) >> conj_tac
    >- metis_tac[label_preserving_name_vv, label_preserving_unwrap_value] >> gen_tac) >>
  all_tac >>~- ([`compile_name_vv cenv mty m`],
    ntac 2 (ho_match_mp_tac (PURE_REWRITE_RULE [comp_bind_def]
      label_preserving_bind) >> conj_tac
      >- metis_tac[label_preserving_name_vv, label_preserving_unwrap_value] >> gen_tac) >>
    ho_match_mp_tac label_preserving_as_stack_val >>
    rewrite_tac[builtinMathTheory.compile_addmod_def,
      builtinMathTheory.compile_mulmod_def, comp_ignore_bind_def] >>
    CONVERT_BIND >> CONVERT_LEAF) >>
  ho_match_mp_tac label_preserving_as_stack_val >>
  rewrite_tac[builtinMathTheory.compile_pow_mod256_def] >> CONVERT_LEAF
QED

Theorem label_preserving_get_target_ptr[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !target s r t. compile_get_target_ptr cfn cenv target s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> ho_match_mp_tac
    (SRULE [] (Q.SPEC `\e. T` vyperASTTheory.base_assignment_target_induction)) >>
  rpt conj_tac >> rewrite_tac[compile_get_target_ptr_def] >>
  all_tac >- (gen_tac >> Cases_on `FLOOKUP cenv.ce_vars s` >>
    simp_tac (srw_ss()) [] >> all_tac >- CONVERT_LEAF >>
    Cases_on `x` >> simp_tac (srw_ss()) [] >> CONVERT_LEAF)
  >- (gen_tac >> Cases_on `FLOOKUP cenv.ce_module_vars p` >>
    simp_tac (srw_ss()) [LET_THM] >> all_tac >- CONVERT_LEAF >>
    Cases_on `x` >> simp_tac (srw_ss()) [] >> CONVERT_LEAF) >>
  all_tac >~ [`struct_field_offset`] >-
   (rpt gen_tac >> strip_tac >> gen_tac >>
    (ho_match_mp_tac label_preserving_bind >> conj_tac >- metis_tac[]) >>
    gen_tac >> simp_tac pure_ss [LET_THM] >>
    CONVERT_BIND >> CONVERT_LEAF) >>
  rpt gen_tac >> strip_tac >>
  (ho_match_mp_tac label_preserving_bind >> conj_tac >- metis_tac[]) >>
  gen_tac >> simp_tac pure_ss [LET_THM] >>
  Cases_on `SND (SND result)` >>
  simp_tac (srw_ss()) [] >> all_tac
  >- (CALLBACK_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
      >- (ho_match_mp_tac label_preserving_array_subscript >>
          rpt strip_tac >> metis_tac[label_preserving_ptr_load]) >>
      gen_tac >> CONVERT_LEAF) >>
  Cases_on `x` >> simp_tac (srw_ss()) [] >> all_tac
  >- (CALLBACK_BIND >> IF_CASES_TAC >>
      ntac 2 (ho_match_mp_tac label_preserving_bind >> conj_tac
        >- metis_tac[label_preserving_return, label_preserving_keccak256_key,
                    label_preserving_mapping_subscript] >> gen_tac) >> CONVERT_LEAF) >>
  CALLBACK_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (ho_match_mp_tac label_preserving_array_subscript >>
      rpt strip_tac >> metis_tac[label_preserving_ptr_load]) >>
  gen_tac >> CONVERT_LEAF
QED

Theorem label_preserving_msg_data_to_memory[local]:
  !s r t. builtinSystem$compile_msg_data_to_memory s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinSystemTheory.compile_msg_data_to_memory_def,
    contextTheory.compile_alloc_dynamic_def, comp_ignore_bind_def] >> ntac 3 CONVERT_BIND >> CONVERT_LEAF
QED

Theorem label_preserving_raw_call_outbuf[local]:
  !s r t. builtinSystem$compile_raw_call_outbuf n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinSystemTheory.compile_raw_call_outbuf_def] >>
  IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
  LABEL_BIND >> rpt CONVERT_BIND >> CONVERT_LEAF
QED

Theorem label_preserving_raw_call_finish[local]:
  !s r t. builtinSystem$compile_raw_call_finish addr dp len gas value ct n rof ov op s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinSystemTheory.compile_raw_call_finish_def,
    comp_ignore_bind_def] >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (Cases_on `ct` >> simp_tac (srw_ss()) [] >> CONVERT_LEAF) >> gen_tac >>
  IF_CASES_TAC
  >- (ntac 2 LABEL_FRESH >> ntac 7 LABEL_BIND >>
      IF_CASES_TAC >- (ntac 2 CONVERT_BIND >>
        ho_match_mp_tac label_preserving_bind >> conj_tac
        >- metis_tac[label_preserving_select] >> gen_tac >>
        CONVERT_BIND >> CONVERT_LEAF) >> CONVERT_LEAF) >>
  IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
  all_tac >- (ntac 2 CONVERT_BIND >>
    ho_match_mp_tac label_preserving_bind >> conj_tac
    >- metis_tac[label_preserving_select] >> gen_tac >> CONVERT_BIND >>
    LABEL_BIND >> ntac 3 CONVERT_BIND >> CONVERT_LEAF) >> CONVERT_LEAF
QED

Theorem label_preserving_fresh_vars[local]:
  !n s r t. fresh_vars n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[fresh_vars_def] >> all_tac >- CONVERT_LEAF >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_fresh_var] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[] >> gen_tac >> CONVERT_LEAF
QED

Theorem label_preserving_emit_multi_op[local]:
  !s r t. emit_multi_op opc ops n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[emit_multi_op_def, comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_fresh_vars] >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_emit_inst] >> gen_tac >> CONVERT_LEAF
QED

Theorem label_preserving_internal_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty fid args default_ret s r t.
    compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac pure_ss [compile_call_def, LET_THM] >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule_all label_preserving_multi_vvs >> strip_tac >>
  qpat_x_assum `!c ty e s r t. _` kall_tac >>
  Cases_on `returns_count > 0` >> asm_rewrite_tac[]
  >- suspend "stack_results" >>
  Cases_on `return_buf_size > 0` >> asm_rewrite_tac[]
  >- suspend "buffer_result" >> suspend "no_result"
QED

Resume label_preserving_internal_call[stack_results]:
  Cases_on `compile_alloc_buffer (32 * returns_count) st1` >> gvs[] >>
  drule label_preserving_abi_alloc_buffer >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_stage_intcall_args >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_emit_multi_op >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_store_multi_results >> strip_tac >>
  simp_tac bool_ss [pairTheory.PAIR_EQ] >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED

Resume label_preserving_internal_call[buffer_result]:
  Cases_on `compile_alloc_buffer return_buf_size st1` >> gvs[] >>
  drule label_preserving_abi_alloc_buffer >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_stage_intcall_args >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_emit_void >> strip_tac >>
  simp_tac bool_ss [pairTheory.PAIR_EQ] >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED

Resume label_preserving_internal_call[no_result]:
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_stage_intcall_args >> strip_tac >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule label_preserving_emit_void >> strip_tac >>
  simp_tac bool_ss [pairTheory.PAIR_EQ] >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED

Finalise label_preserving_internal_call

(* Invert one direct compiler LET before using its boundary theorem. *)
fun CALL_PAIR th =
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  drule_all (Q.INST [`LP` |-> `jump_label_ok`] th) >> strip_tac;

Theorem label_preserving_send_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty hg args default_ret s r t.
    compile_call cfn cenv ret_ty ty (Send hg) args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `args` >> simp_tac pure_ss [compile_call_def, LET_THM]
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  Cases_on `t'` >> simp_tac (srw_ss()) []
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  Cases_on `LENGTH t'' = (if hg then 1 else 0)` >> asm_rewrite_tac[]
  >- suspend "send_success" >>
  CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]
QED

Resume label_preserving_send_call[send_success]:
  simp_tac (srw_ss()) [] >>
  `!c ty e s r t. lower_value cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)` by
    (rpt gen_tac >> disch_tac >> drule_at Any label_preserving_lower_value >>
     (impl_tac >- metis_tac[]) >> simp[]) >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  Cases_on `t''` >> simp_tac (srw_ss()) []
  >- suspend "send_zero_gas" >>
  Cases_on `t'` >> simp_tac (srw_ss()) []
  >- suspend "send_explicit_gas" >>
  suspend "send_bad_gas"
QED

Resume label_preserving_send_call[send_zero_gas]:
  CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_emit_void >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED
Resume label_preserving_send_call[send_explicit_gas]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_emit_void >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED
Resume label_preserving_send_call[send_bad_gas]:
  Cases_on `hg` >> gvs[]
QED
Finalise label_preserving_send_call

fun CALL_VALUE g =
  (pairarg_tac >> asm_rewrite_tac[] >>
   CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
   drule_at Any label_preserving_lower_value >>
   (impl_tac >- metis_tac[]) >> strip_tac) g;

Theorem label_preserving_external_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty ist skip name ats rt opts args default_ret s r t.
    compile_call cfn cenv ret_ty ty (ExtCall ist skip (name,ats,rt) opts)
      args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  CALL_VALUE >> CALL_PAIR label_preserving_multi_vvs >>
  CALL_PAIR label_preserving_ext_call_kwargs >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  Cases_on `gas_opt` >> simp_tac (srw_ss()) []
  >- suspend "default_gas" >> suspend "explicit_gas"
QED

Resume label_preserving_external_call[default_gas]:
  CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_external_call_kwargs >>
  rpt IF_CASES_TAC >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED
Resume label_preserving_external_call[explicit_gas]:
  CALL_PAIR label_preserving_external_call_kwargs >>
  rpt IF_CASES_TAC >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED
Finalise label_preserving_external_call

Theorem label_preserving_raw_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty flags args default_ret s r t.
    compile_call cfn cenv ret_ty ty (RawCallTarget flags) args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  Cases_on `t'` >> simp_tac (srw_ss()) []
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  CALL_VALUE >> CALL_VALUE >> CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_emit_op >> CALL_PAIR label_preserving_ext_call_kwargs >>
  Cases_on `gas_opt` >> simp_tac (srw_ss()) []
  >- suspend "default_gas" >> suspend "explicit_gas"
QED
Resume label_preserving_raw_call[default_gas]:
  CALL_PAIR label_preserving_emit_op >> CALL_PAIR label_preserving_raw_call_outbuf >>
  CALL_PAIR label_preserving_raw_call_finish >>
  IF_CASES_TAC >> strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED
Resume label_preserving_raw_call[explicit_gas]:
  CALL_PAIR label_preserving_raw_call_outbuf >> CALL_PAIR label_preserving_raw_call_finish >>
  IF_CASES_TAC >> strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED
Finalise label_preserving_raw_call

Theorem label_preserving_raw_calldata_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty flags args default_ret s r t.
    compile_call cfn cenv ret_ty ty (RawCallCalldataTarget flags) args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `args` >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  CALL_VALUE >> CALL_PAIR label_preserving_ext_call_kwargs >>
  Cases_on `gas_opt` >> simp_tac (srw_ss()) []
  >- suspend "default_gas" >> suspend "explicit_gas"
QED
Resume label_preserving_raw_calldata_call[default_gas]:
  CALL_PAIR label_preserving_emit_op >> CALL_PAIR label_preserving_raw_call_outbuf >>
  CALL_PAIR label_preserving_msg_data_to_memory >> CALL_PAIR label_preserving_raw_call_finish >>
  IF_CASES_TAC >> strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED
Resume label_preserving_raw_calldata_call[explicit_gas]:
  CALL_PAIR label_preserving_raw_call_outbuf >> CALL_PAIR label_preserving_msg_data_to_memory >>
  CALL_PAIR label_preserving_raw_call_finish >>
  IF_CASES_TAC >> strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED
Finalise label_preserving_raw_calldata_call

Theorem label_preserving_call[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty target args default_ret s r t.
    compile_call cfn cenv ret_ty ty target args default_ret s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `target`
  >~ [`IntCall fid`] >- metis_tac[label_preserving_internal_call]
  >~ [`ExtCall ist skip signature opts`]
  >- (PairCases_on `signature` >> metis_tac[label_preserving_external_call])
  >~ [`Send hg`] >- metis_tac[label_preserving_send_call]
  >~ [`RawCallTarget flags`] >- metis_tac[label_preserving_raw_call]
  >~ [`RawCallCalldataTarget flags`] >- metis_tac[label_preserving_raw_calldata_call] >>
  simp_tac pure_ss [compile_call_def, LET_THM] >>
  CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]
QED

Theorem label_preserving_lower_abi_encode[local]:
  !s r t. lower_abi_encode ensure mid src info maxlen s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `mid` >> rewrite_tac[builtinAbiTheory.lower_abi_encode_def,
    comp_ignore_bind_def] >> simp_tac (srw_ss()) [LET_THM] >>
  ntac 3 LABEL_BIND
  >- (LABEL_BIND >>
      ho_match_mp_tac label_preserving_bind >> conj_tac
      >- metis_tac[cj 2 label_preserving_abi_encode_mutual] >>
      gen_tac >> LABEL_BIND >> LABEL_LEAF) >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (LABEL_BIND >> LABEL_LEAF) >> gen_tac >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[cj 2 label_preserving_abi_encode_mutual] >>
  gen_tac >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (LABEL_BIND >> LABEL_LEAF) >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_lower_abi_decode[local]:
  !s r t. lower_abi_decode src info amin amax outsz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinAbiTheory.lower_abi_decode_def, comp_ignore_bind_def] >>
  ntac 2 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF) >>
  gen_tac >> ntac 3 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt gen_tac >> Cases_on `r` >> metis_tac[label_preserving_abi_decode]) >>
  gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_zero_words[local]:
  !n s r t. compile_zero_words baseop n s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Induct >> rewrite_tac[builtinSimpleTheory.compile_zero_words_def,
    comp_ignore_bind_def]
  >- metis_tac[label_preserving_return] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[] >> gen_tac >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_empty_complex[local]:
  !s r t. compile_builtin_empty_complex sz bytes s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinSimpleTheory.compile_builtin_empty_complex_def,
    comp_ignore_bind_def] >> ntac 2 LABEL_BIND >>
  IF_CASES_TAC
  >- (LABEL_BIND >> LABEL_LEAF) >>
  simp_tac pure_ss [LET_THM] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_zero_words] >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_slice_bounds[local]:
  !s r t. compile_assert_slice_bounds start len src_len s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_assert_slice_bounds_def] >>
  ntac 5 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_bytestring_src[local]:
  !s r t. compile_bytestring_src srcop s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_bytestring_src_def] >>
  ntac 2 LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_extract32_load[local]:
  !s r t. compile_extract32_load len srcop start s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_extract32_load_def,
    comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_slice_bounds] >>
  gen_tac >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_clamp_basetype[local]:
  !s r t. compile_clamp_basetype v ty s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  Cases_on `ty` >> simp_tac (srw_ss()) [compile_clamp_basetype_def]
  >- (Cases_on `b` >> simp_tac (srw_ss()) [compile_clamp_basetype_def]
      >~ [`compile_clamp_basetype v (BaseT (BytesT bnd))`]
      >- (Cases_on `bnd` >>
          simp_tac (srw_ss()) [compile_clamp_basetype_def, comp_ignore_bind_def] >>
          rpt IF_CASES_TAC >> rpt LABEL_BIND >> LABEL_LEAF) >>
      rewrite_tac[comp_ignore_bind_def] >> rpt IF_CASES_TAC >>
      rpt LABEL_BIND >>
      metis_tac[label_preserving_return, label_preserving_clamp_and_return]) >>
  metis_tac[label_preserving_return]
QED

Theorem label_preserving_type_builtin_body[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv vv_ty ty tb ret_ty args s r t.
    compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `tb` >>
  simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM]
  >- suspend "empty"
  >- (Cases_on `type_bounds ret_ty` >> simp_tac (srw_ss()) [] >>
      strip_tac >> gvs[] >> simp[cs_extends_refl, added_labels_def, GSYM MAP_DROP])
  >- (Cases_on `type_bounds ret_ty` >> simp_tac (srw_ss()) [] >>
      strip_tac >> gvs[] >> simp[cs_extends_refl, added_labels_def, GSYM MAP_DROP])
  >- (strip_tac >> gvs[] >> simp[cs_extends_refl, added_labels_def, GSYM MAP_DROP])
  >- suspend "convert"
  >- suspend "extract32"
  >- suspend "decode" >> suspend "encode"
QED

Resume label_preserving_type_builtin_body[empty]:
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> simp[cs_extends_refl, added_labels_def, GSYM MAP_DROP]) >>
  simp_tac pure_ss [LET_THM] >> CALL_PAIR label_preserving_empty_complex >>
  strip_tac >> gvs[]
QED

Resume label_preserving_type_builtin_body[decode]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_unwrap_value >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vv_ty LocMemory action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_ptr_val_def] >>
  qpat_x_assum `(_,_) = lower_abi_decode _ _ _ _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_lower_abi_decode >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_type_builtin_body[extract32]:
  CALL_VALUE >> CALL_PAIR label_preserving_bytestring_src >>
  CALL_VALUE >> CALL_PAIR label_preserving_extract32_load >>
  qmatch_goalsub_abbrev_tac `as_stack_val vv_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_clamp_basetype _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_clamp_basetype >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_type_builtin_body[convert]:
  CALL_VALUE >> IF_CASES_TAC
  >- (strip_tac >> gvs[]) >> IF_CASES_TAC
  >- suspend "convert_widen" >>
  Cases_on `ret_ty` >> simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `as_stack_val vv_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_type_convert _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_type_convert >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_type_builtin_body[convert_widen]:
  qmatch_goalsub_abbrev_tac `as_stack_val vv_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_bytestring_widen_copy _ _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_bytestring_widen_copy >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

val ENCODE_FINISH =
  qmatch_goalsub_abbrev_tac `as_ptr_val vv_ty LocMemory action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_ptr_val_def] >>
  qpat_x_assum `(_,_) = lower_abi_encode _ _ _ _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_lower_abi_encode >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans];

Resume label_preserving_type_builtin_body[encode]:
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- suspend "encode_word" >> suspend "encode_complex") >>
  CALL_PAIR label_preserving_multi_exprs >>
  CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_store_abi_tuple >>
  ENCODE_FINISH
QED

Resume label_preserving_type_builtin_body[encode_word]:
  CALL_VALUE >> CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_emit_void >> ENCODE_FINISH
QED

Resume label_preserving_type_builtin_body[encode_complex]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_unwrap_value >> ENCODE_FINISH
QED


Finalise label_preserving_type_builtin_body

Theorem label_preserving_builtin_bop[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty bop args s r t.
    compile_builtin_dispatch_body cfn cenv ret_ty ty (Bop bop) args s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC
  >- suspend "membership" >> IF_CASES_TAC
  >- suspend "bytes_compare" >>
  CALL_VALUE >> CALL_VALUE >>
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_binop _ _ _ _ _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_binop >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_builtin_bop[bytes_compare]:
  CALL_VALUE >> CALL_VALUE >>
  CALL_PAIR label_preserving_bytestring_hash >>
  CALL_PAIR label_preserving_bytestring_hash >> IF_CASES_TAC
  >- suspend "eq" >> CALL_PAIR label_preserving_emit_op >>
  suspend "neq"
QED

Resume label_preserving_builtin_bop[eq]:
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = emit_op _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_emit_op >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_builtin_bop[neq]:
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = emit_op _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_emit_op >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_builtin_bop[membership]:
  CALL_VALUE >> Cases_on `HD (TL args)` >>
  simp_tac (srw_ss()) []
  >~ [`Builtin bt bi es`] >- (Cases_on `bi` >>
      simp_tac (srw_ss()) []
      >~ [`compile_multi_exprs`] >- suspend "membership_list" >>
      pairarg_tac >> asm_rewrite_tac[] >>
      CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
      first_assum (drule_then strip_assume_tac) >>
      qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
      Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
      qpat_x_assum `(_,_) = compile_var_array_membership _ _ _ _ _ _`
        (assume_tac o SYM) >>
      drule_all label_preserving_var_array_membership >> strip_tac >>
      strip_tac >> gvs[] >> metis_tac[label_extends_trans]) >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_var_array_membership _ _ _ _ _ _`
    (assume_tac o SYM) >>
  drule_all label_preserving_var_array_membership >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_builtin_bop[membership_list]:
  CALL_PAIR label_preserving_multi_exprs >> IF_CASES_TAC >>
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def]
  >- (qpat_x_assum `(_,_) = compile_list_membership_in _ _ _`
        (assume_tac o SYM) >>
      drule (Q.INST [`LP` |-> `jump_label_ok`]
        (CONJUNCT1 label_preserving_list_membership)) >> strip_tac >>
      strip_tac >> gvs[] >> metis_tac[label_extends_trans]) >>
  qpat_x_assum `(_,_) = compile_list_membership_notin _ _ _`
    (assume_tac o SYM) >>
  drule (Q.INST [`LP` |-> `jump_label_ok`]
    (CONJUNCT2 label_preserving_list_membership)) >> strip_tac >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Finalise label_preserving_builtin_bop

Theorem label_preserving_builtin_abs[local]:
  !s r t. compile_builtin_abs v s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinSimpleTheory.compile_builtin_abs_def,
    comp_ignore_bind_def] >> ntac 6 LABEL_BIND >>
  metis_tac[label_preserving_select]
QED

Theorem label_preserving_addmod[local]:
  !s r t. compile_addmod a b c s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMathTheory.compile_addmod_def] >>
  LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_mulmod[local]:
  !s r t. compile_mulmod a b c s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMathTheory.compile_mulmod_def] >>
  LABEL_IGNORE >> LABEL_LEAF
QED

Theorem label_preserving_pow_mod256[local]:
  !s r t. compile_pow_mod256 a b s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMathTheory.compile_pow_mod256_def] >> LABEL_LEAF
QED

Theorem label_preserving_builtin_calldatasize[local]:
  !s r t. compile_builtin_calldatasize s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinSimpleTheory.compile_builtin_calldatasize_def] >> LABEL_LEAF
QED

Theorem label_preserving_blockhash[local]:
  !s r t. compile_blockhash v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_blockhash_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_blobhash[local]:
  !s r t. compile_blobhash v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_blobhash_def] >> LABEL_LEAF
QED

Theorem label_preserving_floor[local]:
  !s r t. compile_floor v divisor s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_floor_def] >> ntac 2 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_select] >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_ceil[local]:
  !s r t. compile_ceil v divisor s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_ceil_def] >> ntac 2 LABEL_BIND >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_select] >> gen_tac >> LABEL_LEAF
QED

Theorem label_preserving_as_wei_value_int[local]:
  !s r t. compile_as_wei_value_int v scale signed s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_int_def,
    comp_ignore_bind_def] >> IF_CASES_TAC >- LABEL_LEAF >>
  ntac 5 LABEL_BIND >> ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (IF_CASES_TAC >- (rpt LABEL_BIND >> LABEL_LEAF) >> LABEL_LEAF) >>
  gen_tac >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_as_wei_value_decimal[local]:
  !s r t. compile_as_wei_value_decimal v scale divisor s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_decimal_def,
    comp_ignore_bind_def] >> ntac 3 LABEL_BIND >> IF_CASES_TAC
  >- LABEL_LEAF >> LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_keccak256_word[local]:
  !s r t. compile_keccak256_word v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_keccak256_word_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_keccak256_bytes[local]:
  !s r t. compile_keccak256_bytes v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytes_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_keccak256_bytesm[local]:
  !s r t. compile_keccak256_bytesm v m s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytesm_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_sha256_word[local]:
  !s r t. compile_sha256_word v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_sha256_word_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_sha256_bytes[local]:
  !s r t. compile_sha256_bytes v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_sha256_bytes_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_sha256_bytesm[local]:
  !s r t. compile_sha256_bytesm v m s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_sha256_bytesm_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_ecrecover[local]:
  !s r t. compile_ecrecover h v rr ss s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_ecrecover_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_ecadd_points[local]:
  !s r t. compile_ecadd_points p1 p2 s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_ecadd_points_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_ecmul_point[local]:
  !s r t. compile_ecmul_point p v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinMiscTheory.compile_ecmul_point_def,
    comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_method_id_hash[local]:
  !s r t. compile_method_id_hash ty v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases_on `ty` >> simp_tac (srw_ss())
    [builtinHashingTheory.compile_method_id_hash_def]
  >- (Cases_on `b` >> simp_tac (srw_ss())
        [builtinHashingTheory.compile_method_id_hash_def]
      >~ [`BytesT bound`] >- (Cases_on `bound` >> simp_tac (srw_ss())
          [builtinHashingTheory.compile_method_id_hash_def] >>
          metis_tac[label_preserving_keccak256_bytes,
            label_preserving_keccak256_bytesm]) >>
      metis_tac[label_preserving_keccak256_bytes]) >>
  metis_tac[label_preserving_keccak256_bytes]
QED

Theorem label_preserving_method_id_runtime[local]:
  !s r t. compile_method_id_runtime ty v isbytes s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinHashingTheory.compile_method_id_runtime_def,
    comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_method_id_hash] >> gen_tac >>
  ntac 2 LABEL_BIND >> IF_CASES_TAC >- LABEL_LEAF >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_slice_out_buf[local]:
  !s r t. compile_slice_out_buf sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_out_buf_def] >>
  rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_slice_data[local]:
  !s r t. compile_slice_data len data_op off n sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_data_def] >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_slice_bounds] >>
  rewrite_tac[comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_slice_calldata[local]:
  !s r t. compile_slice_calldata off n sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_calldata_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_slice_out_buf] >>
  Cases >> simp_tac (srw_ss()) [] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_slice_bounds] >>
  rewrite_tac[comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_slice_code[local]:
  !s r t. compile_slice_code off n sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_code_def] >>
  ho_match_mp_tac label_preserving_bind >> conj_tac
  >- metis_tac[label_preserving_slice_out_buf] >>
  Cases >> simp_tac (srw_ss()) [] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_slice_bounds] >>
  rewrite_tac[comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_slice_extcode[local]:
  !s r t. compile_slice_extcode addr off n buf data_op s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinBytesTheory.compile_slice_extcode_def] >> LABEL_BIND >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- metis_tac[label_preserving_slice_bounds] >>
  rewrite_tac[comp_ignore_bind_def] >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_uint2str[local]:
  !s r t. compile_uint2str v n sz s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  rewrite_tac[builtinStringsTheory.compile_uint2str_def,
    comp_ignore_bind_def] >> ntac 8 LABEL_BIND >>
  ntac 6 LABEL_FRESH >> rpt LABEL_BIND >> LABEL_LEAF
QED

Theorem label_preserving_builtin_len[local]:
  !s r t. compile_builtin_len ctor imm v loc s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[builtinSimpleTheory.compile_builtin_len_def] >>
  metis_tac[label_preserving_ptr_load]
QED

fun STACK_FINISH th =
  qmatch_goalsub_abbrev_tac `as_stack_val result_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  first_x_assum (fn eth => mp_then Any strip_assume_tac
    (Q.INST [`LP` |-> `jump_label_ok`] th) (SYM eth)) >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans];

Theorem label_preserving_builtin_body[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ret_ty ty bi args s r t.
    compile_builtin_dispatch_body cfn cenv ret_ty ty bi args s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `bi`
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop _) _ _`] >-
      metis_tac[label_preserving_builtin_bop] >>
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM]
  >~ [`compile_invert`] >- suspend "not"
  >~ [`compile_neg`] >- (CALL_VALUE >> STACK_FINISH label_preserving_neg)
  >~ [`compile_builtin_abs`] >- (CALL_VALUE >> STACK_FINISH label_preserving_builtin_abs)
  >~ [`compile_env_var`] >- suspend "env"
  >~ [`compile_acc`] >- suspend "acc"
  >~ [`compile_keccak256_bytes`] >- suspend "keccak"
  >~ [`compile_sha256_bytes`] >- suspend "sha"
  >~ [`compile_builtin_calldatasize`] >- suspend "cdsize"
  >~ [`compile_slice_calldata`] >- suspend "cdslice"
  >~ [`compile_builtin_len`] >- suspend "len"
  >~ [`compile_blockhash`] >- (CALL_VALUE >> STACK_FINISH label_preserving_blockhash)
  >~ [`compile_blobhash`] >- (CALL_VALUE >> STACK_FINISH label_preserving_blobhash)
  >~ [`compile_addmod`] >- (ntac 3 CALL_VALUE >> STACK_FINISH label_preserving_addmod)
  >~ [`compile_mulmod`] >- (ntac 3 CALL_VALUE >> STACK_FINISH label_preserving_mulmod)
  >~ [`compile_ceil`] >- (CALL_VALUE >> STACK_FINISH label_preserving_ceil)
  >~ [`compile_floor`] >- (CALL_VALUE >> STACK_FINISH label_preserving_floor)
  >~ [`compile_pow_mod256`] >- (ntac 2 CALL_VALUE >> STACK_FINISH label_preserving_pow_mod256)
  >~ [`compile_ecrecover`] >- (ntac 4 CALL_VALUE >> STACK_FINISH label_preserving_ecrecover)
  >~ [`compile_ecadd_points`] >- suspend "ecadd"
  >~ [`compile_ecmul_point`] >- suspend "ecmul"
  >~ [`compile_concat`] >- suspend "concat"
  >~ [`compile_slice_code`] >- suspend "slice"
  >~ [`compile_uint2str`] >- suspend "uint2str"
  >~ [`compile_as_wei_value_int`] >- suspend "wei"
  >~ [`compile_method_id_runtime`] >- suspend "method"
  >> suspend "array"
QED

Resume label_preserving_builtin_body[not]:
  CALL_VALUE >> IF_CASES_TAC
  >- STACK_FINISH label_preserving_emit_op >>
  STACK_FINISH label_preserving_invert
QED

Resume label_preserving_builtin_body[env]:
  STACK_FINISH label_preserving_env_var
QED

Resume label_preserving_builtin_body[acc]:
  qmatch_goalsub_abbrev_tac `as_stack_val ret_ty action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_stack_val_def] >>
  qpat_x_assum `(_,_) = compile_acc _ _ _ _ _` (assume_tac o SYM) >>
  drule_all label_preserving_acc >> strip_tac >> strip_tac >> gvs[]
QED

Resume label_preserving_builtin_body[cdsize]:
  STACK_FINISH label_preserving_builtin_calldatasize
QED

fun PTR_FINISH th =
  qmatch_goalsub_abbrev_tac `as_ptr_val ret_ty LocMemory action` >>
  Cases_on `action` >> gvs[markerTheory.Abbrev_def, as_ptr_val_def] >>
  first_x_assum (fn eth => mp_then Any strip_assume_tac
    (Q.INST [`LP` |-> `jump_label_ok`] th) (SYM eth)) >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans];

Resume label_preserving_builtin_body[cdslice]:
  CALL_VALUE >> PTR_FINISH label_preserving_slice_calldata
QED

Resume label_preserving_builtin_body[uint2str]:
  CALL_VALUE >> PTR_FINISH label_preserving_uint2str
QED

Resume label_preserving_builtin_body[wei]:
  CALL_VALUE >> IF_CASES_TAC
  >- STACK_FINISH label_preserving_as_wei_value_decimal >>
  STACK_FINISH label_preserving_as_wei_value_int
QED

Resume label_preserving_builtin_body[len]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  STACK_FINISH label_preserving_builtin_len
QED

Resume label_preserving_builtin_body[ecadd]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_unwrap_value >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_unwrap_value >>
  PTR_FINISH label_preserving_ecadd_points
QED

Resume label_preserving_builtin_body[ecmul]:
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  first_assum (drule_then strip_assume_tac) >>
  CALL_PAIR label_preserving_unwrap_value >> CALL_VALUE >>
  PTR_FINISH label_preserving_ecmul_point
QED

Resume label_preserving_builtin_body[keccak]:
  IF_CASES_TAC
  >- (CALL_VALUE >> STACK_FINISH label_preserving_keccak256_bytes) >>
  Cases_on `expr_type (HD args)` >> simp_tac (srw_ss()) []
  >~ [`BaseT b`] >- (Cases_on `b` >> simp_tac (srw_ss()) []
      >~ [`BytesT bound`] >- (Cases_on `bound` >> simp_tac (srw_ss()) []
          >~ [`compile_keccak256_bytesm`] >-
            (CALL_VALUE >> STACK_FINISH label_preserving_keccak256_bytesm) >>
          CALL_VALUE >> STACK_FINISH label_preserving_keccak256_word) >>
      CALL_VALUE >> STACK_FINISH label_preserving_keccak256_word) >>
  CALL_VALUE >> STACK_FINISH label_preserving_keccak256_word
QED

Resume label_preserving_builtin_body[sha]:
  IF_CASES_TAC
  >- (CALL_VALUE >> STACK_FINISH label_preserving_sha256_bytes) >>
  Cases_on `expr_type (HD args)` >> simp_tac (srw_ss()) []
  >~ [`BaseT b`] >- (Cases_on `b` >> simp_tac (srw_ss()) []
      >~ [`BytesT bound`] >- (Cases_on `bound` >> simp_tac (srw_ss()) []
          >~ [`compile_sha256_bytesm`] >-
            (CALL_VALUE >> STACK_FINISH label_preserving_sha256_bytesm) >>
          CALL_VALUE >> STACK_FINISH label_preserving_sha256_word) >>
      CALL_VALUE >> STACK_FINISH label_preserving_sha256_word) >>
  CALL_VALUE >> STACK_FINISH label_preserving_sha256_word
QED

Resume label_preserving_builtin_body[method]:
  Cases_on `method_id_literal (HD args)` >> simp_tac (srw_ss()) []
  >- (CALL_VALUE >> IF_CASES_TAC
      >- STACK_FINISH label_preserving_method_id_runtime >>
      PTR_FINISH label_preserving_method_id_runtime) >>
  strip_tac >> drule label_preserving_literal_vv >> simp[]
QED

Resume label_preserving_builtin_body[array]:
  Cases_on `o'` >> simp_tac (srw_ss()) [] >>
  CALL_PAIR label_preserving_abi_alloc_buffer
  >- PTR_FINISH label_preserving_make_tuple >>
  PTR_FINISH label_preserving_make_array
QED

Resume label_preserving_builtin_body[concat]:
  CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_emit_void >>
  CALL_PAIR label_preserving_concat >>
  CALL_PAIR label_preserving_emit_op >>
  CALL_PAIR label_preserving_emit_void >>
  strip_tac >> gvs[] >> metis_tac[label_extends_trans]
QED

Resume label_preserving_builtin_body[slice]:
  IF_CASES_TAC
  >- (ntac 2 CALL_VALUE >> PTR_FINISH label_preserving_slice_calldata) >>
  IF_CASES_TAC
  >- (ntac 2 CALL_VALUE >> PTR_FINISH label_preserving_slice_code) >>
  IF_CASES_TAC
  >- (ntac 2 CALL_VALUE >> CALL_PAIR label_preserving_slice_out_buf >>
      CALL_VALUE >> PTR_FINISH label_preserving_slice_extcode) >>
  CALL_VALUE >> IF_CASES_TAC
  >- (CALL_PAIR label_preserving_bytestring_src >> ntac 2 CALL_VALUE >>
      PTR_FINISH label_preserving_slice_data) >>
  CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_emit_void >> ntac 2 CALL_VALUE >>
  PTR_FINISH label_preserving_slice_data
QED

Finalise label_preserving_builtin_body

Theorem label_preserving_result_snd[local]:
  (!s r t. f s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !s. cs_extends s (SND (f s)) /\
    EVERY jump_label_ok (added_labels s (SND (f s)))
Proof
  strip_tac >> gen_tac >> Cases_on `f s` >> gvs[] >> metis_tac[]
QED

Theorem label_preserving_mod_names_snd[local]:
  (cs_extends s (SND (compile_addmod_names c rt at a bt b mt m s)) /\
   EVERY jump_label_ok (added_labels s
     (SND (compile_addmod_names c rt at a bt b mt m s)))) /\
  (cs_extends s (SND (compile_mulmod_names c rt at a bt b mt m s)) /\
   EVERY jump_label_ok (added_labels s
     (SND (compile_mulmod_names c rt at a bt b mt m s)))) /\
  (cs_extends s (SND (compile_powmod256_names c rt at a bt b s)) /\
   EVERY jump_label_ok (added_labels s
     (SND (compile_powmod256_names c rt at a bt b s))))
Proof
  rpt conj_tac >>
  metis_tac[label_preserving_result_snd, label_preserving_mod_names]
QED

Theorem label_preserving_expr_body[local]:
  (!c ty e s r t. cfn c ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!c rt ty bi args s r t. bfn c rt ty bi args s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) /\
  (!c vt ty tb rt args s r t. tfn c vt ty tb rt args s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)) ==>
  !cenv ty e s r t.
    compile_expr_body cfn bfn tfn cenv ty e s = (r,t) ==>
    cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `e` >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM]
  >~ [`compile_name_vv`] >- metis_tac[label_preserving_name_vv]
  >~ [`compile_literal_vv`] >- metis_tac[label_preserving_literal_vv]
  >~ [`compile_subscript`] >- metis_tac[label_preserving_subscript]
  >~ [`compile_attribute`] >- metis_tac[label_preserving_attribute]
  >~ [`compile_call`] >- metis_tac[label_preserving_call]
  >~ [`expr_type (TypeBuiltin _ _ _ _)`] >- metis_tac[]
  >~ [`fresh_label`] >- suspend "ifexp"
  >~ [`compile_struct_lit`] >- suspend "struct"
  >~ [`FLOOKUP`] >- suspend "topname"
  >~ [`compile_get_target_ptr`] >- suspend "pop"
  >~ [`expr_type (Builtin _ _ _)`] >- suspend "builtin" >>
  strip_tac >> gvs[] >>
  simp[cs_extends_refl, added_labels_def, all_blocks_def, LENGTH_MAP,
    DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Resume label_preserving_expr_body[struct]:
  CALL_PAIR label_preserving_abi_alloc_buffer >>
  CALL_PAIR label_preserving_struct_lit >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED

Resume label_preserving_expr_body[topname]:
  Cases_on `FLOOKUP cenv.ce_module_vars p` >>
  simp_tac (srw_ss()) []
  >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  Cases_on `x` >> simp_tac (srw_ss()) []
  >~ [`emit_inst`] >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[])
  >~ [`emit_inst`] >- (CALL_PAIR label_preserving_emit_inst >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  simp[cs_extends_refl, added_labels_def, all_blocks_def, LENGTH_MAP,
    DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Resume label_preserving_expr_body[pop]:
  CALL_PAIR label_preserving_get_target_ptr >>
  CALL_PAIR label_preserving_dynarray_pop >> strip_tac >> gvs[] >>
  metis_tac[label_extends_trans]
QED

Resume label_preserving_expr_body[ifexp]:
  CALL_VALUE >>
  CALL_PAIR label_preserving_fresh_var >>
  CALL_PAIR label_preserving_fresh_label >>
  CALL_PAIR label_preserving_fresh_label >>
  CALL_PAIR label_preserving_fresh_label >>
  CALL_PAIR label_preserving_emit_inst >>
  CALL_PAIR label_preserving_new_block >>
  CALL_VALUE >>
  CALL_PAIR label_preserving_emit_inst >>
  CALL_PAIR label_preserving_emit_inst >>
  CALL_PAIR label_preserving_new_block >>
  CALL_VALUE >>
  CALL_PAIR label_preserving_emit_inst >>
  CALL_PAIR label_preserving_emit_inst >>
  CALL_PAIR label_preserving_new_block >>
  Cases_on `is_word_type (expr_type (IfExp t' e' e0 e1))` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  map_every (fn st => irule label_extends_trans >> qexists st >> simp[] >>
    once_rewrite_tac[CONJ_COMM])
    [`st1`, `st2`, `st3`, `st4`, `st5`, `st6`, `st7`, `st8`,
     `st9`, `st10`, `st11`, `st12`, `st13`, `st14`]
QED

Resume label_preserving_expr_body[builtin]:
  `!c rt ty bi args s.
     cs_extends s (SND (bfn c rt ty bi args s)) /\
     EVERY jump_label_ok (added_labels s (SND (bfn c rt ty bi args s)))` by
    (rpt gen_tac >> irule label_preserving_result_snd >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `action = (r,t)` >>
  `cs_extends s (SND action) /\
    EVERY jump_label_ok (added_labels s (SND action))` suffices_by
      (rpt strip_tac >> gvs[]) >>
  unabbrev_all_tac >>
  simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  all_tac >~ [`compile_powmod256_names`] >-
    (Cases_on `b` >> asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd]) >>
  Cases_on `h` >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  BasicProvers.TOP_CASE_TAC >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd] >>
  Cases_on `b` >>
  asm_simp_tac (srw_ss()) [label_preserving_mod_names_snd]
QED
Finalise label_preserving_expr_body
