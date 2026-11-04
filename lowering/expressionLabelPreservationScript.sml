(* Expression helper compilation preserves only the CFG extension and labels. *)
Theory expressionLabelPreservation
Ancestors
  decoderLabelPreservation entryLabelPreservation exprLowering compileEnv
  loweringShapeDefs emitHelper list

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
