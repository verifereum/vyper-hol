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
