(* Supported type-builtin callback boundaries. *)
Theory bodyIntCallTypeBuiltinLabels
Ancestors
  bodyIntCallBuiltinLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  bodyIntCallContextLabels bodyIntCallExprLabels
  supportedExprForms exprLowering compileEnv builtinSimple

Theorem compiler_block_tail_type_extrema_dispatch:
  (tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  compiler_block_tail
    (compile_type_builtin_dispatch_body cfn cenv ann ty tb rt args)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `type_bounds rt` >> simp[compiler_block_tail_def]
QED

Theorem compiler_label_hoare_type_extrema_dispatch:
  (tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  compiler_label_hoare P
    (compile_type_builtin_dispatch_body cfn cenv ann ty tb rt args)
    (\r out. P out)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `type_bounds rt` >> simp[compiler_label_hoare_def]
QED

Theorem compiler_block_tail_zero_words:
  !n buf. compiler_block_tail (compile_zero_words buf n)
Proof
  Induct >> simp[compile_zero_words_def, comp_ignore_bind_def,
                 compiler_block_tail_primitives] >> gen_tac >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_zero_words:
  !n buf. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_zero_words buf n)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> simp[compile_zero_words_def, comp_ignore_bind_def,
                 compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_empty_complex:
  compiler_block_tail (compile_builtin_empty_complex sz z)
Proof
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- simp[compiler_block_tail_alloc_buffer] >>
  gen_tac >> ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- simp[compiler_block_tail_primitives] >>
  gen_tac >> Cases_on `z` >> simp[] >>
  ho_match_mp_tac compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_zero_words]
QED

Theorem compiler_label_hoare_empty_complex:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_empty_complex sz z)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
  >- simp[compiler_label_hoare_storage_primitives] >>
  gen_tac >> ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
  >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  gen_tac >> Cases_on `z` >> simp[] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
       compiler_label_hoare_zero_words]
QED

Theorem compiler_block_tail_empty_dispatch:
  compiler_block_tail
    (compile_type_builtin_dispatch_body cfn cenv ann ty Empty rt args)
Proof
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `is_word_type rt` >> simp[compiler_block_tail_def] >>
  qspecl_then [`type_memory_bytes cenv rt`,
    `is_bytestring_type rt \/ case rt of ArrayT _ (Dynamic _) => T | _ => F`]
    mp_tac (Q.GENL [`sz`, `z`] compiler_block_tail_empty_complex) >>
  simp[compiler_block_tail_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`tail`, `st`] mp_tac) >>
  Cases_on `compile_builtin_empty_complex (type_memory_bytes cenv rt)
    (is_bytestring_type rt \/ case rt of ArrayT _ (Dynamic _) => T | _ => F) st` >>
  simp[]
QED

Theorem compiler_label_hoare_empty_dispatch:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_type_builtin_dispatch_body cfn cenv ann ty Empty rt args)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `is_word_type rt` >> simp[compiler_label_hoare_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >>
  drule (REWRITE_RULE [compiler_label_hoare_def] compiler_label_hoare_empty_complex) >>
  disch_then drule >> simp[]
QED

Theorem compiler_block_tail_type_convert:
  compiler_block_tail (compile_type_convert v cv)
Proof
  Cases_on `cv` >> simp[compile_type_convert_def, comp_ignore_bind_def,
    compiler_block_tail_primitives, compiler_label_hoare_context_primitives,
    compiler_label_hoare_typed_primitives, load_bytestring_as_word_def,
    compiler_block_tail_alloc_buffer, compiler_label_hoare_storage_primitives] >>
  rpt (FIRST [ho_match_mp_tac compiler_block_tail_bind >> conj_tac,
              ho_match_mp_tac compiler_block_tail_cond >> conj_tac,
              gen_tac, pairarg_tac >> gvs[]] >>
       simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer])
QED

Theorem compiler_label_hoare_type_convert:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_type_convert v cv)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `cv` >> simp[compile_type_convert_def, comp_ignore_bind_def,
    compiler_block_tail_primitives, compiler_label_hoare_context_primitives,
    compiler_label_hoare_typed_primitives, load_bytestring_as_word_def,
    compiler_block_tail_alloc_buffer, compiler_label_hoare_storage_primitives] >>
  rpt (FIRST [ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac,
              IF_CASES_TAC,
              gen_tac, pairarg_tac >> gvs[]] >>
       simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
            compiler_label_hoare_storage_primitives])
QED

Theorem compiler_block_tail_convert_dispatch:
  (!ce t. compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail
    (compile_type_builtin_dispatch_body cfn cenv ann ty Convert rt [e])
Proof
  strip_tac >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> Cases_on `rt` >> simp[] >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_type_convert]
QED

Theorem compiler_label_hoare_convert_dispatch:
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_type_builtin_dispatch_body cfn cenv ann ty Convert rt [e])
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> Cases_on `rt` >> simp[] >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_type_convert]
QED
