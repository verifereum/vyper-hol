(* Close the jumps of the external-call shell at their actual block openings. *)
Theory createSizeExternalReturnCode
Ancestors
  createSizeCutCode createSizeCutOpens externalEntryShape exprLowering builtinSimple
  context emitHelper compileEnv venomInst pair pred_set list

fun ext_cut_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_inst,
                  create_cut_code_emit_op, create_cut_code_emit_void,
                  create_cut_targets_def, compile_alloc_buffer_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac, IF_CASES_TAC]);

Theorem ext_cut_code_check[local,simp]:
  create_cut_code exits a (SND (compile_extcodesize_check addr a))
Proof
  ext_cut_steps [compile_extcodesize_check_def]
QED

Theorem ext_cut_return_decode[local,simp]:
  create_cut_code exits a (SND (compile_return_value_decode mn mx a))
Proof
  ext_cut_steps [compile_return_value_decode_def, compile_select_def]
QED

(* The branch opens all of the pending targets in its continuation. *)
Theorem ext_cut_branch[local]:
  !pending. l IN pending /\ r IN pending /\
  (create_cut_code pending (SND (emit_inst JNZ [c; Label l; Label r] [] a))
    (SND (k (SND (emit_inst JNZ [c; Label l; Label r] [] a)))) /\
   pending SUBSET set (added_labels (SND (emit_inst JNZ [c; Label l; Label r] [] a))
    (SND (k (SND (emit_inst JNZ [c; Label l; Label r] [] a)))))) ==>
  create_cut_code {} a
    (SND (comp_ignore_bind (emit_inst JNZ [c; Label l; Label r] []) k a))
Proof
  rpt strip_tac >>
  `create_cut_code pending a (SND (emit_inst JNZ [c; Label l; Label r] [] a))`
    by (irule create_cut_code_emit_inst >> rw[create_cut_targets_def] >> asm_rewrite_tac[]) >>
  irule create_cut_code_close >> qexists_tac `pending` >>
  reverse conj_tac >- (irule create_cut_code_ignore_bind >> simp[]) >>
  gvs[comp_ignore_bind_def, comp_bind_def, UNCURRY_VAR] >>
  fs[create_cut_code_def] >> drule_all added_labels_trans >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ext_cut_bind_open[local]:
  create_cut_code pending a (SND (m a)) /\
  (create_cut_code pending (SND (m a)) (SND (k (FST (m a)) (SND (m a)))) /\
   opens SUBSET set (added_labels (SND (m a))
                               (SND (k (FST (m a)) (SND (m a)))))) ==>
  create_cut_code pending a (SND (comp_bind m k a)) /\
  opens SUBSET set (added_labels a (SND (comp_bind m k a)))
Proof
  simp[comp_bind_def, UNCURRY_VAR] >> metis_tac[create_cut_opens_prepend]
QED

Theorem ext_cut_ignore_open[local]:
  create_cut_code pending a (SND (m a)) /\
  (create_cut_code pending (SND (m a)) (SND (k (SND (m a)))) /\
   opens SUBSET set (added_labels (SND (m a)) (SND (k (SND (m a)))))) ==>
  create_cut_code pending a (SND (comp_ignore_bind m k a)) /\
  opens SUBSET set (added_labels a (SND (comp_ignore_bind m k a)))
Proof
  simp[comp_ignore_bind_def, comp_bind_def, UNCURRY_VAR] >>
  metis_tac[create_cut_opens_prepend]
QED

Theorem ext_cut_new_block_open[local]:
  create_cut_code pending (SND (new_block l a)) (SND (k (SND (new_block l a)))) /\
  opens SUBSET set (added_labels (SND (new_block l a))
                                  (SND (k (SND (new_block l a))))) ==>
  create_cut_code pending a (SND (comp_ignore_bind (new_block l) k a)) /\
  (l INSERT opens) SUBSET set (added_labels a
                                   (SND (comp_ignore_bind (new_block l) k a)))
Proof
  simp[comp_ignore_bind_def, comp_bind_def, UNCURRY_VAR] >> strip_tac >>
  `create_cut_code pending a (SND (new_block l a))` by simp[] >>
  conj_tac >- metis_tac[create_cut_code_join] >>
  `cs_extends a (SND (new_block l a)) /\
   added_labels a (SND (new_block l a)) = [l]` by
    (Cases_on `new_block l a` >> simp[] >>
     metis_tac[cs_extends_new_block, added_labels_new_block]) >>
  fs[create_cut_code_def] >> drule_all added_labels_trans >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

(* Do not simplify an opening obligation itself until the last block opens. *)
val ext_cut_route =
  rpt (FIRST [ho_match_mp_tac ext_cut_new_block_open >> BETA_TAC,
              ho_match_mp_tac ext_cut_bind_open >> BETA_TAC >> (conj_tac >- ext_cut_steps []),
              ho_match_mp_tac ext_cut_ignore_open >> BETA_TAC >> (conj_tac >- ext_cut_steps [])]);

Theorem ext_cut_default[local]:
  (!x y rt dt b. create_cut_code {} b
    (SND (compile_store_memory cenv x y rt dt b))) /\
  (!dst off src len info b. create_cut_code {} b
    (SND (compile_abi_decode_to_buf dst off MLOAD src len info b))) ==>
  create_cut_code {} a
    (SND (compile_default_return_path cenv rt dt buf result def addr skip mn mx info a))
Proof
  strip_tac >>
  `!ex x y rt dt b. create_cut_code ex b
     (SND (compile_store_memory cenv x y rt dt b))` by metis_tac[create_cut_code_widen_empty] >>
  `!ex dst off src len info b. create_cut_code ex b
     (SND (compile_abi_decode_to_buf dst off MLOAD src len info b))`
    by metis_tac[create_cut_code_widen_empty] >>
  simp[compile_default_return_path_def] >>
  rpt (irule create_cut_code_bind >> BETA_TAC >> (conj_tac >- ext_cut_steps [])) >>
  qmatch_goalsub_abbrev_tac `[_; Label dl; Label cl]` >>
  qmatch_goalsub_abbrev_tac `emit_inst JMP [Label xl] []` >>
  ho_match_mp_tac (Q.SPEC `{dl; cl; xl}` ext_cut_branch) >> BETA_TAC >>
  (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
  ext_cut_route >> simp[]
QED

Theorem create_default_return_path_cut_code:
  (!x y rt dt b. create_cut_code {} b
    (SND (compile_store_memory cenv x y rt dt b))) /\
  (!dst off src len info b. create_cut_code {} b
    (SND (compile_abi_decode_to_buf dst off MLOAD src len info b))) ==>
  create_cut_code {} a
    (SND (compile_default_return_path cenv rt dt buf result def addr skip mn mx info a))
Proof
  simp[ext_cut_default]
QED

(* Keep each prefix cut symbolic to avoid expanding earlier states into
   every argument and both arms of the remaining template. *)
Theorem ext_cut_ignore_on[local]:
  create_cut_code exits a (SND (m a)) /\
  (!b. create_cut_code exits b (SND (k b))) ==>
  create_cut_code exits a (SND (comp_ignore_bind m k a))
Proof
  strip_tac >> irule create_cut_code_ignore_bind >> simp[]
QED

val ext_cut_next =
  FIRST [ho_match_mp_tac create_cut_code_bind_all, ho_match_mp_tac ext_cut_ignore_on] >>
  (conj_tac >- ext_cut_steps []);

Theorem create_external_kwargs_case:
  (!dst rows b. create_cut_code {} b
    (SND (compile_abi_encode_values_to_buf cenv dst rows b))) /\
  (!dst off src len info b. create_cut_code {} b
    (SND (compile_abi_decode_to_buf dst off MLOAD src len info b))) /\
  (!x y rt dt b. create_cut_code {} b
    (SND (compile_store_memory cenv x y rt dt b))) ==>
  create_cut_code {} a
    (SND (compile_external_call_kwargs cenv addr vals tys argsize mid retsize
      minsize retmem staticcall value gas skip has_default def rt dt info a))
Proof
  strip_tac >>
  simp[compile_external_call_kwargs_def, LET_DEF] >>
  ntac 6 (ext_cut_next >> rpt gen_tac >> BETA_TAC) >>
  ext_cut_next >> qx_gen_tac `fail_lbl` >> gen_tac >> BETA_TAC >>
  ext_cut_next >> qx_gen_tac `cont_lbl` >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac (Q.SPEC `{fail_lbl; cont_lbl}` ext_cut_branch) >> BETA_TAC >>
  (conj_tac >- simp[]) >> (conj_tac >- simp[]) >> ext_cut_route >>
  simp[] >>
  ext_cut_steps [] >>
  irule create_cut_code_widen_empty >> simp[ext_cut_default]
QED
