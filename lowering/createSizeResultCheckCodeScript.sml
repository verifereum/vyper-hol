(* Static closure of the two branch destinations in the CREATE result check. *)
Theory createSizeResultCheckCode
Ancestors
  createSizeCutOpens createSizeCutCode builtinCreate context emitHelper
  compileEnv venomInst pair pred_set list

(* An instruction that opens no block carries the remaining openings. *)
val result_check_carry =
  match_mp_tac (SIMP_RULE std_ss [UNION_EMPTY, EMPTY_SUBSET]
    (Q.INST [`opened1` |-> `{}`] create_cut_opens_bind)) >> BETA_TAC;

Theorem create_result_check_cut_code:
  create_cut_code {} a (SND (compile_check_create_result created rof a))
Proof
  Cases_on `rof` >> simp[compile_check_create_result_def] >>
  irule create_cut_code_bind >> (conj_tac >- simp[]) >> BETA_TAC >>
  irule create_cut_code_bind >> (conj_tac >- simp[]) >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `emit_inst JNZ [_; Label klbl; Label flbl] []` >>
  match_mp_tac (Q.INST [`pending` |-> `{flbl;klbl}`,
                        `opened` |-> `{flbl} UNION {klbl}`] create_cut_opens_close) >>
  (reverse conj_tac >- simp[SUBSET_DEF]) >>
  pure_rewrite_tac[comp_ignore_bind_def] >>
  result_check_carry >>
  (conj_tac >- (irule create_cut_code_emit_inst >>
                simp[create_cut_targets_def, DISJ_IMP_THM])) >>
  match_mp_tac create_cut_opens_bind >> BETA_TAC >>
  (conj_tac >- simp[create_cut_opens_block]) >>
  result_check_carry >>
  (conj_tac >- simp[create_cut_code_emit_op, create_cut_targets_def]) >>
  result_check_carry >>
  (conj_tac >- (simp[compile_alloc_buffer_def] >> irule create_cut_code_bind >>
                simp[create_cut_code_emit_op, create_cut_targets_def])) >>
  result_check_carry >>
  (conj_tac >- simp[create_cut_code_emit_void, create_cut_targets_def]) >>
  result_check_carry >>
  (conj_tac >- simp[create_cut_code_emit_inst, create_cut_targets_def]) >>
  simp[comp_bind_def, UNCURRY_VAR, comp_return_def,
       SIMP_RULE (srw_ss()) [] create_cut_opens_block]
QED
