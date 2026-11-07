Theory exprSimIfExpWidenedRoot
Ancestors
  exprSimIfExpWidenedSelectedCounted exprSimIfExpWidenedSource
  exprSimIfExpWidenedPost exprSimIfExpWidenedCode
  gasOutcome gasSummary fragGasMode fragGasPath fragGasSeqAbort
  placeTypedCopyPath stmtSimProps emitHelperProps venomExecSemantics venomInst venomState exprSimUint2Str

Theorem outcome_zero_suffix[local]:
  gas_outcome F tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
    ?v. gas_marked_path F ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q' R
Proof
  rw[gas_outcome_def] >> qexists_tac `marks` >>
  Cases_on `gas_summary_at F (ctx,func) marks source (es,s0) Q R`
  >- (disj1_tac >>
      fs[gas_summary_at_def] >>
      gvs[]
      >- (`~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             metis_tac[cj 1 gas_path_normal]) >>
          first_x_assum drule_all >> strip_tac >>
          qexistsl_tac [`res`, `es_end`, `OK v`] >>
          simp[] >> fs[gas_marked_exec_def] >>
          metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem assign_join_path[local]:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_marked_path F ctx func u 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME (mk_inst sx.cs_next_id ASSIGN [op] [rv])` by
    metis_tac[place_copy_emit_instruction] >>
  drule_at (Pat `get_instruction _ _ = _`) gas_marked_path_step >>
  simp[] >>
  disch_then irule >> simp[is_terminator_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `update_var rv w u` >>
  conj_tac >- (irule u2s_step_assign >> simp[]) >>
  `sy.cs_current_insts = sx.cs_current_insts ++
      [mk_inst sx.cs_next_id ASSIGN [op] [rv]] /\
   sy.cs_current_bb = sx.cs_current_bb` by
    metis_tac[emit_inst_extends] >>
  `LENGTH sy.cs_current_insts = SUC (LENGTH sx.cs_current_insts)` by simp[] >>
  simp[gas_marked_path_def] >>
  irule emit_jump_zero_path >>
  conj_tac >- simp[update_var_def] >>
  qexistsl_tac [`sy`, `sz`] >>
  drule_all emit_inst_extends >> strip_tac >>
  drule_all emit_inst_extends >> strip_tac >>
  simp[update_var_def]
QED
