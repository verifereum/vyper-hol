(* Successful indexed-prefix boundaries for DFT schedule simulation. *)
Theory dftFramePrefix
Ancestors
  dftFrameFacts dftFrameCertificate dftFrameNormalize dftPermSim venomExecSemantics venomWf venomInst
  o1PassLift dftDefs passSharedDefs venomEffects instIdxIndep list relation

Theorem dft_assert_unreachable_ok_identity:
  inst_wf b /\ b.inst_opcode = ASSERT_UNREACHABLE /\
  step_inst fuel C b s = OK t ==> t = s
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem dft_exceptional_observation:
  dft_cross a b /\ a.inst_opcode = RETURNDATACOPY /\
  b.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf b /\
  step_inst fuel C b s = OK t ==> mem_corr a s a t /\ call_corr a s a t
Proof
  strip_tac >> drule_all dft_assert_unreachable_ok_identity >>
  strip_tac >> gvs[mem_corr_def, call_corr_def]
QED

(* Each successful non-terminator may use its own call fuel.  The explicit
   index update is the one made by exec_block, not by step_inst itself. *)
Definition dft_prefix_def:
  (dft_prefix C [] s t <=> t = s) /\
  (dft_prefix C (i::is) s t <=>
    ~is_terminator i.inst_opcode /\
    ?fuel u. step_inst fuel C i s = OK u /\
      dft_prefix C is (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem dft_prefix_empty[simp]:
  dft_prefix C [] s t <=> t = s
Proof
  simp[dft_prefix_def]
QED

Theorem dft_prefix_cons:
  dft_prefix C (i::is) s t <=>
    ~is_terminator i.inst_opcode /\
    ?fuel u. step_inst fuel C i s = OK u /\
      dft_prefix C is (u with vs_inst_idx := SUC s.vs_inst_idx) t
Proof
  simp[dft_prefix_def]
QED

Theorem dft_prefix_append:
  !xs ys s t. dft_prefix C (xs ++ ys) s t <=>
    ?u. dft_prefix C xs s u /\ dft_prefix C ys u t
Proof
  Induct >> simp[dft_prefix_cons] >> metis_tac[]
QED

Theorem dft_flip_inst_step:
  dft_flip_inst i j ==> step_inst fuel C j s = step_inst fuel C i s
Proof
  simp[dft_flip_inst_def] >> strip_tac >> gvs[flip_operands_step_inst]
QED

Theorem dft_flip_inst_terminator:
  dft_flip_inst i j ==> (is_terminator j.inst_opcode <=> is_terminator i.inst_opcode)
Proof
  simp[dft_flip_inst_def] >> strip_tac >> gvs[] >>
  simp[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  rename1 `i.inst_operands = op1::rest1` >>
  Cases_on `rest1` >> simp[] >>
  rename1 `i.inst_operands = op1::op2::rest2` >>
  Cases_on `rest2` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def,
      flip_comparison_opcode_def, is_terminator_def]
QED

Theorem dft_flip_prefix:
  !xs ys. LIST_REL dft_flip_inst xs ys ==>
    !s t. (dft_prefix C xs s t <=> dft_prefix C ys s t)
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  simp[dft_prefix_cons] >>
  drule dft_flip_inst_step >> disch_then (fn th => rewrite_tac[th]) >>
  drule dft_flip_inst_terminator >> disch_then (fn th => rewrite_tac[th]) >>
  first_x_assum drule >> simp[]
QED

Theorem dft_noninvoke_step_index:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK t ==>
  step_inst fuel C i (s with vs_inst_idx := n) = OK (t with vs_inst_idx := n)
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_inst_idx_indep >> simp[exec_result_map_def]
QED
