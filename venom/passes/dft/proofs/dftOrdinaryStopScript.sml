Theory dftOrdinaryStop
Ancestors
  dftOrdinarySwap dftOccurrenceOrdinaryObserve venomExecSemantics
  venomInstProofs venomInst venomEffects venomState venomWf opcodeClass list
Libs
  stepInstBaseLib

Theorem dft_ordinary_abort_replay:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  (!op. MEM op i.inst_operands ==> eval_operand op s' = eval_operand op s) /\
  (i.inst_opcode = RETURNDATACOPY ==> s'.vs_returndata = s.vs_returndata) /\
  step_inst_base i s = Abort a t ==>
  ?t'. step_inst_base i s' = Abort a t'
Proof
  strip_tac >> drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def] >>
  with_opcode_clause gvs >> gvs[AllCaseEqs()]
QED

Theorem dft_ordinary_no_halt:
  ~is_terminator i.inst_opcode ==> step_inst_base i s <> Halt t
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule step_inst_base_halt_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_ordinary_pair_abort_iff:
  dft_ordinary_swap_pair x y /\ step_inst_base x s = OK sx ==>
  ((?t. step_inst_base y sx = Abort a t) <=>
   (?t. step_inst_base y s = Abort a t))
Proof
  strip_tac >>
  `x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE /\
   ~is_terminator y.inst_opcode` by fs[dft_ordinary_swap_pair_def] >>
  `step_inst 0 C x s = OK sx` by simp[step_inst_non_invoke] >>
  `!op. MEM op y.inst_operands ==> eval_operand op sx = eval_operand op s` by
    (metis_tac[dft_ordinary_observe_operand, dft_ordinary_swap_pair_sym]) >>
  `(y.inst_opcode = RETURNDATACOPY ==> sx.vs_returndata = s.vs_returndata)` by
    (strip_tac >> irule write_effects_sound_returndata >>
     qexistsl_tac [`C`, `0`, `x`] >> simp[] >>
     gvs[dft_ordinary_swap_pair_def, effects_independent_def,
       read_effects_def, empty_effects_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  eq_tac >> strip_tac >> irule dft_ordinary_abort_replay >> metis_tac[]
QED

Theorem dft_ordinary_abort_idx_iff:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE ==>
  ((?t. step_inst_base i (s with vs_inst_idx := k) = Abort a t) <=>
   (?t. step_inst_base i s = Abort a t))
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (irule dft_ordinary_abort_replay >> simp[] >>
      qexistsl_tac [`s with vs_inst_idx := k`, `t`] >>
      simp[] >> rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  irule dft_ordinary_abort_replay >> simp[] >>
  qexistsl_tac [`s`, `t`] >> simp[] >> rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem dft_ordinary_nonroot_abort_class:
  inst_wf x /\ ~is_terminator x.inst_opcode /\ x.inst_opcode <> INVOKE /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  step_inst_base x s = Abort a t ==>
  x.inst_opcode = RETURNDATACOPY /\ a = ExHalt_abort
Proof
  strip_tac >> drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def, inst_wf_def, read_effects_def, write_effects_def] >>
  with_opcode_clause gvs >> gvs[AllCaseEqs()]
QED

Theorem dft_ordinary_returndatacopy_partner_class:
  dft_ordinary_swap_pair x y /\ x.inst_opcode = RETURNDATACOPY ==>
  (opcode_fail_class y.inst_opcode = NoFail /\
   ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2]) \/
  opcode_fail_class y.inst_opcode = CanExHalt
Proof
  strip_tac >> Cases_on `y.inst_opcode` >>
  simp[write_effects_def, opcode_fail_class_def] >>
  gvs[dft_ordinary_swap_pair_def, effects_independent_def, abort_compatible_def,
      opcode_fail_class_def, read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def]
QED

Theorem dft_ordinary_canexhalt_defined:
  inst_wf i /\ opcode_fail_class i.inst_opcode = CanExHalt /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst_base i s = OK t) \/
  (?t. step_inst_base i s = Abort ExHalt_abort t)
Proof
  strip_tac >>
  `i.inst_opcode = ASSERT_UNREACHABLE \/
   i.inst_opcode = RETURNDATACOPY \/ i.inst_opcode = INVALID` by
    (Cases_on `i.inst_opcode` >> gvs[opcode_fail_class_def]) >>
  gvs[inst_wf_def] >> with_opcode_clause simp >>
  gvs[LENGTH_EQ_NUM_compute] >>
  rpt IF_CASES_TAC >> simp[] >>
  `?a. eval_operand h s = SOME a` by metis_tac[] >>
  `?b. eval_operand h' s = SOME b` by metis_tac[] >>
  `?c. eval_operand h'' s = SOME c` by metis_tac[] >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_ordinary_pure1_total[local]:
  LENGTH i.inst_operands = 1 /\ LENGTH i.inst_outputs = 1 /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure1 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[exec_pure1_def]
QED

Theorem dft_ordinary_pure2_total[local]:
  LENGTH i.inst_operands = 2 /\ LENGTH i.inst_outputs = 1 /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure2 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `i.inst_operands = [a;b]` >>
  `?va. eval_operand a s = SOME va` by metis_tac[] >>
  `?vb. eval_operand b s = SOME vb` by metis_tac[] >> simp[exec_pure2_def]
QED

Theorem dft_ordinary_pure3_total[local]:
  LENGTH i.inst_operands = 3 /\ LENGTH i.inst_outputs = 1 /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure3 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `i.inst_operands = [a;b;c]` >>
  `?va. eval_operand a s = SOME va` by metis_tac[] >>
  `?vb. eval_operand b s = SOME vb` by metis_tac[] >>
  `?vc. eval_operand c s = SOME vc` by metis_tac[] >> simp[exec_pure3_def]
QED

Theorem dft_ordinary_read0_total[local]:
  LENGTH i.inst_outputs = 1 ==> ?t. exec_read0 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> simp[exec_read0_def]
QED

Theorem dft_ordinary_read1_total[local]:
  LENGTH i.inst_operands = 1 /\ LENGTH i.inst_outputs = 1 /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_read1 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[exec_read1_def]
QED

Theorem dft_ordinary_write2_total[local]:
  LENGTH i.inst_operands = 2 /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_write2 f i s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `i.inst_operands = [a;b]` >>
  `?va. eval_operand a s = SOME va` by metis_tac[] >>
  `?vb. eval_operand b s = SOME vb` by metis_tac[] >> simp[exec_write2_def]
QED

Theorem dft_ordinary_ext_call_total[local]:
  LENGTH i.inst_outputs = 1 ==>
  ?t. exec_ext_call i s gas addr value ao az ro rz static = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >>
  simp[exec_ext_call_def] >> pairarg_tac >> simp[]
QED

Theorem dft_ordinary_eval_operands_defined[local]:
  !ops. (!op. MEM op ops ==> ?v. eval_operand op s = SOME v) ==>
        ?vs. eval_operands ops s = SOME vs
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem dft_ordinary_nofail_total:
  inst_wf i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  opcode_fail_class i.inst_opcode = NoFail /\
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. step_inst_base i s = OK t
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, is_alloca_op_def, opcode_fail_class_def] >>
  fs[inst_wf_def] >> with_opcode_clause simp >> all_tac
  >>~- ([`exec_pure1 _ _ _`], irule dft_ordinary_pure1_total >> simp[])
  >>~- ([`exec_pure2 _ _ _`], irule dft_ordinary_pure2_total >> simp[])
  >>~- ([`exec_pure3 _ _ _`], irule dft_ordinary_pure3_total >> simp[])
  >>~- ([`exec_read0 _ _ _`], irule dft_ordinary_read0_total >> simp[])
  >>~- ([`exec_read1 _ _ _`], irule dft_ordinary_read1_total >> simp[])
  >>~- ([`exec_write2 _ _ _`], irule dft_ordinary_write2_total >> simp[])
  >>~- ([`eval_operands _ _`], suspend "log_total") >>
  gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM]
  >>~- ([`exec_ext_call _ _ _ _ _ _ _ _ _ _`],
         irule dft_ordinary_ext_call_total >> simp[])
QED

Resume dft_ordinary_nofail_total[log_total]:
  `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
    (conj_tac >> once_rewrite_tac[GSYM MEM_REVERSE] >>
     irule EL_MEM >> simp[]) >>
  `?off. eval_operand (EL 0 (REVERSE rest)) s = SOME off` by metis_tac[MEM] >>
  `?sz. eval_operand (EL 1 (REVERSE rest)) s = SOME sz` by metis_tac[MEM] >>
  `?topics. eval_operands (DROP 2 (REVERSE rest)) s = SOME topics` by
    (irule dft_ordinary_eval_operands_defined >> rpt strip_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[] >> strip_tac >> metis_tac[MEM]) >>
  fs[]
QED

Finalise dft_ordinary_nofail_total

Theorem dft_ordinary_first_stop_partner:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst_base x s = Abort a t ==>
  (?sy. step_inst_base y s = OK sy) \/
  (?u. step_inst_base y s = Abort a u)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ x.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  drule_all dft_ordinary_nonroot_abort_class >> strip_tac >>
  drule_all dft_ordinary_returndatacopy_partner_class >> strip_tac
  >- (disj1_tac >> irule dft_ordinary_nofail_total >>
      fs[dft_ordinary_swap_pair_def]) >>
  gvs[] >> irule dft_ordinary_canexhalt_defined >> simp[]
QED

Theorem dft_ordinary_pair_abort_indexed_iff:
  dft_ordinary_swap_pair x y /\ step_inst_base x s = OK sx ==>
  ((?t. step_inst_base y (sx with vs_inst_idx := k) = Abort a t) <=>
   (?t. step_inst_base y s = Abort a t))
Proof
  strip_tac >>
  `~is_terminator y.inst_opcode /\ y.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  simp[dft_ordinary_abort_idx_iff] >>
  irule dft_ordinary_pair_abort_iff >> metis_tac[]
QED

Theorem dft_ordinary_first_abort_crossing:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst_base x s = Abort a t ==>
  (?u. step_inst_base y s = Abort a u) \/
  (?sy u. step_inst_base y s = OK sy /\
          step_inst_base x (sy with vs_inst_idx := k) = Abort a u)
Proof
  strip_tac >> drule_all dft_ordinary_first_stop_partner >> strip_tac
  >- (disj2_tac >>
      `dft_ordinary_swap_pair y x` by metis_tac[dft_ordinary_swap_pair_sym] >>
      drule_all dft_ordinary_pair_abort_indexed_iff >>
      disch_then (qspecl_then [`k`, `a`] mp_tac) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem dft_ordinary_second_abort_crossing:
  dft_ordinary_swap_pair x y /\ step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := k) = Abort a t ==>
  ?u. step_inst_base y s = Abort a u
Proof
  metis_tac[dft_ordinary_pair_abort_indexed_iff]
QED
