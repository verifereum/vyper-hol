Theory dftLocalOrdinaryClosure
Ancestors
  dftOccurrenceOrdinaryClosure dftOrdinaryStop dftOrdinarySwap venomExecSemantics venomEffects venomInst venomWf list
Libs
  stepInstBaseLib

Theorem dft_shaped_ordinary_outcome:
  inst_wf i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA /\
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst_base i s = OK t) \/
  (?a t. step_inst_base i s = Abort a t)
Proof
  strip_tac >>
  Cases_on `opcode_fail_class i.inst_opcode = NoFail`
  >- (disj1_tac >> irule dft_ordinary_nofail_total >>
      simp[] >> Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def]) >>
  Cases_on `opcode_fail_class i.inst_opcode = CanExHalt`
  >- (drule_all dft_ordinary_canexhalt_defined >> metis_tac[]) >>
  `i.inst_opcode = ASSERT` by
    (Cases_on `i.inst_opcode` >> gvs[opcode_fail_class_def]) >>
  gvs[inst_wf_def] >> with_opcode_clause simp >>
  gvs[LENGTH_EQ_NUM_compute] >>
  `?v. eval_operand h s = SOME v` by metis_tac[] >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_shaped_ordinary_no_error:
  inst_wf i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA /\
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  !e. step_inst_base i s <> Error e
Proof
  strip_tac >> drule_all dft_shaped_ordinary_outcome >>
  strip_tac >> gvs[]
QED

Theorem dft_ordinary_sync_pair_segment_local:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ y.inst_opcode <> ALLOCA /\
  ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (!sx. step_inst_base x s = OK sx ==>
    !op. MEM op y.inst_operands ==>
      ?v. eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = SOME v) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    (dft_ordinary_sync bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) \/
     dft_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d)) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  `(?sx. step_inst_base x s = OK sx) \/
   (?a t. step_inst_base x s = Abort a t)` by
    (irule dft_shaped_ordinary_outcome >> simp[]) >>
  pop_assum strip_assume_tac
  >- (rename1 `step_inst_base x s = OK sx` >>
      `(?sy. step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sy) \/
       (?a t. step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t)` by
        (irule dft_shaped_ordinary_outcome >> simp[]) >>
      pop_assum strip_assume_tac
      >- (qexistsl_tac [`2`, `2`] >> simp[] >> conj_tac
          >- (disj1_tac >> irule dft_ordinary_sync_success >> metis_tac[]) >>
          irule dft_ordinary_sync_success_cover >> metis_tac[]) >>
      qexistsl_tac [`3`, `2`] >> simp[] >>
      drule_all dft_ordinary_second_abort_segment >> strip_tac >> simp[]) >>
  drule_all dft_ordinary_first_abort_segment >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  qexistsl_tac [`2`, `j`] >> simp[]
QED
