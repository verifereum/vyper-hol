Theory gasFocusCurrentCursor
Ancestors
  dftFinitePacket dftGasInvCrossingProbe dftRunRel dftScheduleOrder dftSsaPreserve dftWf dftStructural
  dftDefs venomEffects passSharedDefs venomExecProps venomInst venomWf
  list rich_list sorting arithmetic

Theorem focus_terminal_schedule_prefix:
  !sched sf tf bb bt ps xs ys pos q inst.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\r y. r < LENGTH xs /\ y.inst_id = (EL r xs).inst_id /\
    from_block [EL r xs] y) sched ys /\
  pos < LENGTH ys /\ q = EL pos sched /\ inst = EL pos ys /\
  is_terminator inst.inst_opcode ==>
  pos < LENGTH sched /\ q < LENGTH xs /\ EL q xs = inst /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE pos sched))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `pos < LENGTH sched` by metis_tac[LIST_REL_LENGTH] >>
  `q < LENGTH xs /\ inst.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] inst` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o PURE_ONCE_REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `pos` mp_tac) >> simp[]) >>
  `is_terminator (EL q xs).inst_opcode` by
    (mp_tac (Q.INST [`bi` |-> `[EL q xs]`, `i` |-> `inst`, `j` |-> `EL q xs`]
       dft_from_block_terminator) >> simp[]) >>
  `EL q xs = inst` by
    (qpat_assum `from_block [EL q xs] inst` mp_tac >>
     qpat_assum `is_terminator (EL q xs).inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[from_block_def] >>
     Cases_on `(EL q xs).inst_opcode` >>
     simp[is_flippable_def, is_commutative_def, is_comparator_def, is_terminator_def]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  `EL q xs = EL pos ys` by simp[] >>
  irule dft_packet_ordered_schedule_predecessors >>
  rpt (first_assum (irule_at Any)) >> simp[dft_must_order_def]
QED

Theorem focus_current_guard_schedule:
  !sched sf tf bb bt ps xs ys pos q inst.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\r y. r < LENGTH xs /\ y.inst_id = (EL r xs).inst_id /\
    from_block [EL r xs] y) sched ys /\
  pos < LENGTH ys /\ q = EL pos sched /\ inst = EL pos ys /\
  (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
   inst.inst_opcode = INVOKE \/ is_terminator inst.inst_opcode) ==>
  pos < LENGTH sched /\ q < LENGTH xs /\ EL q xs = inst /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE pos sched))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all focus_terminal_schedule_prefix >> disch_then ACCEPT_TAC) >>
  `pos < LENGTH sched` by metis_tac[LIST_REL_LENGTH] >>
  `q < LENGTH xs /\ from_block [EL q xs] inst` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o PURE_ONCE_REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `pos` mp_tac) >> simp[]) >>
  `EL q xs = inst` by
    (qpat_assum `from_block [EL q xs] inst` mp_tac >>
     qpat_assum `inv_memory_observation inst.inst_opcode \/ _` mp_tac >>
     qpat_assum `~is_terminator inst.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rw[from_block_def] >>
     Cases_on `(EL q xs).inst_operands` >> gvs[flip_operands_def] >>
     Cases_on `t` >> gvs[flip_operands_def] >>
     Cases_on `t'` >> gvs[flip_operands_def] >>
     Cases_on `(EL q xs).inst_opcode` >>
     qpat_x_assum `is_flippable _` mp_tac >>
     simp_tac (srw_ss()) [is_flippable_def,is_commutative_def,is_comparator_def] >>
     gvs[dftGasInvCrossingProbeTheory.inv_memory_observation_def,is_fallible_def,
         opcode_fail_class_def,is_comparator_def,flip_comparison_opcode_def]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  `EL q xs = EL pos ys` by simp[] >>
  qpat_assum `inst = EL pos ys` SUBST_ALL_TAC >>
  Cases_on `inv_memory_observation (EL pos ys).inst_opcode`
  >- (irule dft_packet_memory_schedule_predecessors >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  irule dft_packet_schedule_predecessors >>
  rpt (first_assum (irule_at Any)) >> gvs[]
QED
