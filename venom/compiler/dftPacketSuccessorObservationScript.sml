Theory dftPacketSuccessorObservation
Ancestors
  dftPacketObservationSuccess dftGasFromListTraceDefs
  dftRunRel dftStructural venomWf venomInst venomState list rich_list

(* Index-facing form of the two-success observation boundary.  Both fuels
   are preserved; in particular the target prefix need not be a whole row. *)
Theorem dft_packet_successor_observation_agreement:
  !C C' sf tf bb bt name ps xs ys be u v gs p d
    source_fuel target_fuel orc q k inst.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
    lookup_block name sf.fn_blocks = SOME bb /\
    lookup_block name tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\
    bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
    EVERY inst_shape_ok bb.bb_instructions /\ bb_well_formed bt /\
    dft_remaining_inv sf bb xs be /\ be.vs_inst_idx = LENGTH ps /\
    q < LENGTH xs /\ k < LENGTH ys /\ EL q xs = inst /\
    (EL k ys).inst_id = inst.inst_id /\
    inv_memory_observation inst.inst_opcode /\
    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
    FOLDR (dft_exec_cons source_fuel C) OK (TAKE q xs)
      (be with vs_gas_readings := gs) = OK u /\
    FOLDR (dft_exec_cons target_fuel C') OK (TAKE k ys) be = OK v /\
    trace_agrees orc (trace_block p d source_fuel C sf
      (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
      (be with vs_gas_readings := gs)) /\
    trace_agrees orc (trace_block p d target_fuel C' tf
      (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be) ==>
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op v) /\
    u.vs_initial_fmp = v.vs_initial_fmp
Proof
  rpt gen_tac >> strip_tac >>
  `xs = TAKE q xs ++ inst::DROP (SUC q) xs` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  `ys = TAKE k ys ++ EL k ys::DROP (SUC k) ys` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  `EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys)` by
    (qpat_assum `bb_well_formed bt`
       (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  irule (Q.INST [`pre` |-> `TAKE q xs`, `scheduled` |-> `TAKE k ys`]
    (SPEC_ALL dft_packet_native_observation_success)) >> simp[] >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK v`)) >>
  simp[LENGTH_TAKE] >>
  goal_assum (drule_at (Pat `MEM _ _.fn_blocks`)) >>
  goal_assum (drule_at (Pat `dft_fn_rel _ _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ tf.fn_blocks = SOME _`)) >>
  goal_assum (drule_at (Pat `EVERY (\x. is_pseudo x.inst_opcode) _`)) >>
  simp[NoAsms, arithmeticTheory.ADD_COMM] >>
  qpat_assum `trace_agrees _ (trace_block _ _ _ C sf _ _)`
    (assume_tac o SRULE [arithmeticTheory.ADD_COMM]) >>
  goal_assum (drule_at (Pat `trace_agrees _ (trace_block _ _ _ C sf _ _)`)) >>
  qexistsl_tac [`DROP (SUC k) ys`, `DROP (SUC q) xs`, `EL k ys`] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `xs = TAKE q xs ++ inst::DROP (SUC q) xs`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `ys = TAKE k ys ++ EL k ys::DROP (SUC k) ys`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (simp[EVERY_TAKE, EVERY_DROP] >>
      fs[EVERY_EL] >> metis_tac[]) >>
  qpat_x_assum `trace_agrees _ (trace_block _ _ _ C' tf _ _)` mp_tac >>
  simp[arithmeticTheory.ADD_COMM]
QED
