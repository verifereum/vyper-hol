(* DFT's existing result relation permits a static exceptional halt to
   become another abort. CODECOPY partners still need defined labels. *)
Theory dftStaticAbort
Ancestors
  dftRunRel dftBlockSim dftDefs dftIndexedExec venomEffects venomInst
  venomWf venomExecSemantics venomState list pred_set
Libs
  stepInstBaseLib

Theorem static_nonroot_exhalt_opcodes[local]:
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  opcode_fail_class x.inst_opcode = CanExHalt ==>
  MEM x.inst_opcode [RETURNDATACOPY; CREATE; CREATE2; SSTORE; TSTORE; LOG; CALL]
Proof
  strip_tac >> Cases_on `x.inst_opcode` >>
  gvs[opcode_fail_class_def, is_terminator_def, inst_wf_def,
      read_effects_def, write_effects_def]
QED

Theorem static_exhalt_partner[local]:
  dft_gas_swap_pair x y /\
  MEM x.inst_opcode [RETURNDATACOPY; CREATE; CREATE2; SSTORE; TSTORE; LOG; CALL] ==>
  y.inst_opcode <> INVOKE /\ ~dft_swap_runtime_error_opcode y.inst_opcode
Proof
  strip_tac >>
  `effects_independent x.inst_opcode y.inst_opcode` by
    fs[dft_gas_swap_pair_def] >>
  qpat_x_assum `dft_gas_swap_pair _ _` kall_tac >> fs[] >>
  simp[dft_swap_runtime_error_opcode_def] >> rpt strip_tac >>
  qpat_x_assum `effects_independent _ _` mp_tac >>
  asm_rewrite_tac[] >> EVAL_TAC
QED

Theorem static_assert_total[local]:
  inst_wf i /\ i.inst_opcode = ASSERT /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst fuel C i s = OK t) \/
  (?t. step_inst fuel C i s = Abort Revert_abort t)
Proof
  strip_tac >>
  `?arg. i.inst_operands = [arg]` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  gvs[] >>
  `?v. eval_operand arg s = SOME v` by metis_tac[MEM] >>
  simp[step_inst_non_invoke] >> with_opcode_clause simp >>
  IF_CASES_TAC >> simp[]
QED

Theorem dft_nongas_suffix_first_abort_static:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst fuel C x s = Abort a t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Abort a t /\
  ?b u. dft_exec_suffix fuel C (y::x::tail) s = Abort b u /\
        (a = Revert_abort ==> b = Revert_abort)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `(?sy. step_inst fuel C y s = OK sy) \/
   (?b u. step_inst fuel C y s = Abort b u /\
          (a = Revert_abort ==> b = Revert_abort))` by
    (Cases_on `x.inst_opcode = INVOKE`
     >- (drule_all dft_swap_invoke_partner_class >> strip_tac >>
         `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def]) >>
         disj1_tac >> irule dft_swap_guarded_nofail_total >> simp[]) >>
     drule_all dft_swap_nonroot_abort_class >> strip_tac >> gvs[] >>
     `MEM x.inst_opcode
        [RETURNDATACOPY; CREATE; CREATE2; SSTORE; TSTORE; LOG; CALL]` by
       (irule static_nonroot_exhalt_opcodes >> simp[]) >>
     drule_all static_exhalt_partner >> strip_tac >>
     `!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v` by
       metis_tac[] >>
     Cases_on `y.inst_opcode = ASSERT`
     >- (drule_all static_assert_total >> metis_tac[]) >>
     `opcode_fail_class y.inst_opcode = NoFail \/
      opcode_fail_class y.inst_opcode = CanExHalt` by
       (Cases_on `y.inst_opcode` >> simp[opcode_fail_class_def] >> gvs[]) >>
     pop_assum strip_assume_tac
     >- (disj1_tac >> irule dft_swap_guarded_nofail_total >> simp[]) >>
     drule_all dft_swap_canexhalt_operand_defined >> metis_tac[])
  >- (`dft_gas_swap_pair y x /\ ~gas_pair y.inst_opcode x.inst_opcode` by
        (gvs[dft_gas_swap_pair_sym, gas_pair_def] >> metis_tac[]) >>
      `?u. step_inst fuel C x sy = Abort a u` by
        metis_tac[dft_nongas_pair_abort_iff] >>
      `?u. step_inst fuel C x
         (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[dft_swap_abort_idx_iff] >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def] >> metis_tac[]) >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def] >> metis_tac[]
QED
