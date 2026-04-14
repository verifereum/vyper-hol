(*
 * asm_bytecode_sim_aux: Forward simulation for multi-step asm -> EVM.
 *
 * Core induction: by induction on n, each asm step either
 *   (a) produces an EVM exception (absorbed by first disjunct), or
 *   (b) corresponds to an EVM step preserving asm_evm_rel, letting
 *       the IH handle the remaining n steps.
 *
 * jumpDest = NONE is part of asm_evm_rel, so it's automatically
 * maintained by asm_evm_step's guarantee of asm_evm_rel on output.
 *)


Theory asmBytecodeSim
Ancestors
  asmSem codegenRel asmWf vfmExecution vfmConstants evmStepSim list arithmetic
(* Helper: reachability condition implies stack bound at current state *)
Theorem reach_stack_bound:
  !prog as.
    (!m as2. asm_steps (SND (compute_label_offsets prog))
                       (build_offset_to_pc prog) prog m as = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit) ==>
    LENGTH as.as_stack < stack_limit
Proof
  rw[] >>
  first_x_assum (qspecl_then [`0`, `as`] mp_tac) >>
  simp[asm_steps_def]
QED

(* Helper: reachability propagates through one AsmOK step *)
Theorem reach_propagate:
  !prog as as1.
    as.as_pc < LENGTH prog /\
    asm_step (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) (EL as.as_pc prog) as = AsmOK as1 /\
    (!m as2. asm_steps (SND (compute_label_offsets prog))
                       (build_offset_to_pc prog) prog m as = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit) ==>
    (!m as2. asm_steps (SND (compute_label_offsets prog))
                       (build_offset_to_pc prog) prog m as1 = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit)
Proof
  rw[] >>
  first_x_assum (qspecl_then [`SUC m`, `as2`] mp_tac) >>
  simp[asm_steps_def]
QED

Theorem asm_bytecode_sim_aux:
  !n prog as es.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    no_asm_calls prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    (!m as2. asm_steps (SND (compute_label_offsets prog))
                       (build_offset_to_pc prog)
                       prog m as = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit) /\
    (!i. i < LENGTH prog ==> 0 < asm_inst_size (EL i prog)) ==>
    (?es' exc. run es = SOME (INR (SOME exc), es') /\
               exc <> StackOverflow) \/
    ((!as'. asm_steps (SND (compute_label_offsets prog))
                      (build_offset_to_pc prog) prog n as = AsmHalt as' ==>
        ?es'. run es = SOME (INR NONE, es') /\
              asm_evm_rel prog as' es') /\
     (!as'. asm_steps (SND (compute_label_offsets prog))
                      (build_offset_to_pc prog) prog n as = AsmRevert as' ==>
        ?es'. run es = SOME (INR (SOME Reverted), es') /\
              asm_evm_rel prog as' es') /\
     (!as'. asm_steps (SND (compute_label_offsets prog))
                      (build_offset_to_pc prog) prog n as = AsmFault as' ==>
        ?es' exc. run es = SOME (INR (SOME exc), es') /\
                  exc <> Reverted /\
                  asm_evm_rel prog as' es'))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> DISJ2_TAC >> rw[asm_steps_def])
  >> rpt gen_tac >> strip_tac
  >> imp_res_tac reach_stack_bound
  >> Cases_on `as.as_pc >= LENGTH prog`
  >- (DISJ2_TAC >> simp[asm_steps_def])
  >> `as.as_pc < LENGTH prog` by decide_tac
  >> Cases_on `is_data_inst (EL as.as_pc prog)`
  >- (Cases_on `EL as.as_pc prog`
      >> fs[is_data_inst_def, asm_step_def, asm_steps_def])
  >> `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by
       (qpat_x_assum `!i. i < LENGTH prog /\ _ ==> _`
          (qspec_then `as.as_pc` mp_tac) >> simp[])
  >> drule_all asm_evm_step >> strip_tac
  (* EVM exception case *)
  >- (DISJ1_TAC >>
      imp_res_tac run_step_inr >>
      qexistsl_tac [`es1`, `exc`] >> simp[])
  (* Results correspond case *)
  >> Cases_on `asm_step (SND (compute_label_offsets prog))
                        (build_offset_to_pc prog)
                        (EL as.as_pc prog) as`
  >> fs[]
  (* AsmOK: apply IH *)
  >- (imp_res_tac run_step_inl >>
      mp_tac (Q.SPECL [`prog`, `as`, `a`] reach_propagate) >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`prog`, `a`, `es1`] mp_tac) >>
      simp[] >>
      (impl_tac >- (
        rpt conj_tac >> rw[] >> res_tac)) >>
      strip_tac
      >- (DISJ1_TAC >> metis_tac[])
      >> DISJ2_TAC >> simp[asm_steps_def])
  (* AsmHalt *)
  >- (DISJ2_TAC >> simp[asm_steps_def] >>
      imp_res_tac run_step_inr >> rw[] >> fs[])
  (* AsmRevert *)
  >- (DISJ2_TAC >> simp[asm_steps_def] >>
      imp_res_tac run_step_inr >> rw[] >> fs[])
  (* AsmFault *)
  >- (DISJ2_TAC >> simp[asm_steps_def] >>
      imp_res_tac run_step_inr >> rw[] >> fs[] >>
      qexistsl_tac [`es1`, `exc`] >> simp[])
  (* AsmError *)
  >> DISJ2_TAC >> simp[asm_steps_def]
QED
