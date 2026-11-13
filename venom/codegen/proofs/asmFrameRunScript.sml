(*
 * The assembly run from a related state against the frame's run_call,
 * by induction on the assembly's step count.
 *
 * TOP-LEVEL:
 *   asm_frame_step - every instruction, from the two step classes
 *   asm_frame_run  - codegen_asm_run_call's clauses from asm_frame_rel
 *)

Theory asmFrameRun
Ancestors
  asmFrameRel asmFrameLocalStep asmFrameCallStep asmFrameCreateStep
  asmFrameDelegateStep asmFrameSelfdestructStep asmSem asmWf symbolResolve
  frameOutcome callTrace vfmExecution

(* Preserve the local-step interface while dispatching stateful frame steps. *)
Theorem asm_frame_local_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\
  EL as.as_pc prog <> AsmOp "STATICCALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "DELEGATECALL"`
  >- (irule asm_frame_delegate_step >> simp[]) >>
  Cases_on `EL as.as_pc prog = AsmOp "CREATE" \/
            EL as.as_pc prog = AsmOp "CREATE2"`
  >- (irule asm_frame_create_step >> simp[]) >>
  Cases_on `EL as.as_pc prog = AsmOp "SELFDESTRUCT"`
  >- (irule asm_frame_selfdestruct_step >> simp[]) >>
  irule asm_frame_noncall_step >> simp[] >> metis_tac[]
QED

Theorem asm_frame_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) ==>
  asm_frame_step_ok prog data es0 as es
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "CALL" \/
            EL as.as_pc prog = AsmOp "STATICCALL"`
  >- (irule asm_frame_call_step >> simp[]) >>
  irule asm_frame_local_step >> fs[]
QED

Theorem asm_frame_run:
  !n prog data es0 as es r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
    run_call es = SOME (r, es') ==>
    frame_resource_starved es0 r es' \/
    ((!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmHalt as' ==>
        frame_outcome es0 r es' NONE as'.as_returndata as'.as_logs /\
        es'.rollback.accounts = as'.as_accounts /\
        es'.rollback.toDelete = as'.as_pending_deletions /\
        es'.rollback.tStorage = as'.as_transient /\
        as'.as_requests = call_requests es0) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmRevert as' ==>
        ?lgs. frame_outcome es0 r es' (SOME Reverted) as'.as_returndata lgs) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmFault as' ==>
        ?exc lgs. exc <> Reverted /\ frame_outcome es0 r es' (SOME exc) [] lgs))
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `as.as_pc < LENGTH prog`) >- simp[asm_steps_def] >>
  Cases_on `is_data_inst (EL as.as_pc prog)`
  >- (Cases_on `EL as.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def, asm_steps_def]) >>
  `asm_frame_step_ok prog data es0 as es` by (irule asm_frame_step >> simp[]) >>
  pop_assum mp_tac >> simp[asm_frame_step_ok_def] >> strip_tac
  >- gvs[] >>
  simp[asm_steps_def] >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              (EL as.as_pc prog) as` >> gvs[]
  >~ [`AsmOK as1`]
  >- (first_x_assum (qspecl_then [`prog`, `data`, `es0`, `as1`, `es1`, `r`, `es'`]
        mp_tac) >> simp[]) >>
  DISJ2_TAC >> metis_tac[]
QED
