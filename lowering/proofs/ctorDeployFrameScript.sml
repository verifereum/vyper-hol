(* Creation-frame boundary: a run of the root-shadowed frame related to the
 * deployment unit's result gives the real creation frame's result
 * (shadow_root_run_halt/_exception and deploy_frame_complete).
 * TOP-LEVEL: deploy_venom_frame (a piece of e2e_deploy_correctness; admitted until proved),
 * deploy_frame_gas_sufficient (S7g-d, a piece of e2e_deploy_gas_sufficient), and its
 * program-free end, deploy_frame_gas_tail.
 *)
Theory ctorDeployFrame
Ancestors
  ctorDeployDefs deployFrameReplay codegenCorrectness e2eDeployFrame
  frameOutcome vfmRunCall vfmState passSimulationDefs e2eDeployDefs
  frameGas venomRunBounded ctorDeployCallFree o1OpcodeAbsence
  codegenAsmProgOk frameRunRaises frameStep ctorDeployEntry immutableSectionRel

(* Single-frame outcomes depend on the start state only through its one
   context's logs and the transaction parameters. *)
Theorem frame_outcome_single_transfer_none[local]:
  es.contexts = [(c0,rb0)] /\ mid.contexts = [(c1,rb1)] /\
  mid.txParams = es.txParams /\ c1.logs = c0.logs ++ lgs /\
  frame_outcome mid r es' NONE out [] ==>
  frame_outcome es r es' NONE out lgs
Proof
  rw[frame_outcome_def] >> gvs[]
QED

Theorem frame_resource_starved_single_transfer[local]:
  es.contexts = [(c0,rb0)] /\ mid.contexts = [(c1,rb1)] /\
  mid.txParams = es.txParams /\ frame_resource_starved mid r es' ==>
  frame_resource_starved es r es'
Proof
  rpt strip_tac >> gvs[frame_resource_starved_def, frame_outcome_def] >>
  metis_tac[]
QED

Theorem shadow_root_frame_outcome_exc[local]:
  es.contexts = [(c0,rb0)] /\
  frame_outcome (shadow_root es) r (shadow_root es') (SOME exc) out lgs ==>
  frame_outcome es r es' (SOME exc) out lgs'
Proof
  rpt strip_tac >>
  gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  Cases_on `es'.contexts` >> gvs[shadow_root_contexts_def] >>
  PairCases_on `h` >> Cases_on `t` >>
  gvs[shadow_root_contexts_def, shadow_root_contexts_nil]
QED

(* An exceptional shadow run is the real run, outcome included. *)
Theorem deploy_frame_exception[local]:
  es.contexts = [(c0,rb0)] /\
  run_call (shadow_root es) = SOME (r,g) /\
  frame_outcome (shadow_root es) r g (SOME exc) out lgs ==>
  ?es'. run_call es = SOME (r,es') /\
        !lgs'. frame_outcome es r es' (SOME exc) out lgs'
Proof
  strip_tac >>
  `LENGTH (shadow_root es).contexts = 1`
    by simp[shadow_root_def, shadow_root_contexts_def] >>
  `run (shadow_root es) = SOME (r,g)`
    by metis_tac[run_call_eq_run_single_context] >>
  `r = INR (SOME exc)`
    by gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  gvs[] >> drule shadow_root_run_exception >> strip_tac >>
  qexists_tac `es'` >> simp[run_call_eq_run_single_context] >>
  gen_tac >> irule shadow_root_frame_outcome_exc >> metis_tac[]
QED

(* A halting shadow run is the real run up to the root's halt handler. *)
Theorem deploy_frame_halt_mid[local]:
  es.contexts = [(c0,rb0)] /\
  run_call (shadow_root es) = SOME (r,g) /\
  frame_outcome (shadow_root es) r g NONE out lgs ==>
  ?mid ctxt rb.
    mid.contexts = [(ctxt,rb)] /\ mid.rollback = g.rollback /\
    ctxt.msgParams.outputTo = c0.msgParams.outputTo /\
    ctxt.returnData = out /\ ctxt.logs = c0.logs ++ lgs /\
    mid.txParams = es.txParams /\
    run_call es = SOME (handle_step NONE mid)
Proof
  strip_tac >>
  `LENGTH (shadow_root es).contexts = 1`
    by simp[shadow_root_def, shadow_root_contexts_def] >>
  `run (shadow_root es) = SOME (r,g)`
    by metis_tac[run_call_eq_run_single_context] >>
  `r = INR NONE`
    by gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  gvs[] >>
  `es.contexts <> []` by simp[] >>
  drule_all shadow_root_run_halt >> strip_tac >>
  qexistsl [`mid`,`ctxt`,`rb`] >>
  gvs[root_output_to_def, run_call_eq_run_single_context] >>
  gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def]
QED

Theorem deploy_venom_frame:
  !tops runtime_bc deploy_bc am tx es src res.
    deploy_state_rel tops deploy_bc am tx es /\
    runtime_bc <> [] /\ ~(?t. runtime_bc = 0xEFw :: t) /\
    deploy_venom_result_rel tops runtime_bc tx src res /\
    (?r g. run_call (shadow_root es) = SOME (r, g) /\
           (frame_resource_starved (shadow_root es) r g \/
            venom_frame_rel (shadow_root es) r g res))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       deploy_result_rel tops runtime_bc tx es r es' src)
Proof
  rpt strip_tac >>
  `?c0 rb0. es.contexts = [(c0,rb0)] /\
            c0.msgParams.outputTo = Code tx.target`
    by gvs[deploy_state_rel_def] >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` kall_tac
  >- (gvs[frame_resource_starved_def] >>
      drule_all deploy_frame_exception >> strip_tac >>
      first_assum (irule_at (Pos hd)) >>
      simp[frame_resource_starved_def] >> metis_tac[]) >>
  Cases_on `res` >> gvs[venom_frame_rel_def]
  >~ [`Halt ss`]
  >- (drule_all deploy_frame_halt_mid >> strip_tac >>
      Cases_on `src`
      >- (PairCases_on `x` >> gvs[deploy_venom_result_rel_def] >>
          qspecl_then [`mid`,`ctxt`,`rb`,`tx.target`] mp_tac
            deploy_frame_complete >>
          impl_tac >- (Cases_on `runtime_bc` >> gvs[]) >>
          strip_tac >> gvs[]
          >- (disj1_tac >> irule frame_resource_starved_single_transfer >>
              metis_tac[]) >>
          disj2_tac >> simp[deploy_result_rel_def] >>
          qexistsl [`section`,`ss.vs_logs`] >>
          gvs[lookup_account_def, update_account_def,
              combinTheory.APPLY_UPDATE_THM] >>
          irule frame_outcome_single_transfer_none >> metis_tac[]) >>
      Cases_on `y` >>
      gvs[deploy_venom_result_rel_def, deploy_result_rel_def] >>
      Cases_on `handle_step NONE mid` >> gvs[])
  >~ [`Abort ab vs'`]
  >- (Cases_on `src`
      >- (PairCases_on `x` >> Cases_on `ab` >>
          gvs[deploy_venom_result_rel_def]) >>
      Cases_on `ab` >> gvs[] >>
      drule_all deploy_frame_exception >> strip_tac >>
      first_assum (irule_at (Pos hd)) >>
      Cases_on `y` >>
      gvs[deploy_venom_result_rel_def, deploy_result_rel_def] >>
      metis_tac[]) >>
  drule deploy_venom_result_rel_terminates >> simp[terminates_def]
QED

(* ===== S7g-d helpers ===== *)

Theorem add_frame_gas_single_context[local]:
  (add_frame_gas g es).contexts = [x] ==> ?c rb. es.contexts = [(c, rb)]
Proof
  rw[add_frame_gas_def] >> BasicProvers.every_case_tac >> gvs[]
QED

Theorem shadow_root_add_frame_gas[local]:
  es.contexts = [(c, rb)] ==>
  shadow_root (add_frame_gas g es) = add_frame_gas g (shadow_root es)
Proof
  rw[shadow_root_def, add_frame_gas_def, shadow_root_contexts_def,
     vfmContextTheory.execution_state_component_equality] >>
  simp[vfmContextTheory.context_component_equality,
       vfmContextTheory.message_parameters_component_equality]
QED

(* A halting root-shadowed run that leaves gas for the largest deposit:
   the real frame's deposit fails with OutOfGas only when oversized. *)
Theorem deploy_frame_halt_deposit[local]:
  es.contexts = [(c0, rb0)] /\ c0.msgParams.outputTo = Code target /\
  run (shadow_root es) = SOME (INR NONE, es1) /\
  code_deposit_cost * max_code_size <= frame_gas_left es1 /\
  es1.contexts = [(c1, rb1)]
  ==>
  ?r es'. run_call es = SOME (r, es') /\
          (r = INR (SOME OutOfGas) ==> max_code_size < LENGTH c1.returnData)
Proof
  strip_tac >>
  `es.contexts <> []` by simp[] >>
  drule_all shadow_root_run_halt >> strip_tac >>
  `run_call es = run es` by (irule run_call_eq_run_single_context >> simp[]) >>
  gvs[root_output_to_def, shadow_root_def, shadow_root_contexts_def,
      frame_gas_left_def] >>
  Cases_on `handle_step NONE mid` >> simp[] >> strip_tac >>
  qspecl_then [`mid`, `ctxt`, `rb`, `target`] mp_tac
    deploy_handle_step_out_of_gas >>
  `0 < code_deposit_cost * max_code_size` by EVAL_TAC >>
  simp[]
QED

(* An exceptional end of the root-shadowed run other than OutOfGas: the
   real frame ends with the same exception. *)
Theorem deploy_frame_exc_end[local]:
  run (shadow_root es) = SOME (INR (SOME exc), ghost) /\ exc <> OutOfGas /\
  run_call es = run es ==>
  ?r es'. run_call es = SOME (r, es') /\ (r = INR (SOME OutOfGas) ==> P)
Proof
  strip_tac >> drule shadow_root_run_exception >> strip_tac >> gvs[]
QED

(* The creation frame's end, from its root-shadowed run: given the per-
   instruction surplus with the largest deposit's gas in reserve, the frame
   runs out of gas only when the code it deposits is oversized.  Nothing
   here names the program or the unit, so any codegen that gives the shadowed
   run's relation to the Venom result (codegen_correct or an optimised twin)
   can use it. *)
Theorem deploy_frame_gas_tail:
  !es ctxt rb tx tops runtime_bc src res r es'.
    es.contexts = [(ctxt, rb)] /\ ctxt.msgParams.outputTo = Code tx.target /\
    wf_state es /\
    (!s op r s'. frame_inst_at (shadow_root es) s op /\ step_inst op s = (r, s') /\
       LENGTH s'.contexts = LENGTH s.contexts ==>
       r <> INR (SOME OutOfGas) /\
       code_deposit_cost * max_code_size <= frame_gas_left s') /\
    run_call (shadow_root es) = SOME (r, es') /\
    (frame_resource_starved (shadow_root es) r es' \/
     venom_frame_rel (shadow_root es) r es' res) /\
    ~deploy_source_exempt tops src /\ deploy_venom_result_rel tops runtime_bc tx src res
    ==>
    ?r es'. run_call es = SOME (r, es') /\
      (r = INR (SOME OutOfGas) ==> max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `wf_state (shadow_root es)` by simp[shadow_root_wf_state] >>
  qabbrev_tac `sh = shadow_root es` >>
  `sh.contexts = [(ctxt with msgParams updated_by
                     (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>),
                   rb)]` by
    simp[Abbr `sh`, shadow_root_def, shadow_root_contexts_def] >>
  qspecl_then [`sh`, `ctxt with msgParams updated_by
                     (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>)`,
               `rb`, `r`, `es'`] mp_tac run_call_root_ends_at_inst >>
  impl_tac >- simp[] >> strip_tac >>
  `r <> INR (SOME OutOfGas)` by
    (strip_tac >> gvs[frame_inst_raises_def] >>
     first_x_assum drule >> disch_then drule >> gvs[frame_inst_at_def]) >>
  `run sh = SOME (r, es')` by
    (`run_call sh = run sh` by (irule run_call_eq_run_single_context >> simp[]) >>
     gvs[]) >>
  `run_call es = run es` by (irule run_call_eq_run_single_context >> simp[]) >>
  `!exc. r = INR (SOME exc) ==>
         ?r es'. run_call es = SOME (r, es') /\
                 (r = INR (SOME OutOfGas) ==>
                  max_code_size < LENGTH runtime_bc + imm_len tops)` by
    (rpt strip_tac >> qpat_x_assum `r = _` SUBST_ALL_TAC >>
     qspecl_then [`es`, `exc`, `es'`,
                  `max_code_size < LENGTH runtime_bc + imm_len tops`] mp_tac
       (Q.GENL [`es`, `exc`, `ghost`, `P`] deploy_frame_exc_end) >>
     impl_tac
     >- (rpt conj_tac
         >- (qpat_x_assum `run sh = _` mp_tac >> simp[Abbr `sh`])
         >- (qpat_x_assum `INR (SOME exc) <> _` mp_tac >> simp[]) >>
         first_assum ACCEPT_TAC) >>
     simp[]) >>
  (* a starved run ends in an exception *)
  Cases_on `frame_resource_starved sh r es'`
  >- (`?exc. r = INR (SOME exc)` by gvs[frame_resource_starved_def, frame_outcome_def] >>
      qpat_x_assum `!exc. r = _ ==> _` (drule_then ACCEPT_TAC)) >>
  drule deploy_venom_result_rel_terminates >> strip_tac >>
  Cases_on `res` >> gvs[terminates_def]
  >~ [`Halt ss`]
  >- (gvs[venom_frame_rel_def, frame_outcome_def] >>
      Cases_on `src` >> gvs[deploy_source_exempt_def]
      >- (PairCases_on `x` >> gvs[deploy_venom_result_rel_def] >>
          drule immutables_section_rel_length >> strip_tac >>
          rename1 `es'.contexts = [(c1, rb1)]` >>
          `LENGTH s.contexts = 1` by
            (qpat_x_assum `frame_inst_at _ s op` mp_tac >>
             qpat_x_assum `sh.contexts = _` mp_tac >>
             simp[frame_inst_at_def] >> rpt strip_tac >> gvs[]) >>
          `code_deposit_cost * max_code_size <= frame_gas_left es'` by
            (qpat_x_assum `!s op r s'. frame_inst_at sh _ _ /\ _ ==> _`
               (qspecl_then [`s`, `op`, `INR NONE`, `es'`] mp_tac) >>
             impl_tac >- fs[] >> simp[]) >>
          qspecl_then [`es`, `ctxt`, `rb`, `tx.target`, `es'`, `c1`, `rb1`] mp_tac
            (Q.GENL [`es`, `c0`, `rb0`, `target`, `es1`, `c1`, `rb1`]
               deploy_frame_halt_deposit) >>
          impl_tac >- fs[Abbr `sh`] >> simp[imm_len_def]) >>
      Cases_on `y` >> gvs[deploy_venom_result_rel_def])
  (* an aborted run ends in an exception *)
  >~ [`Abort ab ss`]
  >- (`?exc. r = INR (SOME exc)` by
        (Cases_on `ab` >> gvs[venom_frame_rel_def, frame_outcome_def]) >>
      qpat_x_assum `!exc. r = _ ==> _` (drule_then ACCEPT_TAC)) >>
  gvs[venom_frame_rel_def]
QED

(* PLANNED ADMISSION S7g-d, sufficient gas for deployment: the deploy-side
   counterpart of codegen_gas_sufficient together with deploy_venom_frame.
   Given the constructor unit's resource bound, some gas g, independent of
   the creation frame, is enough: with g' >= g more gas, the creation frame
   ends in OutOfGas only when the code it deposits, runtime_bc and the
   immutables section, is longer than max_code_size, which handle_create
   rejects with OutOfGas at any gas.  No RETURNDATACOPY exemption: the
   constructor makes no calls.  The last premise says what the constructor
   returns, so the deposit's length is LENGTH runtime_bc + imm_len tops.
   Proof idea: S7g's per-instruction argument on the root-shadowed frame
   codegen runs (shadow_root), with no RETURNDATACOPY run, plus the
   deposit, which costs at most code_deposit_cost * max_code_size.
   wf_state es keeps the frame's own gas use within its limit: otherwise the
   gassed frame could start with no gas left.  deploy_typing_ok fixes each
   builtin's argument count, which the call-free lowering needs. *)
Theorem deploy_frame_gas_sufficient:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan fuel M.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    unit_shape_ok dout.po_unit /\
    constructor_call_free tops
    ==>
    ?g. !g' am tx es Inv.
      g <= g' /\ wf_state es /\ deploy_typing_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx (add_frame_gas g' es) /\
      LENGTH (FST (HD (add_frame_gas g' es).contexts)).msgParams.code
        <= dimword(:256) DIV 2 /\
      codegen_context_obligations Inv dout.po_unit.cu_context cplan /\
      codegen_reachability_package Inv dout.po_unit.cu_context
        (deploy_entry_state prog cplan tops (add_frame_gas g' es)) /\
      venom_run_bounded fuel M dout.po_unit.cu_context
        (deploy_entry_state prog cplan tops (add_frame_gas g' es)) /\
      (?src vfuel.
         ~deploy_source_exempt tops src /\
         deploy_venom_result_rel tops runtime_bc tx src
           (run_context vfuel dout.po_unit.cu_context
              (deploy_entry_state prog cplan tops (add_frame_gas g' es))))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  (* S7g's surplus, with the largest deposit's gas in reserve *)
  qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `fuel`, `M`,
               `code_deposit_cost * max_code_size`] mp_tac codegen_gas_surplus >>
  impl_tac >- fs[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* no RETURNDATACOPY anywhere in the creation code *)
  drule_all lower_vyper_deploy_unit_call_free_entry >> strip_tac >>
  `!fn inst. MEM fn dout.po_unit.cu_context.ctx_functions /\
             MEM inst (fn_insts fn) ==> inst.inst_opcode <> RETURNDATACOPY` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`rpolicy`, `dunit`, `dout`, `efn`] mp_tac
       o1_pipeline_leaf_entry_no_returndatacopy >>
     impl_tac >- fs[] >> disch_then drule_all >> simp[]) >>
  drule_all codegen_assembly_no_returndatacopy >> strip_tac >>
  `?c0 rb0. es.contexts = [(c0, rb0)]` by
    (fs[deploy_state_rel_def] >> metis_tac[add_frame_gas_single_context]) >>
  drule shadow_root_add_frame_gas >> disch_then (qspec_then `g'` assume_tac) >>
  `?ctxt rb. (add_frame_gas g' es).contexts = [(ctxt, rb)] /\
             ctxt.msgParams.outputTo = Code tx.target /\
             wf_state (add_frame_gas g' es)` by fs[deploy_state_rel_def] >>
  `wf_state (shadow_root (add_frame_gas g' es))` by simp[shadow_root_wf_state] >>
  `g' <= frame_gas_left (shadow_root (add_frame_gas g' es))` by
    metis_tac[wf_state_frame_gas_left, shadow_root_wf_state] >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  qabbrev_tac `vs = deploy_entry_state prog cplan tops (add_frame_gas g' es)` >>
  qabbrev_tac `sh = shadow_root (add_frame_gas g' es)` >>
  `!t. ~frame_inst_at sh t ReturnDataCopy` by
    (gen_tac >>
     qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `fuel`, `M`,
                  `Inv`, `vs`, `sh`, `t`] mp_tac codegen_no_returndatacopy >>
     impl_tac >- fs[] >> simp[]) >>
  `!s op r s'. frame_inst_at sh s op /\ step_inst op s = (r, s') /\
               LENGTH s'.contexts = LENGTH s.contexts ==>
               r <> INR (SOME OutOfGas) /\
               code_deposit_cost * max_code_size <= frame_gas_left s'` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!g' Inv vs es s op r s'. _`
       (qspecl_then [`g'`, `Inv`, `vs`, `shadow_root es`, `s`, `op`, `r`, `s'`]
          mp_tac) >>
     qpat_x_assum `sh = add_frame_gas _ _` (assume_tac o GSYM) >>
     impl_tac >- fs[] >> simp[]) >>
  (* the shadowed frame's run, and how it ends *)
  qspecl_then [`vfuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `Inv`,
               `vs`, `sh`] mp_tac codegen_correct >>
  impl_tac >- fs[] >>
  disch_then (qx_choosel_then [`r`, `es'`]
                (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qpat_x_assum `sh = add_frame_gas _ _` kall_tac >>
  qspecl_then [`add_frame_gas g' es`, `ctxt`, `rb`, `tx`, `tops`, `runtime_bc`,
               `src`, `run_context vfuel dout.po_unit.cu_context vs`,
               `r`, `es'`] mp_tac deploy_frame_gas_tail >>
  impl_tac >- (fs[Abbr `sh`] >> first_assum ACCEPT_TAC) >> simp[]
QED
