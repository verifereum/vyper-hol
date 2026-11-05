(* Creation-frame completion after the initcode has returned its bytes.
   TOP-LEVEL: deploy_frame_complete.
   This hook does not establish reachability of that return state. *)
Theory e2eDeployFrame
Ancestors
  frameOutcome vfmExecution vfmState list words

Theorem deploy_exception_none[local]:
  s.contexts = [(c,rb)] ==>
  handle_exception NONE s = (INR NONE,s)
Proof
  simp[handle_exception_def, get_num_contexts_def, bind_def,
       return_def, reraise_def]
QED

Theorem deploy_exception_out_of_gas[local]:
  s.contexts = [(c,rb)] /\
  t.contexts = [(d,rb')] /\ t.txParams = s.txParams /\
  handle_exception (SOME OutOfGas) t = (r,u) ==>
  frame_resource_starved s r u
Proof
  strip_tac >>
  gvs[handle_exception_def, get_gas_left_def, bind_def,
      ignore_bind_def, get_current_context_def, return_def,
      consume_gas_def, set_current_context_def, assert_def] >>
  Cases_on `d.msgParams.gasLimit - d.gasUsed + d.gasUsed <=
            d.msgParams.gasLimit` >>
  gvs[set_return_data_def, bind_def, get_current_context_def,
      return_def, set_current_context_def, get_num_contexts_def,
      reraise_def, frame_resource_starved_def, frame_outcome_def]
QED

Theorem deploy_create[local]:
  s.contexts = [(c,rb)] /\
  c.msgParams.outputTo = Code target /\
  (case c.returnData of h::_ => h <> n2w 0xef | [] => T) ==>
  let g = code_deposit_cost * LENGTH c.returnData;
      sg = s with contexts := [(c with gasUsed := c.gasUsed + g,rb)];
      sa = sg with rollback := (s.rollback with accounts :=
        update_account target
          (lookup_account target s.rollback.accounts with code := c.returnData)
          s.rollback.accounts)
  in handle_create NONE s =
    if c.gasUsed + g <= c.msgParams.gasLimit then
      if LENGTH c.returnData <= max_code_size then ((INR NONE : unit + exception option),sa)
      else (INR (SOME OutOfGas),sg)
    else (INR (SOME OutOfGas),s)
Proof
  strip_tac >>
  simp[handle_create_def, get_return_data_def, get_output_to_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       assert_def, consume_gas_def, set_current_context_def] >>
  Cases_on `c.gasUsed + code_deposit_cost * LENGTH c.returnData <=
            c.msgParams.gasLimit` >>
  simp[bind_def, ignore_bind_def, return_def, update_accounts_def,
       reraise_def] >>
  Cases_on `LENGTH c.returnData <= max_code_size` >> simp[] >>
  simp[vfmContextTheory.execution_state_component_equality,
       vfmContextTheory.rollback_state_component_equality]
QED

(* Gas deposit and the runtime size limit can fail with OutOfGas, already
   covered by frame_resource_starved. The prefix guard concerns all returned
   bytes, including the immutable suffix. No gas or size bound is assumed. *)
Theorem deploy_frame_complete:
  !es ctxt rb target.
    es.contexts = [(ctxt, rb)] /\
    ctxt.msgParams.outputTo = Code target /\
    (case ctxt.returnData of h::_ => h <> n2w 0xef | [] => T) ==>
    ?r es'.
      handle_step NONE es = (r, es') /\
      (frame_resource_starved es r es' \/
       (frame_outcome es r es' NONE ctxt.returnData [] /\
        es'.rollback.accounts =
          update_account target
            (lookup_account target es.rollback.accounts with code := ctxt.returnData)
            es.rollback.accounts /\
        es'.rollback.tStorage = es.rollback.tStorage /\
        es'.rollback.toDelete = es.rollback.toDelete))
Proof
  rpt strip_tac >>
  drule_all deploy_create >> simp[] >> strip_tac >>
  simp[handle_step_def, vfm_abort_def, handle_def] >>
  reverse (Cases_on `ctxt.gasUsed + code_deposit_cost * LENGTH ctxt.returnData <=
            ctxt.msgParams.gasLimit`)
  >- (gvs[] >>
      Cases_on `handle_exception (SOME OutOfGas) es` >> asm_rewrite_tac[] >>
      simp[] >>
      disj1_tac >> irule deploy_exception_out_of_gas >>
      metis_tac[]) >>
  Cases_on `LENGTH ctxt.returnData <= max_code_size`
  >- (gvs[] >>
      simp[deploy_exception_none, frame_outcome_def] >>
      disj2_tac >> simp[] >> metis_tac[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `handle_exception (SOME OutOfGas) charged` >>
  Cases_on `handle_exception (SOME OutOfGas) charged` >> gvs[] >>
  disj1_tac >> irule deploy_exception_out_of_gas >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[Abbr `charged`]
QED
