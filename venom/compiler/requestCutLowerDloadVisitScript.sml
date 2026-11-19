Theory requestCutLowerDloadVisit
Ancestors
  requestCutDloadOperands loweringBudgetFrameOracleTransport
  requestCutReplayProofs requestCutOracleReplay e2eRequestCutDefs
  lowerDloadExternalInputs lowerDloadNormalData lowerDloadCoverageInvariant
  lowerDloadSharedState lowerDloadResidualNonmemory lowerDloadRequestObservation
  o1PassContract contextCodegenRel
  venomExecSemantics venomWf venomState list rich_list

(* Recover the actual request from a boundary reached with a clipped oracle.
   Clipping preserves operands and memory, but only the full steps record k. *)
Theorem request_cut_lower_dload_visit:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  ld_annotated_reachable clip0 CS astk j L AP AG tn fn i
    (s with vs_outcomes := []) /\
  ptr_discipline lo CS clip0 /\ o1_ctx_shape CS /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un
    (s with vs_outcomes := []) (t with vs_outcomes := [])
    astk live keys d A suspended gstk f /\
  LENGTH s.vs_requests = k /\ LENGTH t.vs_requests = k /\
  s.vs_outcomes = t.vs_outcomes /\ i.inst_opcode <> INVOKE /\
  step_inst fuel CT i t = OK t' /\ k < LENGTH t'.vs_requests ==>
  ?s'. step_inst fuel CS i s = OK s' /\ k < LENGTH s'.vs_requests /\
    (tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
     tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address) ==>
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests))
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all lowerDloadRequestObservationTheory.ld_request_growth_external >>
  strip_tac >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  Q.SUBGOAL_THEN `?g a v off sz ro rs salt scalars.
     (i.inst_opcode = CALL /\ i.inst_operands = [g;a;v;off;sz;ro;rs] /\
        scalars = [g;a;v;sz;rs]) \/
     (MEM i.inst_opcode [STATICCALL;DELEGATECALL] /\
        i.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz;rs]) \/
     (i.inst_opcode = CREATE /\ i.inst_operands = [v;off;sz] /\ scalars = [v;sz]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [v;off;sz;salt] /\
        scalars = [v;sz;salt])`
    (qx_choosel_then [`g`,`a`,`v`,`off`,`sz`,`ro`,`rs`,`salt`,`scalars`] assume_tac)
  >-
    (qpat_assum `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
       (strip_assume_tac o REWRITE_RULE [MEM]) >>
     fs[MEM,inst_wf_def,LENGTH_EQ_NUM_compute] >>
     metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> ?w.
     eval_operand op (t with vs_outcomes := []) = SOME w` by
    (simp_tac bool_ss [operand_outcomes_update] >>
     qpat_assum `step_inst fuel CT i t = OK t'` (fn step =>
       qpat_assum `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
         (fn opcode => ACCEPT_TAC
           (MATCH_MP ld_external_target_operands_defined (CONJ opcode step))))) >>
  `~in_revert_forward fn (s with vs_outcomes := [])` by
    fs[in_revert_forward_def, revert_forward_at_def] >>
  drule_all ld_normal_external_inputs_defined >> simp[] >> strip_tac >>
  `s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (drule ld_normal_data_frame >>
     simp[ld_frame_data_def, ld_shared_state_def]) >>
  `?s'. step_inst fuel CS i s = OK s'` by
    (irule request_step_relocated_backward >>
     qpat_x_assum `(i.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >>
     gvs[MEM] >> metis_tac[]) >>
  `k < LENGTH s'.vs_requests` by metis_tac[external_ok_records_request, DECIDE ``k < SUC k``] >>
  qexists_tac `s'` >> simp[] >> strip_tac >>
  irule relocated_request_agrees >> simp[] >> conj_tac
  >- (qabbrev_tac `shell_scalars = if MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL]
        then TAKE (PRE (LENGTH scalars)) scalars else scalars` >>
      irule request_step_relocated_shell >>
      qexistsl_tac [`CS`,`CT`,`a`,`fuel`,`fuel`,`g`,`i`,`n`,`off`,`p`,`q`,`ro`,
        `rs`,`s`,`salt`,`shell_scalars`,`sz`,`t`,`v`] >>
      qpat_assum `(i.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >>
      gvs[MEM,read_memory_def,Abbr `shell_scalars`,DISJ_IMP_THM,FORALL_AND_THM]) >>
  qexistsl_tac [`CS`,`CT`,`fuel`,`fuel`,`i`,`i`,`s`,`t`,`tn`,`tn`] >>
  simp[] >>
  qpat_assum `ld_normal_data CS fn V U lo E L H AP BP AG BH tn un _ _ astk live keys d A suspended gstk f`
    (ACCEPT_TAC o MATCH_MP ld_clipped_normal_shared_store)
QED
