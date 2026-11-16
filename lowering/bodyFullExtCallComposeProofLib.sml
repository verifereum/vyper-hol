(* Consumer procedure, parameterized by the exact Request proposition.
   The validation theory supplies an ordinary local hypothesis; canonical
   Compose supplies the actual Request export. No producer is loaded here. *)
structure bodyFullExtCallComposeProofLib =
struct
open HolKernel boolLib bossLib
open bodySimFullTheory bodyInvNoDallocaTheory exprSimSourceTheory
open gasOutcomeFullTheory exprSimDefsTheory
open bodyFullExtCallStepTheory bodyFullExtCallReturnTheory
open vyperInterpreterTheory vyperASTTheory exprSimExtCallCaseTheory

fun compose_tac request =
  rpt gen_tac >> PairCases_on `sig` >> strip_tac >> gvs[] >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `!st st'. eval_expr cx
      (Call ann (ExtCall is_static' skip (sig0,sig1,sig2) opts) args dflt) st <>
      (INR HaltException, st')` by
    (rpt gen_tac >> irule eval_expr_calls_no_halt >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  rw[expr_vv_sim_full_def] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ source _ post _` >>
  qsuff_tac `gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (es,s0,G0,tn0) post
    (\H res ee gt r. expr_exit res r)`
  >- (simp[gas_outcome_full_def] >> strip_tac >> qexists_tac `marks` >>
      fs[Abbr `source`] >> metis_tac[halt_exit_def]) >>
  unabbrev_all_tac >>
  irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM] request)

val request_finish_tac =
  simp[] >> conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`cenv`, `d`, `env`, `sa`, `sb`, `shadow_func`,
    `shadow_sa`, `shadow_sb`, `tops`, `ty`, `vv`] >>
  simp[] >> rpt strip_tac

val source_tac =
  simp[eval_ext_call_def, vyperStateTheory.type_check_def,
       vyperStateTheory.lift_option_type_def] >>
  simp[vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_return] >>
  `!err. vyperState$assert T err = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  simp[vyperStateTheory.bind_return] >>
  `is_static' <=>
    (if is_static' then NONE else
      case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
        NONE => SOME 0 | SOME v => dest_NumV v) = NONE` by
    metis_tac[extcall_request_ready_def] >>
  `(if is_static' then return NONE else
     case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
       NONE => return (SOME 0)
     | SOME v => bind (case dest_NumV v of
          NONE => raise (Error (TypeError "ExtCall value not int"))
        | SOME n => return n) (\n. return (SOME n))) =
    return (if is_static' then NONE else
     case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
       NONE => SOME 0 | SOME v => dest_NumV v)` by
    (Cases_on `is_static'` >- simp[] >>
     Cases_on `ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest)`
     >- simp[] >> rename1 `SOME v` >>
     Cases_on `dest_NumV v` >> gvs[vyperStateTheory.bind_return]) >>
  simp[vyperStateTheory.bind_return]

val call_tac =
  qmatch_goalsub_abbrev_tac `bind (eval_ext_call_effects cx target calldata _ _ _) kont` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ post _` >>
  irule (SIMP_RULE (srw_ss()) [vyperStateTheory.ignore_bind_def, ETA_THM]
    extcall_call_full_default_frame)

val call_finish_tac =
  simp[] >> conj_tac
  >- (gen_tac >> simp[Abbr `kont`] >>
      Cases_on `if returnData = [] then
        ext_call_kwarg EKDefault opts (DROP (LENGTH sig1) rest) else NONE` >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.storage_trace_frame_lifts,
           vyperStorageTraceTheory.storage_trace_frame_return,
           vyperStorageTraceTheory.storage_trace_frame_state_reads,
           vyperStorageTraceTheory.storage_trace_frame_checks]) >>
  qexistsl [`G0`, `addr_op`, `buf_op`, `call_len`, `call_offset`,
    `abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap sig2 then TupleT [sig2] else sig2)`,
    `cenv`, `d`, `default_op`,
    `ext_call_kwarg EKDefault opts (DROP (LENGTH sig1) rest)`, `default_ty`,
    `es`, `gas_op`, `has_default`, `is_static'`, `s0`, `sa`, `sp`, `sr`,
    `tn0`, `u`, `value_op`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  unabbrev_all_tac >> rpt strip_tac >> simp[]

val return_tac =
  irule (SIMP_RULE (srw_ss()) [vyperStateTheory.ignore_bind_def,
    loweringPostsTheory.post_value_type_def, arithmeticTheory.ADD_COMM, ETA_THM]
    extcall_return_full)

val return_finish_tac =
  simp[] >> conj_tac >- metis_tac[] >>
  qexistsl [`addr_op`, `buf_op`, `default_op`, `default_ty`, `has_default`, `sr`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!dv. _ ==> ptr_mem_ok _ _ _ _ G tn t /\ _`
    (qspec_then `dv` mp_tac) >>
  qpat_x_assum `!dv. _ ==> ptr_mem_ok _ _ _ _ G' tn' t' /\ _`
    (qspec_then `dv` mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
end
