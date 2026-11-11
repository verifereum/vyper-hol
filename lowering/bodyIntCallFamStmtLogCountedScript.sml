(* Counted, resource-preserving emission of an already evaluated ev. *)
Theory bodyIntCallFamStmtLogCounted
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogResource
  bodyIntCallFamStmtSimple stmtSimLogCompose stmtSimLogSource stmtSimLogArgs
  gasOutcome gasSummary fragGasMode vyperState vyperInterpreter
  loweringSlice venomInst venomState list

Theorem intcall_log_suffix_counted:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sm s /\
  sm.cs_next_var <= sb.cs_next_var /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  same_blocks sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
             (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce fp.jc_cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (SND arg) = SOME tv /\
         value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv fp.jc_cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs /\
  encode_source_event (get_tenv fp.jc_cx) fp.jc_cx.sources
    fp.jc_cx.txn.target id vs = SOME
    <|logger := w2w fp.jc_cx.txn.target; topics := n2w h::topics;
      data := enc (Tuple (vyper_to_abi_types (get_tenv fp.jc_cx)
        (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|> ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (lift_option (encode_source_event (get_tenv fp.jc_cx)
       fp.jc_cx.sources fp.jc_cx.txn.target id vs) "Log encode event") push_log)
    (es,s)
    (\res ee u. res = INL () /\
      intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      s.vs_alloca_next <= u.vs_alloca_next)
    (intcall_stmt_exit fp)
Proof
  strip_tac >>
  drule_all intcall_log_suffix_resource_run >> strip_tac >>
  drule_all intcall_resource_run_gas_path >> strip_tac >>
  qmatch_asmsub_abbrev_tac `encode_source_event _ _ _ _ _ = SOME ev` >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE (LENGTH (FILTER (\i. i.inst_opcode = GAS)
    (emitted_insts sm sb))) F` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es with logs := es.logs ++ [ev]`, `OK u`] >>
  conj_tac
  >- (irule gas_marked_exec_no_source_read >>
      simp[fragGasModeTheory.gas_marked_path_def] >>
      simp[bind_def, lift_option_def, push_log_def, return_def]) >>
  `intcall_joint_res fp ce env
     ((es with logs := es.logs ++ [ev]) with gas_obs := []) sb u` by
    (rewrite_tac[intcall_joint_res_gas_obs] >> metis_tac[]) >>
  gvs[lookup_var_def]
QED
