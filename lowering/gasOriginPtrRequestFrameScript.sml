(* A normal prefix without an INVOKE or a new request is independent of the
   dead mask. Preserve its exact gas marks and pointer ghosts. *)
Theory gasOriginPtrRequestFrame
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec gasEvents
  ptrSafeRun dftGasRequestObservation venomExecProofs venomExecSemantics
  venomState rich_list

Theorem gas_origin_ptr_edge_requests[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) marks (OK t,G',tn') /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==> inst.inst_opcode <> INVOKE) ==>
  s.vs_requests <<= t.vs_requests /\
  (s.vs_requests = t.vs_requests ==>
   !D'. gas_origin_ptr_edge (D',lo,explicit,ctx,fn,PG)
     (s,G,tn) marks (OK t,G',tn'))
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o MATCH_MP gas_origin_ptr_edge_common_fuel) assume_tac) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fuel`,`bb`,`inst`,`middle`]
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  `?v. middle = OK v /\ v.vs_requests = t.vs_requests` by
    (qpat_x_assum `(?v. _) \/ _` mp_tac >>
     strip_tac >> gvs[exit_result_def] >>
     TRY (qpat_assum `eval_phis _ _ = OK _`
       (mp_tac o Q.AP_TERM `\u. u.vs_requests` o
        MATCH_MP eval_phis_only_updates_vs_vars) >> simp[]) >>
     metis_tac[]) >>
  `s.vs_requests <<= t.vs_requests` by metis_tac[step_inst_requests_prefix] >>
  simp[] >> strip_tac >> gen_tac >>
  `ptr_safe_step D' lo fuel ctx fn PG G tn inst s` by
    (qpat_x_assum `ptr_safe_step D lo fuel ctx fn PG G tn inst s` mp_tac >>
     asm_simp_tac (srw_ss()) [ptr_safe_defs, ptr_inst_ok_def]) >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `fuel` >>
  fs[gas_events_length] >> metis_tac[]
QED

Theorem gas_origin_ptr_path_requests:
  !config start marks out.
    gas_origin_ptr_path config start marks out ==>
    !D lo explicit ctx fn PG s G tn t G' tn' inside.
      config = (D,lo,explicit,ctx,fn,PG) /\
      start = (s,G,tn) /\ out = (OK t,G',tn') /\ inside s /\
      (!u bb inst. inside u /\
        lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME inst ==> inst.inst_opcode <> INVOKE) /\
      (!u Gu tnu m v Gv tnv. inside u /\
        gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
          (u,Gu,tnu) m (OK v,Gv,tnv) ==> inside v) ==>
      s.vs_requests <<= t.vs_requests /\
      (s.vs_requests = t.vs_requests ==>
       !D'. gas_origin_ptr_path (D',lo,explicit,ctx,fn,PG)
         (s,G,tn) marks (OK t,G',tn'))
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[exit_result_def]
  >- simp[gas_origin_ptr_path_rules] >>
  `inside mid` by metis_tac[] >>
  drule gas_origin_ptr_edge_requests >> impl_tac >- metis_tac[] >> strip_tac >>
  qpat_assum `!Q. _ ==> mid.vs_requests <<= t.vs_requests /\ _`
    (qspec_then `inside` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- metis_tac[IS_PREFIX_TRANS] >>
  strip_tac >>
  `s.vs_requests = mid.vs_requests /\ mid.vs_requests = t.vs_requests` by
    metis_tac[IS_PREFIX_ANTISYM] >>
  metis_tac[gas_origin_ptr_path_rules]
QED
