Theory bodyPtrPrecompileBuiltinsSuffix
Ancestors bodyPtrPrecompileBuiltinsBoundary fragGasSeqPtr
          emitHelperProps ptrSafeRun ptrDiscipline venomInstProofs
          venomExecSemantics venomInst venomState finite_map
          contextCodegenRel codegenRel memLocDefs exprSimHash
          decoderGhostFramePtr exprLoweringProps ghostPcTransportPtr venomMemProps
          instIdxIndep exprSimPrecompiles venomCallOracleDefs

Theorem gas_ptr_inst_ok:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id GAS [] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mem_read_ops_def, mem_write_ops_def, step_inst_non_invoke, step_GAS,
       update_var_def]
QED

Theorem gas_output_taint:
  op_taint (step_taint (mk_inst id GAS [] [out]) s t tn) (Var out) = {}
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem gas_ptr_covers:
  p <> out /\ ptr_covers G tn p s sz /\
  step_inst_base (mk_inst id GAS [] [out]) s = OK t ==>
  ptr_covers (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn) p t sz
Proof
  strip_tac >> irule ptr_covers_step_frame >> simp[mk_inst_def] >>
  gvs[step_GAS, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem assert_ptr_inst_ok:
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ op_taint tn op = {} ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mem_read_ops_def, mem_write_ops_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs] >>
  Cases_on `eval_operand op s` >> simp[] >>
  rename1 `eval_operand op s = SOME w` >> Cases_on `w = 0w` >> simp[]
QED

Theorem staticcall_ptr_inst_ok:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] /\
  ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s (w2n rn) /\
  op_taint tn gp = {} /\ eval_operand (Var src) s = SOME ai /\
  (!i. w2n ai <= i /\ i < w2n ai + w2n an ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  (!t. step_inst_base inst s <> Halt t) ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok lo G fn inst s` by
    (gvs[] >> irule staticcall_access_ok >> qexists_tac `tn` >> simp[]) >>
  `taint_ok fn tn inst s` by
    (gvs[] >> irule staticcall_taint_ok >>
     gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  simp[ptr_inst_ok_def] >>
  gvs[mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem gas_step_taint:
  step_inst_base (mk_inst id GAS [] [out]) s = OK t ==>
  step_taint (mk_inst id GAS [] [out]) s t tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> gvs[step_GAS] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, range_bytes_def,
       source_memory_write_ranges_def, set_var_taint_def, out_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       mk_inst_def, update_var_def] >>
  simp[finite_mapTheory.FLOOKUP_DEF, taint_component_equality,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem assert_step_ghost:
  step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
  step_taint (mk_inst id ASSERT [op] []) s s tn = tn
Proof
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
       DRESTRICT_UNIV, FLOOKUP_DEF, taint_component_equality,
       pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

(* Success of the GAS/STATICCALL prefix supplies the intermediate states.
   ASSERT is checked for either outcome, so the same boundary covers normal
   return and failed-call reversion. Checks are not inferred from erasure. *)
Theorem suffix_checked:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s (w2n rn) /\
  eval_operand (Var src) s = SOME wi /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  run_inst_seq [gi;ci] s = OK t ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s G' tn'
Proof
  strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  rename1 `step_inst_base (mk_inst id GAS [] [gv]) s = OK u` >>
  rename1 `step_inst_base (mk_inst (id+1) STATICCALL _ _) u = OK v` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id GAS [] [gv]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id GAS [] [gv]) s u tn` >>
  qabbrev_tac `ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv]` >>
  `ptr_inst_ok D lo 0 ctx fn G1 tn1 ci
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    suspend "call_check" >>
  `ptr_inst_ok D lo 0 ctx fn (step_prov PG G1 ci v)
      (step_taint ci u v tn1) (mk_inst (id+2) ASSERT [Var cv] [])
      (v with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    suspend "assert_check" >>
  suspend "sequence"
QED

Resume suffix_checked[call_check]:
  `ptr_covers G1 tn1 src u (w2n an) /\
   ptr_covers G1 tn1 dst u (w2n rn)` by
    (simp[Abbr `G1`, Abbr `tn1`] >> metis_tac[gas_ptr_covers]) >>
  simp[Abbr `ci`] >> irule staticcall_ptr_inst_ok >>
  (conj_tac >-
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, mk_inst_def,
         is_terminator_def, exec_result_map_def]) >>
  drule gas_step_taint >>
  simp[Abbr `tn1`] >> strip_tac >>
  gvs[step_GAS, allocas_from_def, update_var_def,
      mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
      eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Resume suffix_checked[assert_check]:
  `v.vs_allocas = u.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> qexists_tac `ci` >>
     simp[Abbr `ci`, mk_inst_def]) >>
  irule assert_ptr_inst_ok >>
  simp[Abbr `ci`] >> conj_tac
  >- (irule staticcall_output_taint >> simp[mk_inst_def]) >>
  gvs[step_GAS, allocas_from_def, update_var_def] >> metis_tac[]
QED

Resume suffix_checked[sequence]:
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id GAS [] [gv]) s` by
    (irule gas_ptr_inst_ok >> simp[]) >>
  `~is_terminator ci.inst_opcode` by
    simp[Abbr `ci`, mk_inst_def, is_terminator_def] >>
  `~is_terminator (mk_inst (id+2) ASSERT [Var cv] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       Abbr `G1`, Abbr `tn1`] >>
  Cases_on `step_inst_base (mk_inst (id+2) ASSERT [Var cv] []) v` >>
  simp[exec_result_map_def]
QED

Finalise suffix_checked


