(* A failing calldata slice stops at the shared scalar bounds endpoint. *)
Theory bodyFullBuiltinBytestringCalldataAbort
Ancestors
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringAbort
  bodyPtrBytestringBuiltinsExternalSlice exprSimCalldataSlice
  bodyPtrBytestringBuiltinsBounds fragGasOriginPtr fragExec
  emitHelper emitHelperProps freshWrites compileEnv loweringStateRelDefs
  ptrDiscipline venomExecSemantics venomState venomInst words list finite_map

Theorem bytestring_calldata_full_abort:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a < dimword (:256) /\ n < dimword (:256) /\ 0 < n /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n) /\
  alloca_inv s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u HG tm. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort u,HG,tm)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_slice_calldata_stages >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  mp_tac (bytestring_source_size_full_run |> Q.INST
    [`sb` |-> `s1`, `opc` |-> `CALLDATASIZE`, `ops` |-> `[]`,
     `wl` |-> `n2w (LENGTH s.vs_call_ctx.cc_calldata)`]) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `q` (qx_choose_then `v`
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> drule emitted_insts_emit_op >> simp[]) >>
  `v.vs_labels = s.vs_labels` by
    (qpat_assum `v = _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [update_var_def] o
        Q.AP_TERM `\st. st.vs_labels`)) >>
  `eval_operand start v = SOME (n2w a) /\
   op_prov G1 start = NONE /\ op_taint tn1 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[]) >>
  `!op. MEM op [start;Lit (n2w n);limit] ==>
      op_prov G1 op = NONE /\ op_taint tn1 op = {} /\
      (!x. op = Var x ==> not_fresh_at s1 x)` by
    (gvs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `allocas_from lo v /\ lo <= v.vs_alloca_next` by
    (qpat_assum `v = _` SUBST1_TAC >>
     simp[allocas_from_def, update_var_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `?u. run_inst_seq (emitted_insts s1 s2) v = Abort Revert_abort u` by
    (mp_tac (slice_bounds_run |> Q.INST [`a` |-> `start_arg`, `n` |-> `length_arg`] |> Q.INST
      [`sa` |-> `s1`, `sb` |-> `s2`, `s` |-> `v`,
       `start_arg` |-> `start`, `length_arg` |-> `Lit (n2w n)`,
       `wa` |-> `n2w a`, `wn` |-> `n2w n`,
       `wl` |-> `n2w (LENGTH s.vs_call_ctx.cc_calldata)`]) >>
     impl_tac >- (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
       qpat_assum `!op. MEM op [start;Lit (n2w n);limit] ==> _` mp_tac >>
       qpat_assum `limit = Var q` mp_tac >>
       rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
     `((n2w a:bytes32) + n2w n <+ n2w a \/
       (n2w (LENGTH s.vs_call_ctx.cc_calldata):bytes32) <+ n2w a + n2w n)` by
       (mp_tac (slice_bounds_word |> Q.INST
          [`limit` |-> `LENGTH s.vs_call_ctx.cc_calldata`]) >>
        impl_tac >- gvs[dimword_def] >>
        gvs[GSYM dimword_def]) >> simp[]) >>
  mp_tac (bytestring_slice_bounds_full_abort |> Q.INST [`a` |-> `start_arg`, `n` |-> `length_arg`] |> Q.INST
    [`sa` |-> `s1`, `sb` |-> `s2`, `s` |-> `v`,
     `start_arg` |-> `start`, `length_arg` |-> `Lit (n2w n)`,
     `wa` |-> `n2w a`, `wn` |-> `n2w n`,
     `wl` |-> `n2w (LENGTH s.vs_call_ctx.cc_calldata)`,
     `G` |-> `G1`, `tn` |-> `tn1`, `ab` |-> `Revert_abort`]) >>
  impl_tac >- (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
       qpat_assum `!op. MEM op [start;Lit (n2w n);limit] ==> _` mp_tac >>
       qpat_assum `limit = Var q` mp_tac >>
       rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`u with vs_inst_idx := v.vs_inst_idx+5`,`G'`,`tn'`] >>
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (v,G1,tn1) _ _` (qspec_then `D` mp_tac) >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
