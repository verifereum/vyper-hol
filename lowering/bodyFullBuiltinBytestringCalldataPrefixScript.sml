(* CALLDATASIZE and the slice bounds test share their concrete endpoint. *)
Theory bodyFullBuiltinBytestringCalldataPrefix
Ancestors
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBounds
  bodyPtrBytestringBuiltinsSlice bodyPtrBytestringBuiltinsBounds
  bodyFullUnwrapRun fragGasOriginPtr fragExec exprSimProps exprLoweringProps
  emitHelper emitHelperProps freshWrites compileEnv loweringStateRelDefs
  localPtrsProps ptrDiscipline venomExecSemantics venomState venomInst words list finite_map

Theorem bytestring_calldata_prefix_full_run:
  emit_op CALLDATASIZE [] sa = (limit,sm) /\
  compile_assert_slice_bounds start (Lit (n2w n)) limit sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a < dimword (:256) /\ n < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a+n < dimword (:256) /\ a+n <= LENGTH s.vs_call_ctx.cc_calldata /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    t = s with <|vs_vars := t.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac
     >- metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
     metis_tac[slice_bounds_extends]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  mp_tac (bytestring_source_size_full_run |> Q.INST
    [`sb` |-> `sm`, `opc` |-> `CALLDATASIZE`, `ops` |-> `[]`,
     `wl` |-> `n2w (LENGTH s.vs_call_ctx.cc_calldata)`]) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `q` (qx_choose_then `u`
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `alloca_inv u` by
    (irule alloca_inv_fields >> qexists_tac `s` >> simp[update_var_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> drule emitted_insts_emit_op >> simp[]) >>
  `eval_operand start u = SOME (n2w a) /\
   op_prov G1 start = NONE /\ op_taint tn1 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[]) >>
  `!op. MEM op [start;Lit (n2w n);limit] ==>
      op_prov G1 op = NONE /\ op_taint tn1 op = {} /\
      (!x. op = Var x ==> not_fresh_at sm x)` by
    (gvs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `u = _` SUBST1_TAC >>
     simp[allocas_from_def, update_var_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  mp_tac (slice_bounds_reserved_natural_runtime |> Q.INST
    [`sa` |-> `sm`, `s` |-> `u`, `len` |-> `Lit (n2w n)`,
     `cap` |-> `LENGTH s.vs_call_ctx.cc_calldata`]) >>
  impl_tac >- (simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sm sb) u = OK v` by simp[] >>
  mp_tac (bytestring_slice_bounds_full_run |> Q.INST
    [`sa` |-> `sm`, `s` |-> `u`, `u` |-> `v`,
     `len` |-> `Lit (n2w n)`, `G` |-> `G1`, `tn` |-> `tn1`,
     `wa` |-> `n2w a`, `wn` |-> `n2w n`,
     `wl` |-> `n2w (LENGTH s.vs_call_ctx.cc_calldata)`]) >>
  impl_tac
  >- (simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
      qpat_assum `!op. MEM op [start;Lit (n2w n);limit] ==> _` mp_tac >>
      qpat_assum `limit = Var q` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)) >>
  qabbrev_tac `t = v with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `t = s with <|vs_vars := t.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_assum `v = u with vs_vars := v.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sb.cs_current_insts`) >>
     simp[Abbr `t`, update_var_def]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (fs[lookup_var_def] >> simp[Abbr `t`] >> metis_tac[]) >>
  (fn (asl,w) =>
    let
      val horizon = find_term (fn tm => is_forall tm andalso
        fst (dest_var (fst (dest_forall tm))) = "H'") w
      val endpoint = last (snd (strip_comb (snd (dest_imp
        (snd (dest_forall horizon))))))
    in
      qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => sg [ANTIQUOTE (subst [endpoint |-> lhs (concl th)] horizon)]) (asl,w)
    end)
  >-
    (rpt strip_tac >>
     qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_vars_frame >>
     simp[] >> fs[local_ptrs_reserved_def, lookup_var_def,
                  stmt_state_rel_inst_idx] >> metis_tac[]) >>
  `alloca_history func t` by
    (simp[Abbr `t`] >>
     qspecl_then [`emitted_insts sm sb`,`sm`,`sb`,`u`,`v`]
       mp_tac emitted_alloca_history >>
     impl_tac
      >- (drule compile_assert_slice_bounds_layout >> strip_tac >>
          gvs[same_blocks_def, is_terminator_def, mk_inst_def, update_var_def]) >>
      simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,G2,tn2)` by
    (gen_tac >> qunabbrev_tac `t` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `G1 = _` mp_tac >> qpat_assum `tn1 = _` mp_tac >>
     qpat_assum `u = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
     metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `~v.vs_halted` by
    (qpat_assum `v = u with vs_vars := v.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >> simp[]) >>
  qexistsl_tac [`t`,`G2`,`tn2`] >>
  simp[Abbr `t`, update_var_def] >> rpt strip_tac >>
  (fn (asl,w) =>
    qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ _`
      (match_mp_tac o ISPEC (hd (snd (strip_comb w)))) (asl,w)) >>
  first_assum ACCEPT_TAC
QED
