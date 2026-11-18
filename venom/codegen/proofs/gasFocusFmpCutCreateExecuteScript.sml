(* Successful CREATE and CREATE2 at a selected FMP cursor. *)
Theory gasFocusFmpCutCreateExecute
Ancestors
  gasFocusFmpCutCreatePrestate fmpStageOpBase fmpStagePointRanges fmpStageRel
  o1LowerDloadExternalEffects o1LowerDloadJointRangeRead lowerDloadOracleCallAssembly
  lowerDloadPtrCreateInterfaces
  ptrDiscipline ptrStaticDiscipline pointerConfinedDefs memLocDefs frameViewFacts contextCodegenRel
  venomWf venomExecSemantics venomCallOracleDefs venomState venomInst
  vfmConstants words finite_map pred_set list

Theorem cut_create_decode[local]:
  MEM inst.inst_opcode [CREATE;CREATE2] /\ step_inst_base inst s = OK s1 ==>
  ?vop offop szop rest value off sz salt.
    inst.inst_operands = vop::offop::szop::rest /\
    eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
    eval_operand szop s = SOME sz /\
    ((inst.inst_opcode = CREATE /\ rest = [] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw.
       rest = [sop] /\ eval_operand sop s = SOME sw /\ salt = SOME sw)) /\
    ~s.vs_call_ctx.cc_static /\ exec_create inst s value off sz salt = OK s1
Proof
  simp[MEM] >> rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operands_def] >> metis_tac[]
QED

Theorem cut_create_scalar_prov[local]:
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  ((inst.inst_opcode = CREATE /\ rest = []) \/
   (inst.inst_opcode = CREATE2 /\ ?sop. rest = [sop])) /\
  inst.inst_operands = vop::offop::szop::rest /\ MEM op (vop::szop::rest) ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v = NONE` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `ptr_use_static_ok _ _ _`
    (qspec_then `v` mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_static_ok_def]) >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def,
      Excl "FILTER"] >>
  simp[FILTER] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem cut_create_read[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. op = Var v ==> ~retpc_var fn v) /\
  eval_operand op s = SOME off /\ MEM (w2n off,len) (source_memory_read_ranges inst s) ==>
  ?off'. eval_operand op t = SOME off' /\ read_memory (w2n off) len s = read_memory (w2n off') len t
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI /\ MEM inst.inst_opcode [SHA3; LOG; CREATE; CREATE2]`
    by gvs[] >>
  drule_all_then assume_tac taint_ok_observation_operand >>
  `!k. k < len ==> w2n off + k NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> irule taint_ok_observation_read >> metis_tac[]) >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  drule_all fmp_mem_read_operand_range_point >> strip_tac >>
  qexists_tac `y` >> simp[] >> irule ld_memory_agree_clean_slice >>
  qexistsl_tac [`0`,`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  asm_rewrite_tac[] >> metis_tac[prim_recTheory.NOT_LESS_0]
QED

Theorem focus_fmp_cut_create_execute:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\ step_inst_base inst s = OK s1 ==>
  ?vop offop szop value off off' sz salt out rq w r rt.
    eval_operand vop s = SOME value /\ eval_operand vop t = SOME value /\
    eval_operand offop s = SOME off /\ eval_operand offop t = SOME off' /\
    eval_operand szop s = SOME sz /\ eval_operand szop t = SOME sz /\
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw.
       inst.inst_operands = [vop;offop;szop;sop] /\
       eval_operand sop s = SOME sw /\ eval_operand sop t = SOME sw /\ salt = SOME sw)) /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    rq = venom_create_request s value off sz salt /\
    rq = venom_create_request t value off' sz salt /\
    inst.inst_outputs = [out] /\ consume_create_outcome rq s = (w,r) /\
    consume_create_outcome rq t = (w,rt) /\ s1 = update_var out w r /\
    step_inst_base inst t = OK (update_var out w rt) /\
    r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions; vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|> /\
    rt = t with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions; vs_returndata := r.vs_returndata;
      vs_requests := record_request rq t.vs_requests|> /\
    tn.t_stor = {} /\ tn.t_trans = {}
Proof
  strip_tac >>
  drule_all focus_fmp_cut_create_prestate >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `!op. MEM op inst.inst_operands ==> !v. op = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >> gen_tac >> disch_tac >>
     irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  `inst.inst_opcode <> PHI /\ MEM inst.inst_opcode [SHA3;LOG;CREATE;CREATE2]` by fs[] >>
  drule_all cut_create_decode >> strip_tac >>
  `!op x. MEM op (vop::szop::rest) /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x` by
    (rpt strip_tac >>
     `MEM op inst.inst_operands` by gvs[] >>
     `op_prov G op = NONE` by metis_tac[cut_create_scalar_prov] >>
     `op_taint tn op = {} /\ (!v. op = Var v ==> ~retpc_var fn v)` by
       metis_tac[taint_ok_observation_operand] >>
     drule_all fmp_stage_operand_point >> strip_tac >>
     fs[] >> metis_tac[fmp_mem_value_clean]) >>
  `?off'. eval_operand offop t = SOME off' /\
     read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (irule cut_create_read >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
     gvs[mem_read_ops_def, source_memory_read_ranges_def, memory_range_of_operands_def] >>
     metis_tac[]) >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _`
    (strip_assume_tac o PURE_REWRITE_RULE [dload_exec_create_success_iff]) >>
  rename1 `consume_create_outcome _ s = (w,r)` >>
  qmatch_asmsub_abbrev_tac `consume_create_outcome rq s` >>
  `venom_create_request t value off' sz salt = rq` by
    (simp[Abbr `rq`] >> metis_tac[]) >>
  drule_all ld_consume_create_outcome_transport >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_create_outcome rq t = (_,rt)` >>
  `exec_create inst t value off' sz salt = OK (update_var out w rt)` by
    (pure_rewrite_tac[dload_exec_create_success_iff] >>
     qexistsl_tac [`out`,`w`,`rt`] >> simp[Excl "consume_create_outcome_eq"]) >>
  `eval_operand vop t = SOME value /\ eval_operand szop t = SOME sz` by
    metis_tac[MEM] >>
  `!sop sw. rest = [sop] /\ eval_operand sop s = SOME sw ==> eval_operand sop t = SOME sw` by
    metis_tac[MEM] >>
  `~t.vs_call_ctx.cc_static` by metis_tac[] >>
  `step_inst_base inst t = OK (update_var out w rt)` by
    (simp[step_inst_base_opcode_eqs, Excl "consume_create_outcome_eq"] >>
     gvs[AllCaseEqs(), Excl "consume_create_outcome_eq"] >> metis_tac[]) >>
  qexistsl_tac [`vop`,`offop`,`szop`,`value`,`off`,`off'`,`sz`,`salt`,`out`,`rq`,`w`,`r`,`rt`] >>
  simp[Excl "consume_create_outcome_eq", Abbr `rt`, Abbr `rq`] >> metis_tac[]
QED
