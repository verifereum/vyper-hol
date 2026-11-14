Theory bodyFullBuiltinPrecompileSuffixPath
Ancestors
  bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsSuffix
  fragGasSeqPtr fragExecMem fragExec instMemFrontier memSafeRun
  venomInstProofs venomExecSemantics venomInst venomState instIdxIndep
  ptrDiscipline exprLoweringProps finite_map list rich_list

Theorem precompile_suffix_mem_ok:
  ((addr = 1w /\ an = 128w /\ rn = 32w) \/
   (addr = 6w /\ an = 128w /\ rn = 64w) \/
   (addr = 7w /\ an = 96w /\ rn = 64w)) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  w2n wi + w2n an <= s.vs_alloca_next /\
  w2n wo + w2n rn <= s.vs_alloca_next /\
  run_inst_seq [gi;ci;ai] s = OK q ==>
  run_inst_seq_mem_ok [gi;ci;ai] s
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_gas_def, bind_outputs_def] >>
  Cases_on `s.vs_gas_readings` >> simp[] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_STATICCALL,
       inst_dload_in_section_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def] >>
  gvs[eval_operand_def, lookup_var_def, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base ii st` >>
  Cases_on `step_inst_base ii st` >> simp[]
QED

Theorem precompile_suffix_origin_path:
  ((addr = 1w /\ an = 128w /\ rn = 32w) \/
   (addr = 6w /\ an = 128w /\ rn = 64w) \/
   (addr = 7w /\ an = 96w /\ rn = 64w)) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  w2n wi + w2n an <= s.vs_alloca_next /\
  w2n wo + w2n rn <= s.vs_alloca_next /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  ptr_covers G tn src s (w2n an) /\
  ptr_covers G tn dst s (w2n rn) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [F]
    (OK (q with vs_inst_idx := s.vs_inst_idx + 3),G2,tn2)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok [gi;ci;ai] s` by
    (irule precompile_suffix_mem_ok >> metis_tac[]) >>
  `run_inst_seq [gi;ci] s = OK v` by
    gvs[run_inst_seq_def] >>
  `?g t. inst_seq_ptr D lo ctx func PG G tn [gi;ci;ai] s g t` by
    (irule suffix_checked >> metis_tac[]) >>
  `inst_seq_ptr D lo ctx func PG G tn [gi;ci;ai] s G2 tn2` by
    (drule_all suffix_final_ghost >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [gi;ci;ai]` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  simp[mk_inst_def, is_terminator_def]
QED
