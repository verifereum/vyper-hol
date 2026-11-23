(* The optional caller return buffer occupies no code or one ALLOCA.
   The allocating case uses the raw endpoint supplied by the frame proof. *)
Theory entryIntCallReturnBufferPrefix
Ancestors
  entryCreateFocusSpec entryCreatePathScope abiBufferAllocationCode
  abiEncoderProps exprLoweringProps
  createSizePrefixReplay createMarkedPath fragExec fragGasOrigin frameGasEvents
  venomExecSemantics venomInst venomState venomInstProofs1 compileEnv
  pair list relation arithmetic pred_set

Theorem return_buffer_alloca_edge[local]:
  i.inst_opcode = ALLOCA /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst_base i s = OK r ==>
  (gas_origin_edge F explicit ctx func s marks (OK t) <=>
   marks = [] /\ t = (r with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `~r.vs_halted` by metis_tac[step_inst_base_preserves_all] >>
  simp[gas_origin_edge_def,step_inst_non_invoke,
       gas_events_step_plain,exit_result_def]
QED

Theorem return_buffer_alloca_stop[local]:
  (!marks t. create_prefix_step sa st2 explicit ctx func s marks t ==> t = entry) /\
  create_operand_at st2 entry /\
  create_expr_prefix sa st2 explicit ctx func s marks u ==>
  u = s \/ u = entry
Proof
  strip_tac >>
  `RTC (\x y. ?ms. create_prefix_step sa st2 explicit ctx func x ms y) s u` by
    (drule create_expr_prefix_rtc_project >>
     disch_then (qspec_then `\x y. ?ms. create_prefix_step sa st2 explicit ctx func x ms y` mp_tac) >>
     metis_tac[]) >>
  qpat_x_assum `RTC _ s u` (mp_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  simp[] >> strip_tac >- simp[] >>
  rename1 `create_prefix_step sa st2 explicit ctx func s ms x` >>
  `x = entry` by metis_tac[] >>
  qpat_x_assum `x = entry` SUBST_ALL_TAC >>
  qpat_x_assum `RTC _ entry u` (mp_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  fs[create_prefix_step_def,create_operand_at_def] >> metis_tac[]
QED

Theorem intcall_return_buffer_segment:
  create_operand_at sa s0 /\
  ((st2 = sa /\ entry = s0) \/
   (?buf_n rb r. compile_alloc_buffer buf_n sa = (rb,st2) /\
      fn_has_code sa st2 func /\ ~s0.vs_halted /\
      run_inst_seq (emitted_insts sa st2) s0 = OK r /\
      entry = (r with vs_inst_idx := LENGTH st2.cs_current_insts))) ==>
  create_expr_prefix sa st2 explicit ctx func s0 [] entry /\
  create_operand_at st2 entry /\
  (!p d k before key f i v after.
    create_interior_visit sa st2 explicit ctx func (p,d,k) s0
      (before,(key,f,i,v),after) ==> i.inst_opcode = ALLOCA)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >- (gvs[] >> simp[create_interior_visit_def,create_operand_fetch_def,frag_ids_def]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf_n)]
                              [STRING #"%" (toString sa.cs_next_var)]` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_id = sa.cs_next_id` by simp[Abbr `ins`,mk_inst_def] >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s0.vs_inst_idx = SOME ins` by
    (drule_all fn_has_code_same_block >> simp[create_operand_at_def] >>
     strip_tac >> qexists_tac `bb` >> fs[create_operand_at_def]) >>
  `step_inst_base ins s0 = OK r` by
    (Cases_on `step_inst_base ins s0` >> fs[run_inst_seq_def]) >>
  `create_operand_at st2 entry /\ ~create_operand_at st2 s0 /\
   LENGTH st2.cs_current_insts = SUC s0.vs_inst_idx` by
    (drule step_inst_base_preserves_all >>
     gvs[create_operand_at_def,is_terminator_def]) >>
  `!ms t. gas_origin_edge F explicit ctx func s0 ms (OK t) <=> ms = [] /\ t = entry` by
    (drule_all return_buffer_alloca_edge >> simp[]) >>
  `ins.inst_id IN frag_ids sa st2` by simp[frag_ids_def] >>
  conj_tac
  >- (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
      simp[create_marked_edge_def,create_prefix_step_def,GSYM create_operand_at_def] >>
      metis_tac[]) >>
  simp[] >>
  `!ms t. create_prefix_step sa st2 explicit ctx func s0 ms t ==> t = entry` by
    simp[create_prefix_step_def] >>
  `!u ms. create_expr_prefix sa st2 explicit ctx func s0 ms u /\
          ~create_operand_at st2 u ==> u = s0` by metis_tac[return_buffer_alloca_stop] >>
  rpt gen_tac >> disch_then (strip_assume_tac o MATCH_MP create_interior_visit_cases) >>
  fs[create_operand_fetch_def] >> res_tac >> gvs[]
QED
