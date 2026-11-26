(* A dynamic EXTCODECOPY into an already covered memory window. *)
Theory bodyCreateDynamicExtcodecopyMods
Ancestors
  bodyFullRawCallCallOrigin bodyPtrMakeArrayPrimitiveInstall
  bodyPtrBytestringBuiltinsExternalSlice ptrSafetyTransport
  lowerDloadPtrCopy[qualified] venomInstProps
  fragGasOriginPtr ptrSafeRun ptrDiscipline bodyPtrDefs memSafeRun codegenRel
  contextCodegenRel unitTransformDefs venomState venomInst venomExecSemantics
  emitHelper list words

Theorem create_dynamic_extcodecopy_path_physical:
  emit_void EXTCODECOPY [addr;Var p;off;cnt] sa = ((),sb) /\
  fn_has_code sa sb func /\ eval_operand addr s = SOME a /\
  eval_operand (Var p) s = SOME b /\ eval_operand off s = SOME k /\
  eval_operand cnt s = SOME n /\ op_taint tn addr = {} /\
  op_taint tn off = {} /\ op_taint tn cnt = {} /\ ptr_covers G tn p s (w2n n) /\
  ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n b /\
  w2n b + w2n n <= w2n s.vs_fmp /\ allocas_below_fmp s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (write_memory_with_expansion (w2n b) (TAKE (w2n n) (DROP (w2n k) (lookup_account (w2w a) s.vs_accounts).code ++ REPLICATE (w2n n) 0w)) s with vs_inst_idx := LENGTH sb.cs_current_insts),G,
     tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}))
Proof
  strip_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  simp[] >> rpt gen_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id EXTCODECOPY [addr;Var p;off;cnt] []` >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n b) bytes s` >>
  qabbrev_tac `u = write_memory_with_expansion (w2n b) bytes s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, Abbr `bytes`, step_inst_base_opcode_eqs] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists `0` >>
     simp[Abbr `i`] >> irule ptr_inst_ok_external_copy >>
     simp[] >> qexistsl [`k`,`n`] >> simp[] >> qexists `a` >> simp[]) >>
  `source_memory_write_ranges i s = [(w2n b,w2n n)] /\
   source_memory_read_ranges i s = []` by
    simp[Abbr `i`,mk_inst_def,source_memory_read_ranges_def,
         source_memory_write_ranges_def,sized_source_write_range_def] >>
  `i.inst_opcode = EXTCODECOPY` by simp[Abbr `i`,mk_inst_def] >>
  `mem_safe_step 0 ctx i s` by
    simp[mem_safe_step_non_invoke,inst_mem_below_frontiers_def,inst_dload_in_section_def] >>
  `step_prov PG G i u = G /\
   step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}` by
    (simp_tac bool_ss [Abbr `u`] >> irule lowerDloadPtrCopyTheory.external_copy_ghosts >>
     simp[Abbr `i`,mk_inst_def] >> qexistsl [`addr`,`Var p`,`off`,`cnt`,`k`] >> simp[]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode` by
    simp[is_terminator_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` by
    (irule non_gas_mem_safe_origin_ptr_edge >> simp[] >> qexists `bb` >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[Abbr `u`] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[write_memory_with_expansion_def]
QED
