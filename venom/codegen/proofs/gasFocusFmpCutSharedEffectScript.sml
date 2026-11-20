(* Shared effects at a related FMP instruction, without whole-run safety. *)
Theory gasFocusFmpCutSharedEffect
Ancestors
  fmpStageOpBase fmpStageRel fmpStagePointRanges frameViewFacts
  o1LowerDloadRelocationKernel o1PassContract o1LowerDloadJointStorageWrite
  o1LowerDloadJointInternalEffects o1LowerDloadJointMemoryWrite o1LowerDloadJointRelation
  o1LowerDloadShared o1LowerDloadRangeTransport ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst vfmState memLocDefs pointerConfinedDefs words byte finite_map pred_set list
  fmpStageOpSimMemEffects[qualified,ignore_grammar]

Theorem cut_storage_store[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  (!kop vop key v. inst.inst_operands = [kop;vop] /\
    eval_operand kop s = SOME key /\ eval_operand vop s = SOME v ==>
    ?w. eval_operand kop t = SOME key /\ eval_operand vop t = SOME w /\
        word_agree_except (op_taint tn vop) v w) ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    (step_taint inst s s1 tn).t_mem = tn.t_mem /\
    s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
    s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars /\
    s1.vs_returndata = s.vs_returndata /\ t1.vs_returndata = t.vs_returndata
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  gvs[eval_operands_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  rename1 `inst.inst_operands = [kop;vop]` >>
  rename [`eval_operand kop s = SOME key`, `eval_operand vop s = SOME v`]
  >- (`step_taint inst s (sstore key v s) tn =
        tn with t_stor := key_update tn.t_stor key (op_taint tn vop)` by
        simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
             adopt_reset_def, mem_taint_def, new_site_bytes_def, written_taint_def,
             step_writes_def, source_memory_write_ranges_def, range_bytes_def,
             sstore_def, FLOOKUP_DEF, taint_component_equality,
             EXTENSION, SF CONJ_ss, DRESTRICT_UNIV] >>
      simp[] >> reverse conj_tac >- simp[sstore_def] >> irule ld_shared_sstore >> simp[]) >>
  `step_taint inst s (tstore key v s) tn =
     tn with t_trans := key_update tn.t_trans key (op_taint tn vop)` by
    simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
         adopt_reset_def, mem_taint_def, new_site_bytes_def, written_taint_def,
         step_writes_def, source_memory_write_ranges_def, range_bytes_def,
         tstore_def, FLOOKUP_DEF, taint_component_equality,
         EXTENSION, SF CONJ_ss, DRESTRICT_UNIV] >>
  simp[] >> reverse conj_tac >- simp[tstore_def] >> irule ld_shared_tstore >> simp[]
QED

Theorem cut_storage_load[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  (!op key. MEM op inst.inst_operands /\ eval_operand op s = SOME key ==>
    eval_operand op t = SOME key) ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out y t) /\
    word_agree_except (out_taint tn inst s) x y
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_outputs = [out]`, `inst.inst_operands = [op]`,
          `eval_operand op s = SOME key`] >>
  `eval_operand op t = SOME key` by metis_tac[MEM] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def] >>
  qmatch_goalsub_abbrev_tac `update_var out lhs s` >>
  qmatch_goalsub_abbrev_tac `update_var out rhs t` >>
  qexistsl_tac [`lhs`,`rhs`] >> simp[Abbr `lhs`, Abbr `rhs`] >>
  simp[out_taint_def, sload_def, tload_def, key_taint_def,
       contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def] >>
  fs[ld_shared_agree_def, word_agree_except_def] >> metis_tac[]
QED

Theorem cut_istore[local]:
  inst.inst_opcode = ISTORE /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s1 /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_joint_geometry sites FEMPTY eom owners /\
  (!p vop x v. inst.inst_operands = [p;vop] /\
    eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
    w2n x + 32 <= eom /\
    ?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
        word_agree_except (op_taint tn vop) v w) ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    ld_memory_agree sites eom (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
    s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars /\
    s1.vs_returndata = s.vs_returndata /\ t1.vs_returndata = t.vs_returndata
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [p;vop]`, `eval_operand p s = SOME x`,
          `eval_operand vop s = SOME v`] >>

  `mem_taint tn inst s (istore (w2n x) v s) =
    (tn.t_mem DIFF {i | w2n x <= i /\ i < w2n x+32}) UNION
    {w2n x+j | j IN op_taint tn vop}` by
    (simp[mem_taint_def, new_site_bytes_def, written_taint_def,
          step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
          range_bytes_def, FLOOKUP_DEF, EXTENSION, istore_def, mstore_def,
          write_memory_with_expansion_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
     (tn with t_imm := key_update tn.t_imm (w2n x) (op_taint tn vop))
     (istore (w2n x) v s) (istore (w2n x) w t)` by (irule ld_shared_istore >> simp[]) >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
  conj_tac >- fs[ld_shared_agree_def] >>
  reverse conj_tac >- simp[istore_def,mstore_def,write_memory_with_expansion_def] >>
  simp[istore_memory] >>
  `ld_memory_agree sites eom
      (tn.t_mem DIFF {i | w2n x <= i /\ i < w2n x + 32} UNION
       {w2n x + j | j IN op_taint tn vop})
      (mstore (w2n x) v s).vs_memory (mstore (w2n x) w t).vs_memory` by
    (irule ld_memory_agree_mstore_geometry >>
     (metis_tac[])) >>
  fs[arithmeticTheory.ADD_COMM]
QED

Theorem cut_log_shape[local]:
  inst.inst_opcode = LOG /\ step_inst_base inst s = OK s1 ==>
  ?tc p sz tops x l topics.
    inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
    LENGTH tops = w2n tc /\ ~s.vs_call_ctx.cc_static /\
    eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
    eval_operands tops s = SOME topics /\
    s1 = s with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
         data := read_memory (w2n x) (w2n l) s|>]
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = Lit tc :: rest` >>
  `?offop sizeop tops. REVERSE rest = offop::sizeop::tops` by
    (Cases_on `REVERSE rest` >> fs[] >> Cases_on `t` >> fs[] >>
     metis_tac[LENGTH_REVERSE, LENGTH]) >>
  `rest = REVERSE (offop::sizeop::tops)` by metis_tac[REVERSE_REVERSE] >>
  `LENGTH (REVERSE rest) = w2n tc + 2` by simp[] >>
  qexistsl_tac [`offop`, `sizeop`, `tops`, `off`, `sz`, `topics`] >>
  gs[read_memory_def, REVERSE_APPEND] >>
  `IS_SOME (eval_operands tops s)` by simp[] >>
  `IS_SOME (eval_operands (Lit tc::(REVERSE tops ++ [sizeop] ++ [offop])) s)` by
    fs[eval_operands_IS_SOME_EVERY, EVERY_MEM, MEM_APPEND, MEM_REVERSE,
       SF CONJ_ss, eval_operand_def] >>
  fs[]
  >> (gvs[])
QED

Theorem cut_eval_operands_equal[local]:
  !ops xs. eval_operands ops s = SOME xs /\
    (!op x. MEM op ops /\ eval_operand op s = SOME x ==> eval_operand op t = SOME x) ==>
    eval_operands ops t = SOME xs
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem cut_log_taint[local]:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] ==>
  step_taint inst s (s with vs_logs := s.vs_logs ++ [ev]) tn = tn
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[written_taint_def] >>
     namedCases_on `rest` ["", "b rest2"] >> simp[written_taint_def] >>
     namedCases_on `rest2` ["", "c rest3"] >> simp[written_taint_def] >>
     Cases_on `rest3` >> simp[written_taint_def]) >>
  simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, taint_component_equality,
       EXTENSION, FLOOKUP_DEF, SF CONJ_ss, DRESTRICT_UNIV]
QED

Theorem cut_log[local]:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\ step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  (!tc p sz tops x l. inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
    eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
    MEM (w2n x,w2n l) (source_memory_read_ranges inst s) ==>
    (?y. eval_operand p t = SOME y /\
      (w2n l = 0 \/ (x = y /\ w2n x + w2n l <= eom) \/
       ?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j + w2n l <= z /\
                    w2n x = b+j /\ w2n y = c+j)) /\
    (!op w. MEM op (sz::tops) /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)) ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    (step_taint inst s s1 tn).t_mem = tn.t_mem /\
    s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
    s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars /\
    s1.vs_returndata = s.vs_returndata /\ t1.vs_returndata = t.vs_returndata
Proof
  strip_tac >> drule_all cut_log_shape >> strip_tac >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
  qpat_x_assum `!tc p sz tops x l. _` drule_all >> strip_tac >>
  `eval_operand sz t = SOME l` by metis_tac[MEM] >>
  `eval_operands tops t = SOME topics` by
    (irule cut_eval_operands_equal >> qexists_tac `s` >> simp[]) >>
  `read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t` by
    (irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
     `w2n x + x' NOTIN tn.t_mem` by (irule taint_ok_observation_read >> metis_tac[MEM]) >>
     irule ld_memory_agree_slice_element >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `s.vs_logs ++ [ev]` >>
  qexists_tac `t with vs_logs := t.vs_logs ++ [ev]` >>
  `step_inst_base inst t = OK (t with vs_logs := t.vs_logs ++ [ev])` by
    fs[Abbr `ev`, step_inst_base_opcode_eqs, REVERSE_APPEND, read_memory_def] >>
  `step_taint inst s (s with vs_logs := s.vs_logs ++ [ev]) tn = tn` by
    metis_tac[cut_log_taint] >>
  simp[] >> irule ld_shared_logs_append >> simp[]
QED

val shared_ops = ``[SLOAD; TLOAD; SSTORE; TSTORE; ISTORE; LOG]``;
val storage_ops = ``[SLOAD; TLOAD; SSTORE; TSTORE; ISTORE]``;
val static_abort_ops = ``[SSTORE; TSTORE; LOG]``;

Theorem cut_shared_result[local]:
  MEM inst.inst_opcode ^shared_ops /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  (?s1. r = OK s1) \/
  (?se. r = Abort ExHalt_abort se /\ s.vs_call_ctx.cc_static /\
     IS_SOME (eval_operands inst.inst_operands s) /\
     MEM inst.inst_opcode ^static_abort_ops)
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >> fs[MEM] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def] >>
  gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem cut_shared_abort[local]:
  MEM inst.inst_opcode ^static_abort_ops /\ t.vs_call_ctx = s.vs_call_ctx /\
  s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s) /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          ?y. eval_operand op t = SOME y) ==>
  step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  fs[MEM] >> simp[step_inst_base_opcode_eqs]
QED

val related_operands = ``!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ fmp_value_rel sm (op_prov G op) (op_taint tn op) x y``;

Theorem cut_storage_prov[local]:
  fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  MEM inst.inst_opcode ^storage_ops /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst /\
   (inst.inst_opcode = ISTORE ==>
     !v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn)` by
    metis_tac[fn_static_ptr_ok_def] >>
  Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[MEM, ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem cut_log_operands[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) ==>
  mem_read_ops inst = SOME <|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> /\
  MEM p inst.inst_operands /\ (!op. MEM op (sz::tops) ==> MEM op inst.inst_operands)
Proof
  strip_tac >> simp[mem_read_ops_def, REVERSE_APPEND, MEM_APPEND, MEM_REVERSE] >>
  Cases_on `tops` >> simp[] >> metis_tac[]
QED

Theorem cut_log_scalar_prov[local]:
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  MEM op (sz::tops) ==> op_prov G op = NONE
Proof
  strip_tac >> drule_all cut_log_operands >> strip_tac >>
  Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `MEM (Var v) inst.inst_operands` by metis_tac[] >>
  qpat_x_assum `ptr_use_static_ok _ _ _`
    (qspec_then `v` mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_static_ok_def]) >>
  (impl_tac >- simp[is_pointer_preserving_op_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `p = Var v` by gvs[mem_write_ops_def] >>
  `MEM (Var v) (FILTER ($= (Var v)) (sz::tops))` by simp[MEM_FILTER] >>
  `FILTER ($= (Var v)) (REVERSE inst.inst_operands) = [Var v]` by
    simp[Once FILTER_REVERSE, IgnAsm `inst.inst_operands = _`] >>
  `REVERSE inst.inst_operands = p::sz::tops ++ [Lit tc]` by simp[] >>
  qpat_x_assum `inst.inst_operands = _` kall_tac >>
  gvs[FILTER_APPEND_DISTRIB, Excl "FILTER"] >>
  fs[Once FILTER, FILTER_APPEND_DISTRIB]
QED

Theorem cut_storage_key[local]:
  taint_ok fn tn inst s /\
  ((MEM inst.inst_opcode [SLOAD;TLOAD] /\ MEM op inst.inst_operands) \/
   (MEM inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\ inst.inst_operands = [op;vop])) ==>
  op_taint tn op = {}
Proof
  strip_tac >> fs[taint_ok_def] >> gvs[MEM] >> metis_tac[]
QED

Theorem cut_istore_low[local]:
  access_ok eom G fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [op;vop] /\
  op_prov G op = NONE /\ eval_operand op s = SOME x /\ eval_operand vop s = SOME v ==>
  w2n x + 32 <= eom
Proof
  strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def, mem_write_ops_def, source_memory_write_ranges_def,
       fixed_source_write_range_def] >>
  disch_then (mp_tac o CONJUNCT1) >>
  Cases_on `op` >> gvs[op_prov_def]
QED

Theorem cut_log_range[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  (!v. p = Var v ==> ~retpc_var fn v) /\
  eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
  MEM (w2n x,w2n l) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand p t = SOME y /\
    (w2n l = 0 \/ (x = y /\ w2n x + w2n l <= eom) \/
     ?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
                  j + w2n l <= z /\ w2n x = b+j /\ w2n y = c+j)
Proof
  strip_tac >> drule_all cut_log_operands >> strip_tac >>
  `MEM inst.inst_opcode [SHA3;LOG;CREATE;CREATE2] /\ inst.inst_opcode <> PHI` by simp[] >>
  drule_all_then assume_tac taint_ok_observation_operand >>
  `(<|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> : inst_access_ops).iao_ofst = p` by simp[] >>
  drule_all fmp_mem_read_operand_range_point >> simp[w2n_11]
QED

val cut_data = ``
  (!v. ~MEM v inst.inst_outputs ==>
       FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
       FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
     ?y. FLOOKUP t1.vs_vars v = SOME y /\
         (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
           (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata``;

Theorem cut_storage_values[local]:
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode ^storage_ops /\ ^related_operands ==>
  !op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint tn op) x y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac cut_storage_prov >>
  first_x_assum drule_all >> simp[fmp_value_rel_def, ld_value_agree_scalar]
QED

Theorem cut_storage_load_data[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ inst.inst_outputs = [out] /\
  s1 = update_var out x s /\ t1 = update_var out y t /\
  word_agree_except (out_taint tn inst s) x y /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata ==>
  ^cut_data
Proof
  strip_tac >> drule_all fmpStageOpSimMemEffectsTheory.fmp_mem_storage_load_ghost >> strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
      fmp_value_rel_def, ld_value_agree_scalar, ld_shared_agree_def]
QED

val point_nonretpc = ``!op v. MEM op inst.inst_operands /\ op = Var v ==> ~retpc_var fn v``;

Theorem cut_log_related[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET fn_pv P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  ^related_operands /\ ^point_nonretpc /\
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\ step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  s.vs_returndata = t.vs_returndata ==>
  ?t1. step_inst_base inst t = OK t1 /\ ^cut_data
Proof
  strip_tac >>
  `!tc p sz tops x l. inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
     eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
     MEM (w2n x,w2n l) (source_memory_read_ranges inst s) ==>
     (?y. eval_operand p t = SOME y /\
       (w2n l = 0 \/ (x = y /\ w2n x + w2n l <= eom) \/
        ?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
                     j + w2n l <= z /\ w2n x = b+j /\ w2n y = c+j)) /\
     (!op w. MEM op (sz::tops) /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w)` by
    (rpt gen_tac >> strip_tac >> drule_all cut_log_operands >> strip_tac >>
     conj_tac >- (`!v. p = Var v ==> ~retpc_var fn v` by metis_tac[] >>
                  drule_all cut_log_range >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     `MEM op inst.inst_operands` by metis_tac[] >>
     drule_all_then assume_tac cut_log_scalar_prov >>
     `MEM inst.inst_opcode [SHA3; LOG; CREATE; CREATE2]` by simp[] >>
     drule_all_then assume_tac taint_ok_observation_operand >>
     qpat_x_assum `!op x. _ ==> ?y. _ /\ fmp_value_rel _ _ _ _ _` drule_all >>
     metis_tac[fmp_mem_value_clean]) >>
  drule_all cut_log >> strip_tac >> qexists `t1` >> simp[]
QED

val storage_values = ``!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint tn op) x y``;
val store_inputs = ``!p vop x v. inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
  ?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
      word_agree_except (op_taint tn vop) v w``;

Theorem cut_store_inputs[local]:
  ^storage_values /\ MEM inst.inst_opcode [SSTORE; TSTORE; ISTORE] /\
  taint_ok fn tn inst s ==> ^store_inputs
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `op_taint tn p = {}` by (irule cut_storage_key >> metis_tac[]) >>
  `?y. eval_operand p t = SOME y /\ word_agree_except {} x y` by metis_tac[MEM] >>
  `x = y` by metis_tac[ld_value_agree_clean, ld_value_agree_scalar] >>
  metis_tac[MEM]
QED

Theorem cut_storage_ok[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  eom <= fmp0 /\ fmp0 <= raw0 /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst_wf inst /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  ~in_revert_forward fn s /\ ^related_operands /\
  MEM inst.inst_opcode ^storage_ops /\ step_inst_base inst s = OK s1 /\
  t.vs_call_ctx = s.vs_call_ctx /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  s.vs_returndata = t.vs_returndata ==>
  ?t1. step_inst_base inst t = OK t1 /\ ^cut_data
Proof
  strip_tac >>
  `^storage_values` by metis_tac[cut_storage_values] >>
  Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD]`
  >- (`!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
         eval_operand op t = SOME x` by
        (rpt gen_tac >> strip_tac >>
         `op_taint tn op = {}` by (irule cut_storage_key >> metis_tac[]) >>
         qpat_x_assum `^storage_values` drule_all >> simp[] >>
         metis_tac[ld_value_agree_clean, ld_value_agree_scalar]) >>
      drule_all cut_storage_load >> strip_tac >>
      qexists `update_var out y t` >> conj_tac >- simp[] >>
      irule cut_storage_load_data >> metis_tac[]) >>
  `MEM inst.inst_opcode [SSTORE; TSTORE; ISTORE]` by gvs[MEM] >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  `^store_inputs` by (match_mp_tac cut_store_inputs >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SSTORE; TSTORE]`
  >- (drule_all cut_storage_store >> strip_tac >> qexists `t1` >> simp[]) >>
  `inst.inst_opcode = ISTORE` by gvs[MEM] >>
  `!p vop x v. inst.inst_operands = [p;vop] /\
     eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
     w2n x + 32 <= eom /\
     ?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
         word_agree_except (op_taint tn vop) v w` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (`MEM p inst.inst_operands` by simp[] >>
         drule_all_then assume_tac cut_storage_prov >>
         drule_all cut_istore_low >> simp[]) >>
     qpat_x_assum `^store_inputs` drule_all >> simp[]) >>
  drule_all_then assume_tac fmp_mem_geometry_point >>
  drule_all cut_istore >> strip_tac >> qexists `t1` >> simp[]
QED

(* The retained opcode runs on the actual related target state; this result
   feeds the separate reconstruction of the successor frame. *)
Theorem focus_fmp_cut_shared_effect:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  eom <= fmp0 /\ fmp0 <= raw0 /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst_wf inst /\ opaque_use_ok fn /\ access_ok eom G fn inst s /\
  taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode ^shared_ops /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\ ^cut_data
    | Abort ab s1 => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> RET /\
   inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET` by gvs[MEM] >>
  `^point_nonretpc` by metis_tac[ordinary_operand_not_retpc] >>
  `^related_operands` by
    (rpt gen_tac >> strip_tac >>
     `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[] >>
     drule_all fmp_stage_operand_point >> simp[]) >>
  drule_all cut_shared_result >> strip_tac
  >- (qpat_x_assum `r = OK s1` SUBST_ALL_TAC >>
      `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
       ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
       s.vs_returndata = t.vs_returndata` by
        fs[fmp_stage_rel_def] >>
      `?t1. step_inst_base inst t = OK t1 /\ ^cut_data` by
        (Cases_on `inst.inst_opcode = LOG`
         >- (`inst.inst_outputs = []` by gvs[inst_wf_def] >>
             `ptr_use_static_ok P (fn_pv P fn) inst` by metis_tac[fn_static_ptr_ok_def] >>
             drule_all cut_log_related >> simp[]) >>
         `MEM inst.inst_opcode ^storage_ops` by gvs[MEM] >>
         drule_all cut_storage_ok >> simp[]) >>
      qexists `OK t1` >> simp[] >> qexists `t1` >> simp[]) >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y` by metis_tac[] >>
  drule_all_then assume_tac cut_shared_abort >>
  qexists `Abort ExHalt_abort (halt_state (set_returndata [] t))` >>
  gvs[dead_result_rel_def]
QED
