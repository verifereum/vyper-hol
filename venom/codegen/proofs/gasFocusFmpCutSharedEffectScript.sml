(* Shared effects at a related FMP instruction, without whole-run safety. *)
Theory gasFocusFmpCutSharedEffect
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadJointStorageWrite
  o1LowerDloadJointInternalEffects o1LowerDloadJointMemoryWrite o1LowerDloadJointRelation
  o1LowerDloadShared o1LowerDloadRangeTransport ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst vfmState memLocDefs pointerConfinedDefs words byte finite_map pred_set list

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

Theorem cut_storage_load_ghost[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ inst.inst_outputs = [out] ==>
  step_prov PG G inst (update_var out w s) = DRESTRICT G (COMPL {out}) /\
  step_taint inst s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,out_taint tn inst s)
Proof
  strip_tac >> gvs[MEM] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, mem_write_ops_def,
       range_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION,
       taint_component_equality, SF CONJ_ss] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[written_taint_def] >>
  namedCases_on `rest` ["", "b rest2"] >> simp[written_taint_def] >>
  namedCases_on `rest2` ["", "c rest3"] >> simp[written_taint_def] >>
  Cases_on `rest3` >> simp[written_taint_def]
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
    eval_operand p s = SOME x /\ eval_operand sz s = SOME l ==>
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
  qpat_x_assum `!tc p sz tops x l. _` drule_all >> strip_tac >>
  `eval_operand sz t = SOME l` by metis_tac[MEM] >>
  `eval_operands tops t = SOME topics` by
    (irule cut_eval_operands_equal >> qexists_tac `s` >> simp[]) >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
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
