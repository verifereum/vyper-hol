(* Shared storage, immutable and log operations at an FMP boundary. *)
Theory fmpStageOpSimMemEffects
Ancestors
  fmpStageOpSimMemSupport fmpStageOpSimMemReads fmpStageOpSimMemWrites fmpStageOpBase fmpStageRel
  o1LowerDloadShared o1LowerDloadRangeTransport o1LowerDloadMemoryConsumer
  o1LowerDloadRelocationKernel o1PassContract ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst vfmState memLocDefs pointerConfinedDefs words byte finite_map pred_set list

Theorem fmp_mem_effect_scalar_prov[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE;ISTORE] /\
  MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst /\
   (inst.inst_opcode = ISTORE ==>
     !v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn)` by
    (fs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem fmp_mem_effect_word[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE;ISTORE] /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint tn op) x y
Proof
  strip_tac >>
  `op_prov G op = NONE` by metis_tac[fmp_mem_effect_scalar_prov] >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_stage_operand >> simp[fmp_value_rel_def, ld_value_agree_def]
QED

Theorem fmp_mem_effect_clean[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ((MEM inst.inst_opcode [SLOAD;TLOAD] /\ MEM op inst.inst_operands) \/
   (MEM inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\ inst.inst_operands = [op;vop])) /\
  eval_operand op s = SOME x ==> eval_operand op t = SOME x
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE;ISTORE] /\ MEM op inst.inst_operands` by gvs[] >>
  `op_prov G op = NONE` by metis_tac[fmp_mem_effect_scalar_prov] >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_operand_clean >> simp[]
QED

Theorem fmp_mem_storage_load_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [SLOAD;TLOAD] /\ step_inst k C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\ inst.inst_outputs = [out] /\
    step_inst k C' inst t = OK (update_var out y t) /\
    word_agree_except (out_taint tn inst s) x y
Proof
  strip_tac >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (rpt strip_tac >> irule fmp_mem_effect_clean >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `inst.inst_outputs = [out]` >>
  rename1 `eval_operand op s = SOME key` >>
  `eval_operand op t = SOME key` by metis_tac[MEM] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def] >>
  gvs[out_taint_def, sload_def, tload_def, ld_shared_agree_def,
      key_taint_def, contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def] >>
  qmatch_goalsub_abbrev_tac `update_var out lhs s` >>
  qmatch_goalsub_abbrev_tac `update_var out rhs t` >>
  qexistsl_tac [`lhs`,`rhs`] >> simp[Abbr `lhs`, Abbr `rhs`] >>
  fs[word_agree_except_def] >> metis_tac[]
QED

Theorem fmp_mem_storage_load_ghost[local]:
  MEM inst.inst_opcode [SLOAD;TLOAD] /\ inst.inst_outputs = [out] ==>
  step_prov PG G inst (update_var out w s) = DRESTRICT G (COMPL {out}) /\
  step_taint inst s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,out_taint tn inst s)
Proof
  strip_tac >> fs[] >>
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

Theorem fmp_mem_storage_store_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\ step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [kop;vop]`, `eval_operand kop s = SOME key`,
          `eval_operand vop s = SOME v`] >>
  `eval_operand kop t = SOME key` by
    (irule fmp_mem_effect_clean >> simp[] >> metis_tac[]) >>
  `?w. eval_operand vop t = SOME w /\ word_agree_except (op_taint tn vop) v w` by
    (irule fmp_mem_effect_word >> metis_tac[MEM]) >>
  gvs[eval_operands_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
  simp[ld_shared_agree_def, sstore_def, tstore_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[ld_shared_agree_def] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[key_update_def, word_agree_except_def])
  >- (qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `t.vs_call_ctx.cc_address` mp_tac) >>
      disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED

Theorem fmp_mem_istore_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = ISTORE /\ step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    ld_memory_agree (fmp_ld_sites sm) eom (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [p;vop]`, `eval_operand p s = SOME off`,
          `eval_operand vop s = SOME v`] >>
  `eval_operand p t = SOME off` by
    (irule fmp_mem_effect_clean >> simp[] >> metis_tac[]) >>
  `?w. eval_operand vop t = SOME w /\ word_agree_except (op_taint tn vop) v w` by
    (irule fmp_mem_effect_word >> simp[] >> metis_tac[MEM]) >>
  `w2n off + 32 <= eom` by
    (`access_ok eom G fn inst s` by metis_tac[fmp_stage_frame_facts] >>
     `op_prov G p = NONE` by (irule fmp_mem_effect_scalar_prov >> simp[] >> metis_tac[MEM]) >>
     gvs[access_ok_def, mem_write_ops_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, op_prov_def] >>
     Cases_on `p` >> gvs[op_prov_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> conj_tac
  >- (`mem_taint tn inst s (istore (w2n off) v s) =
        (tn.t_mem DIFF {i | w2n off<=i /\ i<w2n off+32}) UNION
        {w2n off+j | j IN op_taint tn vop}` by
       (simp[mem_taint_def, new_site_bytes_def, written_taint_def,
             step_writes_def, source_memory_write_ranges_def,
             fixed_source_write_range_def, range_bytes_def, FLOOKUP_DEF, EXTENSION,
             istore_def, mstore_def, write_memory_with_expansion_def] >>
        metis_tac[]) >>
      fs[istore_def] >> irule fmp_mem_mstore_agree >> simp[] >> metis_tac[]) >>
  fs[fmp_stage_rel_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       ld_shared_agree_def, istore_def, mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[ld_shared_agree_def] >>
  Cases_on `key = w2n off` >>
  gvs[key_update_def, word_agree_except_def, FAPPLY_FUPDATE_THM]
QED

Theorem fmp_mem_log_scalar[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  MEM op (sz::tops) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G v` >>
     Cases_on `FLOOKUP G v` >> simp[] >>
     `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
     simp[ptr_use_static_ok_def, is_pointer_preserving_op_def, mem_write_ops_def,
          mem_read_ops_def] >>
     qexists_tac `v` >> simp[MEM_REVERSE, REVERSE_APPEND] >>
     Cases_on `p = Var v` >>
     gvs[FILTER_APPEND_DISTRIB, FILTER_REVERSE, REVERSE_EQ_SING, FILTER_EQ_NIL] >>
     Cases_on `tops` >> gvs[] >> IF_CASES_TAC >> gvs[] >> strip_tac >>
     qpat_x_assum `_ = [Var v]` (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
     simp[] >> IF_CASES_TAC >> simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def, MEM_REVERSE] >> gvs[] >> metis_tac[MEM, MEM_APPEND]) >>
  `MEM op inst.inst_operands /\ inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by
    gvs[retpc_use_ok_def, MEM_REVERSE] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_operand_clean >> simp[]
QED

Theorem fmp_mem_log_read[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\ LENGTH tops = w2n tc /\
  eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
  eval_operands tops s = SOME topics ==>
  ?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    eval_operands tops t = SOME topics /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t
Proof
  strip_tac >>
  `!op x. MEM op (sz::tops) /\ eval_operand op s = SOME x ==> eval_operand op t = SOME x` by
    (rpt strip_tac >> irule fmp_mem_log_scalar >> metis_tac[]) >>
  `eval_operand sz t = SOME l` by metis_tac[MEM] >>
  `eval_operands tops t = SOME topics` by
    (qpat_x_assum `!op x. _` mp_tac >>
     qpat_x_assum `eval_operands tops s = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> qid_spec_tac `topics` >> Induct_on `tops` >>
     simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >>
     rename1 `eval_operand h s = SOME a` >>
     `eval_operand h t = SOME a` by metis_tac[MEM] >> simp[] >>
     gvs[] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn p = {}` by (fs[taint_ok_def, MEM_REVERSE] >> gvs[] >> metis_tac[MEM, MEM_APPEND]) >>
  `MEM p inst.inst_operands /\ inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by
    simp[retpc_use_ok_def, MEM_REVERSE] >>
  `!v. p = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
  `mem_read_ops inst = SOME <|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> /\
   (<|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> : inst_access_ops).iao_ofst = p` by
    (simp[mem_read_ops_def, REVERSE_APPEND] >> Cases_on `tops` >> simp[]) >>
  drule_all fmp_mem_read_operand_range >> strip_tac >> qexists_tac `y` >> simp[] >>
  irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
  `w2n x+x' NOTIN tn.t_mem` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def, about_to_revert_def] >>
     strip_tac >> qpat_x_assum `!off len i. _`
       (qspecl_then [`w2n x`,`w2n l`,`w2n x+x'`] mp_tac) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem fmp_mem_log_shape[local]:
  inst.inst_opcode = LOG /\ step_inst k C inst s = OK s1 ==>
  ?tc p sz tops x l topics.
    inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
    LENGTH tops = w2n tc /\ ~s.vs_call_ctx.cc_static /\
    eval_operand p s = SOME x /\ eval_operand sz s = SOME l /\
    eval_operands tops s = SOME topics /\
    s1 = s with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
         data := read_memory (w2n x) (w2n l) s|>]
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = Lit tc :: rest` >>
  `?p sizeop tops. REVERSE rest = p::sizeop::tops` by
    (Cases_on `REVERSE rest` >> fs[] >> Cases_on `t` >> fs[] >>
     metis_tac[LENGTH_REVERSE, LENGTH]) >>
  `rest = REVERSE (p::sizeop::tops)` by metis_tac[REVERSE_REVERSE] >>
  gvs[read_memory_def] >>
  `IS_SOME (eval_operands tops s)` by simp[] >>
  `IS_SOME (eval_operands inst.inst_operands s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM, MEM_REVERSE, MEM_APPEND,
          eval_operand_def] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     rpt strip_tac >> gvs[eval_operand_def]) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >> gvs[]
QED

Theorem fmp_mem_log_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = LOG /\ step_inst k C inst s = OK s1 ==>
  ?ev. s1 = s with vs_logs := s.vs_logs ++ [ev] /\
    step_inst k C' inst t = OK (t with vs_logs := t.vs_logs ++ [ev])
Proof
  strip_tac >> drule_all fmp_mem_log_shape >> strip_tac >>
  drule_all fmp_mem_log_read >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  qexists_tac `<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
                 data := read_memory (w2n x) (w2n l) s|>` >> simp[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, read_memory_def] >>
  gvs[read_memory_def, REVERSE_APPEND]
QED

Theorem fmp_mem_effect_defined[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE;ISTORE;LOG] /\
  IS_SOME (eval_operands inst.inst_operands s) ==>
  IS_SOME (eval_operands inst.inst_operands t)
Proof
  strip_tac >> fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM op inst.inst_operands` >>
  `?x. eval_operand op s = SOME x` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_stage_operand >> strip_tac >> simp[]
QED

Theorem fmp_mem_effect_outputs[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE;TSTORE;ISTORE;LOG] ==> inst.inst_outputs = []
Proof
  strip_tac >>
  `o1_fn_shape C fn /\ MEM inst (fn_insts fn)` by
    metis_tac[fmp_stage_frame_facts] >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  fs[] >> gvs[inst_wf_def]
QED

Theorem fmp_mem_effect_result[local]:
  MEM inst.inst_opcode [SLOAD;TLOAD;SSTORE;TSTORE;ISTORE;LOG] /\
  step_inst k C inst s = r /\ terminates r ==>
  (?s1. r = OK s1) \/
  (?se. r = Abort ExHalt_abort se /\ s.vs_call_ctx.cc_static /\
     IS_SOME (eval_operands inst.inst_operands s) /\
     MEM inst.inst_opcode [SSTORE;TSTORE;LOG])
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def] >>
  gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem fmp_mem_effect_abort[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\ s.vs_call_ctx.cc_static /\
  IS_SOME (eval_operands inst.inst_operands s) ==>
  step_inst k C' inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (irule fmp_mem_effect_defined >> fs[] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem fmp_mem_effects_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE; ISTORE; LOG] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> drule_all fmp_mem_effect_result >> strip_tac
  >- (qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      Cases_on `MEM inst.inst_opcode [SLOAD;TLOAD]`
      >- (drule_all fmp_mem_storage_load_step >> strip_tac >>
          qexistsl_tac [`k`,`OK (update_var out y t)`] >> simp[] >>
          drule_all fmp_mem_storage_load_ghost >> strip_tac >> gvs[] >>
          simp[update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
               fmp_value_rel_def, ld_value_agree_scalar] >>
          fs[fmp_stage_rel_def, ld_shared_agree_def, update_var_def]) >>
      `inst.inst_outputs = []` by (irule fmp_mem_effect_outputs >> fs[] >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = LOG`
      >- (drule_all fmp_mem_log_step >> strip_tac >>
          qexistsl_tac [`k`,`OK (t with vs_logs := t.vs_logs ++ [ev])`] >> simp[] >>
          gvs[] >>
          simp[step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
               adopt_reset_def, mem_taint_def, new_site_bytes_def, written_taint_def,
               step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
          fs[fmp_stage_rel_def, ld_shared_agree_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
          namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[] >>
          namedCases_on `rest` ["", "b rest2"] >> gvs[] >>
          namedCases_on `rest2` ["", "c rest3"] >> gvs[] >>
          Cases_on `rest3` >> gvs[]) >>
      Cases_on `inst.inst_opcode = ISTORE`
      >- (drule_all fmp_mem_istore_step >> strip_tac >>
          qexistsl_tac [`k`,`OK t1`] >> simp[] >>
          qpat_x_assum `step_inst _ C _ _ = _` mp_tac >>
          qpat_x_assum `step_inst _ C' _ _ = _` mp_tac >>
          simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
          ntac 2 strip_tac >> gvs[] >>
          gvs[step_taint_def, set_var_taint_def, adopt_reset_def,
              istore_def, mstore_def, write_memory_with_expansion_def] >>
          fs[fmp_stage_rel_def]) >>
      `MEM inst.inst_opcode [SSTORE;TSTORE]` by fs[] >>
      drule_all fmp_mem_storage_store_step >> strip_tac >>
      qexistsl_tac [`k`,`OK t1`] >> simp[] >>
      qpat_x_assum `step_inst _ C _ _ = _` mp_tac >>
      qpat_x_assum `step_inst _ C' _ _ = _` mp_tac >> fs[] >>
      simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
      simp[AllCaseEqs()] >> ntac 2 strip_tac >> gvs[] >>
      fs[fmp_stage_rel_def, sstore_def, tstore_def] >>
      gvs[step_taint_def, set_var_taint_def, mem_taint_def, new_site_bytes_def,
          written_taint_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def, adopt_reset_def, imm_taint_def, FLOOKUP_DEF,
          EXTENSION, SF CONJ_ss]) >>
  qpat_x_assum `r = Abort _ _` SUBST_ALL_TAC >>
  drule_all fmp_mem_effect_abort >> strip_tac >>
  qexistsl_tac [`k`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`] >>
  simp[dead_result_rel_def]
QED

