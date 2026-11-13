(* RawLog dynamic header/payload preparation: joint instruction checks. *)
Theory bodyFullRawLogDynamicPrepareSafety
Ancestors
  bodyFullRawLogDynamicData fragGasSeqPtr ptrSafeRun ptrDiscipline
  fragExecMem unitTransformDefs venomExecSemantics venomInstProofs
  venomInst venomState finite_map words list arithmetic valueEncodingDefs
  instIdxIndep pred_set memSafeRun contextCodegenRel codegenRel bodyPtrDefs memLocDefs

Theorem raw_log_dynamic_prepare_safety:
  src <> l /\ src <> p /\ l <> p /\
  eval_operand (Var src) s = SOME (n2w b) /\
  FLOOKUP G src = SOME (rootbase,cap) /\
  ptr_covers G tn src s (32+32*word_size (LENGTH bs)) /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (!i. b<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  b+32+LENGTH bs <= s.vs_alloca_next /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\
  u = update_var l (n2w (LENGTH bs)) s /\
  v = update_var p (n2w (b+32)) u /\
  step_inst_base (mk_inst id MLOAD [Var src] [l]) s = OK u /\
  step_inst_base (mk_inst (id+1) ADD [Var src;Lit 32w] [p]) u = OK v ==>
  run_inst_seq_mem_ok
    [mk_inst id MLOAD [Var src] [l];
     mk_inst (id+1) ADD [Var src;Lit 32w] [p]] s /\
  inst_seq_ptr D lo ctx func PG G tn
    [mk_inst id MLOAD [Var src] [l];
     mk_inst (id+1) ADD [Var src;Lit 32w] [p]] s
    (DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap)))
    (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}))
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  conj_tac >- suspend "memory" >>
  suspend "pointer"
QED

Resume raw_log_dynamic_prepare_safety[memory]:
  simp[run_inst_seq_mem_ok_def] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    mk_inst_def, update_var_def, AllCaseEqs()] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume raw_log_dynamic_prepare_safety[pointer]:
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- suspend "load_ok" >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  `mem_word_taint tn.t_mem b = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
     Cases_on `x < 32` >> simp[] >>
     qpat_x_assum `!i. _` (qspec_then `b+x` mp_tac) >>
     `b <= b+x /\ b+x < b+32+LENGTH bs` by decide_tac >> simp[]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    written_taint_def, set_var_taint_def, out_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, update_var_def] >>
  simp[GSYM FLOOKUP_DEF] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- suspend "add_ok" >>
  qpat_x_assum `step_inst_base _ u = OK v` mp_tac >>
  simp[mk_inst_def, update_var_def] >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[exec_pure2_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    update_var_def] >>
  simp[inst_seq_ptr_def, step_prov_def, set_prov_def, out_prov_def,
    op_prov_def, FLOOKUP_DRESTRICT, step_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
    range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, update_var_def] >>
  fs[eval_operand_def, lookup_var_def] >>
  simp[first_prov_def, op_prov_def, FLOOKUP_DRESTRICT,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `!aid b' sz. FLOOKUP s.vs_allocas aid = SOME (b',sz) ==> aid IN FDOM s.vs_allocas` by
    (rpt gen_tac >> Cases_on `aid IN FDOM s.vs_allocas` >> simp[FLOOKUP_DEF]) >>
  simp[taint_component_equality, EXTENSION] >> metis_tac[]
QED

Resume raw_log_dynamic_prepare_safety[load_ok]:
  fs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    mem_read_ops_def, step_inst_non_invoke] >>
  gvs[eval_operand_def] >> decide_tac
QED

Resume raw_log_dynamic_prepare_safety[add_ok]:
  fs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    mem_read_ops_def, step_inst_non_invoke, allocas_from_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  fs[op_taint_def, allocas_from_def, eval_operand_def, lookup_var_def] >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE, update_var_def] >>
  conj_tac
  >- (gen_tac >> Cases_on `op = Var src` >> simp[] >>
      Cases_on `op = Lit 32w` >> simp[]) >>
  metis_tac[]
QED

Finalise raw_log_dynamic_prepare_safety
