(* External code is not a memory source: only the destination is covered. *)
Theory bodyPtrCodeSliceExternalCopy
Ancestors
  bodyPtrCodeSliceSelfSuffix fragExecPtr fragGasSeqPtr ptrDiscipline
  venomExecSemantics venomInst venomState codegenRel words list finite_map
  lowerDloadPtrExpansionTransport bodyPtrDefs ptrSafeRun memLocDefs contextCodegenRel

Theorem ptr_inst_ok_extcodecopy:
  !D ctx fn G tn s id dst addr src len a b n fuel t.
    ptr_covers G tn dst s (w2n n) /\
    eval_operand addr s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand len s = SOME n /\
    op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s = OK t ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s
Proof
  rpt strip_tac >>
  `access_ok 0 G fn (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s /\
   taint_ok fn tn (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s` by
    (gvs[ptr_covers_def] >>
     simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, sized_source_write_range_def,
          mem_write_ops_def, mem_read_ops_def, op_prov_def, mk_inst_def,
          eval_operand_def] >>
     metis_tac[]) >>
  simp[ptr_inst_ok_def, allocas_from_def, step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  gvs[ptr_covers_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       write_memory_with_expansion_def] >> rpt strip_tac >> gvs[]
QED

Theorem external_code_copy_state_ghost:
  !PG G tn id addr dst src len s t a b c n.
    eval_operand addr s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand src s = SOME c /\ eval_operand len s = SOME n /\
    step_inst_base (mk_inst id EXTCODECOPY [addr;dst;src;len] []) s = OK t ==>
    t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels /\
    step_prov PG G (mk_inst id EXTCODECOPY [addr;dst;src;len] []) t = G /\
    step_taint (mk_inst id EXTCODECOPY [addr;dst;src;len] []) s t tn =
      tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+w2n n}
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >> strip_tac >> gvs[] >>
  simp[write_memory_with_expansion_def, step_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, new_site_bytes_def, finite_mapTheory.DRESTRICT_UNIV,
       taint_component_equality, finite_mapTheory.FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem external_code_copy_store_checked:
  !D ctx fn PG G tn s t id sid dst out addr src len a c n p b.
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
    eval_operand addr s = SOME a /\ eval_operand src s = SOME c /\
    eval_operand len s = SOME n /\
    lookup_var out s = SOME p /\ lookup_var dst s = SOME b /\
    op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s = OK t ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id EXTCODECOPY [addr;Var dst;src;len] [];
       mk_inst sid MSTORE [Var out;len] []] s G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n b <= j /\ j < w2n b+w2n n}) DIFF
        {j | w2n p <= j /\ j < w2n p+32})
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s` by
    (irule ptr_inst_ok_extcodecopy >> metis_tac[]) >>
  `t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels /\
   step_prov PG G (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) t = G /\
   step_taint (mk_inst id EXTCODECOPY [addr;Var dst;src;len] []) s t tn =
     tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+w2n n}` by
    (irule external_code_copy_state_ghost >>
     simp[eval_operand_def] >> metis_tac[]) >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok _ _ _ _ _ _ un _ u` >>
  `lookup_var out u = SOME p /\ eval_operand len u = SOME n` by
    (Cases_on `len` >> gvs[Abbr `u`, lookup_var_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G un (mk_inst sid MSTORE [Var out;len] []) u` by
    (irule ptr_inst_ok_mstore >>
     gvs[Abbr `un`, Abbr `u`, ptr_covers_def, op_taint_def, lookup_var_def]) >>
  simp[] >>
  `step_inst_base (mk_inst sid MSTORE [Var out;len] []) u =
    OK (mstore (w2n p) n u)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  simp[] >>
  `step_prov PG G (mk_inst sid MSTORE [Var out;len] []) (mstore (w2n p) n u) = G /\
   step_taint (mk_inst sid MSTORE [Var out;len] []) u (mstore (w2n p) n u) un =
    un with t_mem := un.t_mem DIFF {j | w2n p <= j /\ j < w2n p+32}` by
    (irule exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame >>
     gvs[Abbr `un`, op_taint_def]) >>
  gvs[Abbr `u`, Abbr `un`, inst_seq_ptr_def]
QED
