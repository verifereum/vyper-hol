Theory o1LowerDloadSuppliedSegmentTransport
Ancestors
  o1LowerDloadSuppliedSegmentExec o1LowerDloadSuppliedSegmentControl
  o1LowerDloadSuppliedSegmentInputs o1LowerDloadSuppliedSegmentEnvironment
  o1LowerDloadScratchExtension o1LowerDloadScratchMemory
  o1LowerDloadJointRangeCopy o1LowerDloadRangeTransport
  o1LowerDloadJointRelation o1LowerDloadOccurrence ptrDiscipline
  o1PassContract memLocDefs codegenRel venomExecSemantics words finite_map list
  unitShapeDefs venomState irSupply lowerDloadDefs o1LowerDloadShared
  o1LowerDloadEnvironment pred_set

Theorem ld_joint_dloadbytes_destination:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
  eval_operand sz s = SOME z ==>
  ?q. eval_operand dst t = SOME q /\
    (w2n z = 0 \/ (w2n p = w2n q /\ w2n p + w2n z <= lo) \/
     (?id b c k j. FLOOKUP sites id = SOME (b,c,k) /\
       j + w2n z <= k /\ w2n p = b+j /\ w2n q = c+j))
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn dst = {}` by
    metis_tac[ld_data_load_inputs_untainted, MEM] >>
  `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
  drule ld_joint_write_operand_range >> disch_then irule >> simp[] >>
  simp[mem_write_ops_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, sized_source_write_range_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem ld_joint_supply_dloadbytes_transport:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  inst.inst_outputs = [] /\ step_inst fuel C inst s = OK s1 /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
  eval_operand sz s = SOME z /\
  fresh_ir_var u = (bv,u1) /\ lower_dload_inst_supply u inst = (es,u') /\
  ~MEM bv (fn_ir_vars fn) /\ dst <> Var bv /\ sz <> Var bv /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) ==>
  ?q. eval_operand dst t = SOME q /\
    let t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t;
        t3 = write_memory_with_expansion (w2n q)
          (TAKE (w2n z) (DROP (w2n x) t.vs_data_section ++ REPLICATE (w2n z) 0w)) t2
    in LENGTH es = 2 /\ step_inst fuel C' (EL 0 es) t = OK t2 /\
       step_inst fuel C' (EL 1 es) t2 = OK t3 /\
       ld_env_agree sites fn (occurrence_step a HP H inst s1)
         (step_taint inst s s1 tn) s1 t3 /\
       ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
         s1.vs_memory t3.vs_memory
Proof
  strip_tac >>
  drule_all ld_joint_dloadbytes_destination >>
  disch_then (qx_choose_then `q` assume_tac) >>
  `eval_operand src t = SOME x /\ eval_operand sz t = SOME z` by
    (drule ld_joint_dloadbytes_inputs_clean >> simp[] >> metis_tac[]) >>
  `s.vs_data_section = t.vs_data_section` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `s1 = write_memory_with_expansion (w2n p)
    (TAKE (w2n z) (DROP (w2n x) t.vs_data_section ++ REPLICATE (w2n z) 0w)) s` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> simp[]) >>
  `eval_operand dst t = SOME q` by metis_tac[] >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_supply_dloadbytes_exact)) >>
  disch_then (qspecl_then [`fuel`,`C'`] strip_assume_tac) >>
  qexists_tac `q` >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n q) bs tmp` >>
  conj_tac
  >- (drule ld_joint_environment >> strip_tac >>
      drule ld_env_supply_dloadbytes >> disch_then irule >>
      simp[write_memory_with_expansion_def] >>
      qexistsl_tac [`bv`,`x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)`] >>
      simp[Abbr `tmp`]) >>
  `LENGTH bs = w2n z` by simp[Abbr `bs`, LENGTH_TAKE_EQ] >>
  `ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def] >>
  `tmp.vs_memory = t.vs_memory` by simp[Abbr `tmp`, update_var_def] >>
  `(step_taint inst s (write_memory_with_expansion (w2n p) bs s) tn).t_mem =
    tn.t_mem DIFF {i | w2n p <= i /\ i < w2n p + LENGTH bs}` by
    (simp[step_taint_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, sized_source_write_range_def,
          written_taint_def, new_site_bytes_def, range_bytes_def,
          write_memory_with_expansion_def, FLOOKUP_DEF] >>
     simp[EXTENSION] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  Cases_on `w2n z = 0`
  >- (`bs = []` by metis_tac[LENGTH_NIL] >>
      simp[] >> irule ld_memory_agree_empty_write >> simp[]) >>
  qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[GSYM th]) >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_clean_write >>
  disch_then irule >> simp[] >> metis_tac[w2n_11]
QED

Theorem ld_joint_supply_dload_transport:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s1 /\
  eval_operand off s = SOME x /\
  fresh_ir_var u = (av,u1) /\ fresh_ir_var u1 = (bv,u2) /\
  lower_dload_inst_supply u inst = (es,u') /\ off <> Var av /\
  ~MEM av (fn_ir_vars fn) /\ ~MEM bv (fn_ir_vars fn) /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) /\
  ((FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE /\ b = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas (EL 0 es).inst_id = SOME (b,32)) /\
  b+32 < dimword(:256) /\
  ld_joint_geometry sites X1 lo owners /\
  FLOOKUP X1 key = SOME ((EL 0 es).inst_id,b) ==>
  let t1 = update_var av (n2w b)
        (if FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE then
           t with <|vs_allocas := t.vs_allocas |+ ((EL 0 es).inst_id,(b,32));
                    vs_alloca_next := t.vs_alloca_next+32|>
         else t);
      t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t1;
      bs = TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w);
      t3 = write_memory_with_expansion b bs t2;
      t4 = update_var out (word_of_bytes T (0w:bytes32) bs) t3
  in LENGTH es = 4 /\
     step_inst fuel C' (EL 0 es) t = OK t1 /\
     step_inst fuel C' (EL 1 es) t1 = OK t2 /\
     step_inst fuel C' (EL 2 es) t2 = OK t3 /\
     step_inst fuel C' (EL 3 es) t3 = OK t4 /\
     ld_env_agree sites fn (occurrence_step a HP H inst s1)
       (step_taint inst s s1 tn) s1 t4 /\
     ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
       s1.vs_memory t4.vs_memory
Proof
  strip_tac >> (
  `eval_operand off t = SOME x` by
    (drule ld_joint_dload_inputs_clean >> simp[] >> metis_tac[]) >>
  `s.vs_data_section = t.vs_data_section` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `s1 = update_var out (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w))) s` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[exec_read1_def, bind_outputs_def]) >>
  rule_assum_tac (REWRITE_RULE [EL]) >>
  drule_at (Pat `lower_dload_inst_supply _ _ = _`)
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_supply_dload_exact)) >>
  disch_then (drule_at (Pat `code_layout_valid _`)) >>
  disch_then (drule_at (Pat `fresh_ir_var _ = _`)) >>
  disch_then (drule_at (Pat `fresh_ir_var _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`,`C'`] strip_assume_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion addr bs tmp` >>
  conj_tac
  >- (drule ld_joint_environment >> strip_tac >>
      drule ld_env_supply_dload >> disch_then irule >> simp[] >>
      qexistsl_tac [`av`,`bv`,`n2w addr`,`word_of_bytes T (0w:bytes32) bs`,
        `x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)`] >>
      simp[Abbr `tmp`, update_var_def, write_memory_with_expansion_def]) >>
  `(step_taint inst s (update_var out (word_of_bytes T (0w:bytes32) bs) s) tn).t_mem =
    tn.t_mem` by
    (simp[step_taint_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, written_taint_def,
          new_site_bytes_def, update_var_def, range_bytes_def, FLOOKUP_DEF] >>
     simp[EXTENSION] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `ld_memory_agree sites lo tn.t_mem s.vs_memory tmp.vs_memory` by
    (simp[Abbr `tmp`, update_var_def] >> fs[ld_joint_boundary_def]) >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_scratch_write >>
  disch_then irule >> simp[Abbr `bs`, LENGTH_TAKE_EQ] >>
  metis_tac[])
QED
