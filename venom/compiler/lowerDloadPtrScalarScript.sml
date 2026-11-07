Theory lowerDloadPtrScalar
Ancestors
  lowerDloadPtrOrdinary lowerDloadPtrBlockEntry lowerDloadPtrAggregate
  lowerDloadPtrPhi lowerDloadPtrRel venomExecSemantics venomState venomInst
  ptrDiscipline unitShapeDefs codegenRel memLocDefs pointerConfinedDefs
  finite_map list pred_set

Theorem scalar_operand_no_prov[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  MEM op i.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem scalar_operand_clean[local]:
  MEM i.inst_opcode [Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by
    gvs[MEM] >>
  conj_tac >- (drule_all scalar_operand_no_prov >> simp[]) >>
  gvs[MEM, taint_ok_def] >> metis_tac[]
QED

Theorem scalar_matched_data:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. b = Var v ==> v IN V) /\ op_prov G b = NONE /\
  eval_operand b t = SOME y ==>
  ?x. eval_operand b s = SOME x /\
    op_taint tn b = op_taint un b /\ word_agree_except (op_taint tn b) x y
Proof
  strip_tac >>
  `eval_operand b s = NONE <=> eval_operand b t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  Cases_on `eval_operand b s` >- gvs[] >>
  `dload_value_word fs (op_taint tn b) (op_prov G b) (op_prov H b) x y` by
    (irule dload_matched_operand >> qexistsl [`V`,`s`,`t`,`un`] >> simp[]) >>
  Cases_on `op_prov H b` >> gvs[dload_value_word_def] >>
  Cases_on `b` >> gvs[op_taint_def, dload_vars_match_def]
QED

Theorem scalar_step_transport[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t' ==>
  ?out z. i.inst_outputs = [out] /\ t' = update_var out z t /\
    step_inst fuel Cs i s = OK (update_var out z s)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM] >> metis_tac[]
QED

Theorem out_taint_opcode_exclusion:
  ~MEM i.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; MUL; SHL; SHR; SAR] ==>
  out_taint tn i s = {}
Proof
  simp[MEM] >> strip_tac >>
  namedCases_on `i.inst_operands` ["", "a ops"] >- simp[out_taint_def] >>
  namedCases_on `ops` ["", "b rest"]
  >- (simp[out_taint_def] >> Cases_on `eval_operand a s` >> simp[]) >>
  Cases_on `rest` >> simp[out_taint_def] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem written_taint_opcode_exclusion:
  ~MEM i.inst_opcode [MSTORE; ISTORE; MCOPY] ==>
  written_taint tn i s = {}
Proof
  simp[MEM] >> strip_tac >>
  namedCases_on `i.inst_operands` ["", "a ops"] >- simp[written_taint_def] >>
  namedCases_on `ops` ["", "b rest"] >- simp[written_taint_def] >>
  namedCases_on `rest` ["", "c tail"] >- simp[written_taint_def] >>
  Cases_on `tail` >> simp[written_taint_def]
QED

Theorem scalar_ghost_updates[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s)
Proof
  strip_tac >>
  `~MEM i.inst_opcode [MSTORE; ISTORE; MCOPY]` by gvs[MEM] >>
  `written_taint tn i s = {}` by
    metis_tac[written_taint_opcode_exclusion] >>
  gvs[MEM] >>
  simp[step_prov_def, out_prov_def, step_taint_def] >>
  simp[mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def] >>
  simp[new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_scalar:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `?out z w. i.inst_outputs = [out] /\ t' = update_var out w t /\
     step_inst fuel Cs i s = OK (update_var out z s) /\
     out_taint tn i s = out_taint un i t /\
     word_agree_except (out_taint tn i s) z w` by
    (Cases_on `i.inst_opcode = MUL`
     >- (qpat_x_assum `step_inst _ Ct _ _ = _` mp_tac >>
         simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
              exec_pure2_def, AllCaseEqs()] >>
         strip_tac >> gvs[] >>
         rename1 `i.inst_operands = [a;b]` >>
         rename1 `eval_operand a t = SOME y` >>
         rename1 `eval_operand b t = SOME w` >>
         rename1 `i.inst_outputs = [out]` >>
         `!op. MEM op i.inst_operands ==> op_prov G op = NONE` by
           (rpt strip_tac >> irule scalar_operand_no_prov >> simp[] >>
            metis_tac[]) >>
         `?x. eval_operand a s = SOME x /\ op_taint tn a = op_taint un a /\
              word_agree_except (op_taint tn a) x y` by
           (irule scalar_matched_data >>
            qexistsl [`G`,`H`,`V`,`fs`,`t`] >> simp[] >> metis_tac[MEM]) >>
         `?z. eval_operand b s = SOME z /\ op_taint tn b = op_taint un b /\
              word_agree_except (op_taint tn b) z w` by
           (irule scalar_matched_data >>
            qexistsl [`G`,`H`,`V`,`fs`,`t`] >> simp[] >> metis_tac[MEM]) >>
         `op_taint tn a = {} ==> x = y` by
           (strip_tac >> `eval_operand a s = eval_operand a t` by
              (irule scalar_operand_equal >> simp[] >>
               qexistsl [`G`,`H`,`V`,`fs`,`tn`,`un`] >> simp[] >>
               metis_tac[MEM]) >>
            gvs[]) >>
         `op_taint tn b = {} ==> z = w` by
           (strip_tac >> `eval_operand b s = eval_operand b t` by
              (irule scalar_operand_equal >> simp[] >>
               qexistsl [`G`,`H`,`V`,`fs`,`tn`,`un`] >> simp[] >>
               metis_tac[MEM]) >>
            gvs[]) >>
         qexistsl [`x * z`,`y * w`] >>
         simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
              exec_pure2_def] >>
         Cases_on `op_taint tn a = {}`
         >- (Cases_on `op_taint tn b = {}`
             >- gvs[out_taint_def, word_agree_except_def] >>
             `x = 0w \/ x = 1w` by
               (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
                simp[taint_ok_def] >> strip_tac >>
                qpat_x_assum `!op. _` (qspec_then `b` mp_tac) >>
                gvs[] >> strip_tac >> gvs[]) >>
             gvs[out_taint_def, word_agree_except_def,
                 wordsTheory.WORD_MULT_CLAUSES]) >>
         `op_taint tn b = {} /\ (z = 0w \/ z = 1w)` by
           (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
            simp[taint_ok_def] >> strip_tac >>
            qpat_x_assum `!op. _` (qspec_then `a` mp_tac) >>
            gvs[] >> strip_tac >> gvs[]) >>
         gvs[out_taint_def, word_agree_except_def,
             wordsTheory.WORD_MULT_CLAUSES]) >>
     `MEM i.inst_opcode [Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
        SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by
       gvs[MEM] >>
     `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
       (rpt strip_tac >>
        `op_prov G op = NONE /\ op_taint tn op = {}` by
          (drule_all scalar_operand_clean >> simp[]) >>
        `!v. op = Var v ==> v IN V` by metis_tac[] >>
        `eval_operand op s = NONE <=> eval_operand op t = NONE` by
          (drule eval_operand_definedness >>
           disch_then (qspec_then `op` mp_tac) >>
           (impl_tac >- metis_tac[]) >> simp[]) >>
        drule_all scalar_operand_equal >> simp[]) >>
     `~MEM i.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; MUL; SHL; SHR; SAR]` by
       gvs[MEM] >>
     `out_taint tn i s = {} /\ out_taint un i t = {}` by
       metis_tac[out_taint_opcode_exclusion] >>
     drule_all scalar_step_transport >>
     disch_then (qspec_then `Cs` strip_assume_tac) >> gvs[] >>
     qexistsl [`z`,`z`] >> simp[word_agree_except_def]) >>
  gnvs[] >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
   step_taint i s (update_var out z s) tn =
     tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s)` by
    (irule scalar_ghost_updates >> simp[]) >>
  `step_prov PH H i (update_var out w t) = set_prov H [out] NONE /\
   step_taint i t (update_var out w t) un =
     un with t_var := set_var_taint un.t_var [out] (out_taint un i t)` by
    (irule scalar_ghost_updates >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s))
    (un with t_var := set_var_taint un.t_var [out] (out_taint un i t))
    (s with <|vs_vars := (update_var out z s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out w t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >>
     simp[dload_value_word_def] >> gvs[]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_scalar_index:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_boundary_core_scalar >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
