Theory lowerDloadPtrShift
Ancestors
  lowerDloadPtrScalar lowerDloadPtrOrdinary lowerDloadPtrPhi
  lowerDloadPtrRel lowerDloadPtrAggregate lowerDloadPtrBlockEntry
  ptrDiscipline venomExecSemantics venomState venomInst
  unitShapeDefs codegenRel memLocDefs pointerConfinedDefs finite_map list pred_set

Theorem shift_operand_safety[local]:
  MEM i.inst_opcode [SHL; SHR; SAR] /\ i.inst_operands = [a;b] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s ==>
  op_prov G a = NONE /\ op_prov G b = NONE /\ op_taint tn a = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  conj_asm1_tac
  >- (Cases_on `a` >>
      gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def, op_prov_def,
          FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `b` >>
      gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def, op_prov_def,
          FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[MEM, taint_ok_def] >> metis_tac[]
QED

Theorem shift_step_success[local]:
  MEM i.inst_opcode [SHL; SHR; SAR] ==>
  (step_inst fuel C i t = OK t' <=>
   ?a b x y out. i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
     eval_operand a t = SOME x /\ eval_operand b t = SOME y /\
     t' = update_var out
       (if i.inst_opcode = SHL then word_lsl y (w2n x)
        else if i.inst_opcode = SHR then word_lsr y (w2n x)
        else word_asr y (w2n x)) t)
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem shift_ghost_updates[local]:
  MEM i.inst_opcode [SHL; SHR; SAR] /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  eval_operand a s = SOME x ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out]
      (shift_taint i.inst_opcode (w2n x) (op_taint tn b))
Proof
  strip_tac >> gvs[MEM] >>
  simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    written_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_shift:
  MEM i.inst_opcode [SHL; SHR; SAR] /\
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
  drule shift_step_success >> disch_then (drule o iffLR) >>
  strip_tac >> gnvs[] >>
  `MEM i.inst_opcode [SHL; SHR; SAR]` by simp[MEM] >>
  `op_prov G a = NONE /\ op_prov G b = NONE /\ op_taint tn a = {}` by
    (irule shift_operand_safety >> metis_tac[MEM]) >>
  `!v. a = Var v ==> v IN V` by metis_tac[] >>
  `eval_operand a s = NONE <=> eval_operand a t = NONE` by
    (drule_all dload_matched_operand_defined >> simp[]) >>
  `eval_operand a s = eval_operand a t` by
    (drule_all scalar_operand_equal >> simp[]) >>
  `?w. eval_operand b s = SOME w /\ op_taint tn b = op_taint un b /\
       word_agree_except (op_taint tn b) w y` by
    (irule scalar_matched_data >>
     qexistsl [`G`,`H`,`V`,`fs`,`t`] >> simp[] >> metis_tac[MEM]) >>
  qexists `update_var out
    (if i.inst_opcode = SHL then word_lsl w (w2n x)
     else if i.inst_opcode = SHR then word_lsr w (w2n x)
     else word_asr w (w2n x)) s` >>
  conj_tac >- (drule shift_step_success >> disch_then (irule o iffRL) >>
    qexistsl [`a`,`b`,`x`,`w`,`out`] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule update_var_definedness >>
    qexists `U` >> simp[]) >>
  `word_agree_except (shift_taint i.inst_opcode (w2n x) (op_taint tn b))
    (if i.inst_opcode = SHL then word_lsl w (w2n x)
     else if i.inst_opcode = SHR then word_lsr w (w2n x)
     else word_asr w (w2n x))
    (if i.inst_opcode = SHL then word_lsl y (w2n x)
     else if i.inst_opcode = SHR then word_lsr y (w2n x)
     else word_asr y (w2n x))` by
    (gvs[] >> metis_tac[word_agree_except_shl, word_agree_except_shr,
                       word_agree_except_sar]) >>
  qmatch_goalsub_abbrev_tac `update_var out zs s` >>
  qmatch_goalsub_abbrev_tac `update_var out zt t` >>
  `step_prov PG G i (update_var out zs s) = set_prov G [out] NONE /\
   step_taint i s (update_var out zs s) tn =
     tn with t_var := set_var_taint tn.t_var [out]
       (shift_taint i.inst_opcode (w2n x) (op_taint tn b))` by
    (irule shift_ghost_updates >> simp[]) >>
  `step_prov PH H i (update_var out zt t) = set_prov H [out] NONE /\
   step_taint i t (update_var out zt t) un =
     un with t_var := set_var_taint un.t_var [out]
       (shift_taint i.inst_opcode (w2n x) (op_taint un b))` by
    (irule shift_ghost_updates >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out]
      (shift_taint i.inst_opcode (w2n x) (op_taint tn b)))
    (un with t_var := set_var_taint un.t_var [out]
      (shift_taint i.inst_opcode (w2n x) (op_taint un b)))
    (s with <|vs_vars := (update_var out zs s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out zt t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >>
     simp[dload_value_word_def, Abbr `zs`, Abbr `zt`] >> metis_tac[]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_shift_index:
  MEM i.inst_opcode [SHL; SHR; SAR] /\
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
  drule_all dload_boundary_core_shift >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
