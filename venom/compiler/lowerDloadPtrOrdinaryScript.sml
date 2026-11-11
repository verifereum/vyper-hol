Theory lowerDloadPtrOrdinary
Ancestors
  lowerDloadPtrBlockEntry lowerDloadPtrAggregate lowerDloadPtrPhi
  lowerDloadPtrRel lowerDloadPtrCompare lowerDloadPtrStatic
  venomExecSemantics venomState venomInst ptrDiscipline
  unitShapeDefs codegenRel memLocDefs pointerConfinedDefs finite_map list pred_set

Theorem retpc_assign_input_tracked:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  MEM v i.inst_outputs /\ ~retpc_var f v /\
  i.inst_operands = [Var w] ==> ~retpc_var f w
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_assign]
QED

Theorem assign_step_success:
  i.inst_opcode = ASSIGN ==>
  (step_inst fuel C i s = OK s' <=>
   ?op out a. i.inst_operands = [op] /\ i.inst_outputs = [out] /\
     eval_operand op s = SOME a /\ s' = update_var out a s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem assign_ghost_updates:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  eval_operand op s = SOME a ==>
  step_prov PG G i (update_var out a s) = set_prov G [out] (op_prov G op) /\
  step_taint i s (update_var out a s) tn =
    tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op)
Proof
  simp[step_prov_def, out_prov_def, first_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    written_taint_def, range_bytes_def, source_memory_write_ranges_def,
    FLOOKUP_DEF, taint_component_equality] >>
  Cases_on `op_prov G op` >> simp[EXTENSION] >> metis_tac[]
QED

Theorem dload_assign_original_input_closed:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [op] ==>
  !out w. MEM out i.inst_outputs /\
    out IN (set (fn_ir_vars f) DIFF {v | retpc_var f v}) /\
    MEM (Var w) i.inst_operands ==>
    w IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})
Proof
  rpt strip_tac >> gvs[] >>
  conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  irule retpc_assign_input_tracked >> qexistsl [`i`,`out`] >> simp[]
QED

Theorem dload_boundary_core_assign_tracked:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!out w. MEM out i.inst_outputs /\ out IN V /\
    MEM (Var w) i.inst_operands ==> w IN V) /\
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
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[assign_step_success] >> strip_tac >> gvs[] >>
  `eval_operand op s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `op` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand op s` >- gvs[] >>
  rename1 `eval_operand op t = SOME b` >>
  rename1 `eval_operand op s = SOME a` >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `out IN V ==> op_taint tn op = op_taint un op /\
    dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) a b` by
    (strip_tac >>
     `!w. op = Var w ==> w IN V` by metis_tac[MEM] >>
     conj_tac >- (Cases_on `op` >> gvs[op_taint_def, dload_vars_match_def]) >>
     irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[]) >>
  drule_all assign_ghost_updates >> strip_tac >>
  qpat_x_assum `eval_operand op s = SOME a` mp_tac >>
  drule_all assign_ghost_updates >> strip_tac >> disch_tac >>
  qexists `update_var out a s` >>
  simp[assign_step_success, assign_ghost_updates] >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V
    (set_prov G [out] (op_prov G op)) (set_prov H [out] (op_prov H op))
    (tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op))
    (un with t_var := set_var_taint un.t_var [out] (op_taint un op))
    (s with <|vs_vars := (update_var out a s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out b t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >> simp[]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_assign:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  strip_tac >>
  `?op. i.inst_operands = [op]` by
    (drule_all assign_step_success >> simp[] >> metis_tac[]) >>
  irule dload_boundary_core_assign_tracked >>
  simp[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gvs[] >>
    irule retpc_assign_input_tracked >> qexistsl [`i`,`out`] >> simp[]) >>
  metis_tac[]
QED

Theorem dload_boundary_core_assign_tracked_index:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!out w. MEM out i.inst_outputs /\ out IN V /\
    MEM (Var w) i.inst_operands ==> w IN V) /\
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
  strip_tac >> drule_all dload_boundary_core_assign_tracked >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED

Theorem dload_boundary_core_assign_index:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  strip_tac >> drule_all dload_boundary_core_assign >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED

Theorem compare_pointer_operands[local]:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  (op_prov G a <> NONE \/ op_prov G b <> NONE) /\
  i.inst_operands = [a;b] ==>
  ?u w. a = Var u /\ b = Var w
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[op_prov_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem compare_operand_results[local]:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  i.inst_operands = [a;b] /\
  dload_live_layout lo sf tf fs /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) [a;b] ==> v IN V) /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME x' /\
  eval_operand b s = SOME y /\ eval_operand b t = SOME y' ==>
  (x = y <=> x' = y') /\
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_taint tn a = {} /\ op_taint tn b = {}` by
    (gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `dload_value_word fs (op_taint tn a) (op_prov G a) (op_prov H a) x x'` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM]) >>
  `dload_value_word fs (op_taint tn b) (op_prov G b) (op_prov H b) y y'` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM]) >>
  Cases_on `op_prov G a = NONE /\ op_prov G b = NONE`
  >- (Cases_on `op_prov H a` >> Cases_on `op_prov H b` >>
      gvs[dload_value_word_def, word_agree_except_bits] >>
      `x = x'` by (simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
      `y = y'` by (simp[fcpTheory.CART_EQ] >> metis_tac[]) >> simp[]) >>
  `?u w. a = Var u /\ b = Var w` by metis_tac[compare_pointer_operands] >>
  gvs[] >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  `u IN FDOM G \/ w IN FDOM G` by
    (gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `u IN FDOM G \/ w IN FDOM G ==> _` mp_tac >>
  simp[] >> strip_tac >>
  gvs[op_prov_def] >>
  Cases_on `FLOOKUP H u` >> Cases_on `FLOOKUP H w` >>
  gvs[dload_value_word_def] >>
  qpat_x_assum `~in_revert_forward _ _ ==> _` kall_tac >>
  rename1 `dload_pointer_word fs (b,sz) qx x x'` >>
  Cases_on `qx` >>
  rename1 `dload_pointer_word fs (b,sz) qy y y'` >>
  Cases_on `qy` >>
  qpat_assum `dload_pointer_word _ _ _ x x'`
    (mp_then (Pat `dload_pointer_word _ _ _ x x'`) mp_tac
      dload_pointer_word_comparisons) >>
  disch_then (drule_at (Pat `dload_pointer_word _ _ _ y y'`)) >>
  disch_then drule >> simp[]
QED

Theorem compare_step_success[local]:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) ==>
  (step_inst fuel C i s = OK s' <=>
   ?a b out x y. i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
     eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
     s' = update_var out
       (bool_to_word (if i.inst_opcode = EQ then x = y
         else if i.inst_opcode = LT then w2n x < w2n y
         else w2n y < w2n x)) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[arithmeticTheory.GREATER_DEF] >> metis_tac[]
QED

Theorem compare_ghost_updates[local]:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    written_taint_def, range_bytes_def, source_memory_write_ranges_def,
    FLOOKUP_DEF, taint_component_equality, EXTENSION] >>
  Cases_on `eval_operand a s` >> simp[] >> metis_tac[]
QED

Theorem dload_boundary_core_compare:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
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
  drule compare_step_success >>
  disch_then (qspecl_then [`t'`,`t`,`fuel`,`Ct`] mp_tac) >>
  simp[] >> strip_tac >> gnvs[] >>
  `eval_operand a s <> NONE /\ eval_operand b s <> NONE` by
    (conj_tac
     >- (drule eval_operand_definedness >>
         disch_then (qspec_then `a` mp_tac) >>
         (impl_tac >- metis_tac[MEM]) >> simp[]) >>
     drule eval_operand_definedness >>
     disch_then (qspec_then `b` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand a s` >- gvs[] >>
  Cases_on `eval_operand b s` >- gvs[] >>
  rename1 `eval_operand a s = SOME xs` >>
  rename1 `eval_operand b s = SOME ys` >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs` by
    metis_tac[dload_boundary_layout] >>
  `((xs = ys <=> x = y) /\
    (w2n xs < w2n ys <=> w2n x < w2n y) /\
    (w2n ys < w2n xs <=> w2n y < w2n x))` by
    (`!v. MEM (Var v) [a;b] ==> v IN V` by
       (simp[] >> metis_tac[]) >>
     drule_all compare_operand_results >> simp[]) >>
  qmatch_goalsub_abbrev_tac `update_var out z t` >>
  qexists `update_var out z s` >>
  conj_tac
  >- (drule compare_step_success >>
      disch_then (qspecl_then [`update_var out z s`,`s`,`fuel`,`Cs`] mp_tac) >>
      simp[Abbr `z`] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
   step_taint i s (update_var out z s) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule compare_ghost_updates >> metis_tac[]) >>
  `step_prov PH H i (update_var out z t) = set_prov H [out] NONE /\
   step_taint i t (update_var out z t) un =
     un with t_var := set_var_taint un.t_var [out] {}` by
    (irule compare_ghost_updates >> metis_tac[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    (s with <|vs_vars := (update_var out z s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out z t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >>
     simp[dload_value_word_def, word_agree_except_def]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_compare_index:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
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
  drule_all dload_boundary_core_compare >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
