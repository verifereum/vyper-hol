Theory lowerDloadPtrAffine
Ancestors
  lowerDloadPtrOrdinary lowerDloadPtrRel lowerDloadPtrJointNext
  lowerDloadPtrBlockEntry lowerDloadPtrAggregate lowerDloadPtrPhi
  lowerDloadPtrCall lowerDloadPtrStatic contextCodegenRel irSupply
  ptrDiscipline pointerConfinedDefs venomExecSemantics venomState venomInst
  instIdxIndep memLocDefs codegenRel list words finite_map pred_set arithmetic

Theorem dload_pointer_word_affine[local]:
  dload_pointer_word fs p q x y ==>
  dload_pointer_word fs p q (x+z) (y+z) /\
  dload_pointer_word fs p q (z+x) (z+y) /\
  dload_pointer_word fs p q (x-z) (y-z)
Proof
  PairCases_on `p` >> PairCases_on `q` >>
  simp[dload_pointer_word_def] >> strip_tac >> simp[] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem affine_step_success[local]:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) ==>
  (step_inst fuel C i s = OK s' <=>
   ?a b out x y. i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
     eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
     s' = update_var out (if i.inst_opcode = ADD then x+y else x-y) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem affine_provenance_exclusions[local]:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  i.inst_operands = [a;b] ==>
  (op_prov G a = NONE \/ op_prov G b = NONE) /\
  (i.inst_opcode = SUB ==> op_prov G b = NONE)
Proof
  strip_tac >>
  `affine_pointer_ops f (ptr_roots P f)` by metis_tac[fn_ptr_ok_def] >>
  gvs[affine_pointer_ops_def, GSYM fn_pv_def, fn_insts_def,
      o1PassContractTheory.fn_insts_blocks_MEM] >>
  first_x_assum (drule_at (Pat `MEM _ _.bb_instructions`)) >>
  simp[] >> strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem dload_affine_value[local]:
  dload_value_word fs {} p p' x x' /\
  dload_value_word fs {} q q' y y' /\
  (p = NONE \/ q = NONE) /\ (~isadd ==> q = NONE) ==>
  dload_value_word fs {}
    (case p of NONE => q | SOME site => SOME site)
    (case p' of NONE => q' | SOME site => SOME site)
    (if isadd then x+y else x-y) (if isadd then x'+y' else x'-y')
Proof
  `!a b:bytes32. word_agree_except {} a b <=> a = b` by
    simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
  Cases_on `isadd` >>
  Cases_on `p` >> Cases_on `p'` >> Cases_on `q` >> Cases_on `q'` >>
  simp[dload_value_word_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[dload_pointer_word_affine, WORD_ADD_COMM]
QED

Theorem affine_operand_result[local]:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ i.inst_operands = [a;b] /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) [a;b] ==> v IN V) /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME x' /\
  eval_operand b s = SOME y /\ eval_operand b t = SOME y' ==>
  dload_value_word fs {} (first_prov G [a;b]) (first_prov H [a;b])
    (if i.inst_opcode = ADD then x+y else x-y)
    (if i.inst_opcode = ADD then x'+y' else x'-y')
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
  drule_all affine_provenance_exclusions >> disch_then assume_tac >>
  `first_prov G [a;b] = (case op_prov G a of NONE => op_prov G b | SOME p => SOME p)` by
    (simp[first_prov_def] >> Cases_on `op_prov G a` >> Cases_on `op_prov G b` >> simp[]) >>
  `first_prov H [a;b] = (case op_prov H a of NONE => op_prov H b | SOME p => SOME p)` by
    (simp[first_prov_def] >> Cases_on `op_prov H a` >> Cases_on `op_prov H b` >> simp[]) >>
  simp[] >> irule (SRULE [] dload_affine_value) >> simp[] >> metis_tac[]
QED

Theorem affine_ghost_updates[local]:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] (first_prov G [a;b]) /\
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

Theorem dload_boundary_core_affine:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
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
  drule affine_step_success >>
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
  `dload_value_word fs {} (first_prov G [a;b]) (first_prov H [a;b])
     (if i.inst_opcode = ADD then xs+ys else xs-ys)
     (if i.inst_opcode = ADD then x+y else x-y)` by
    (irule affine_operand_result >> simp[] >>
     goal_assum (drule_at (Pat `dload_vars_match _ _ _ _ _ _ _ _`)) >> simp[] >> metis_tac[MEM]) >>
  qmatch_goalsub_abbrev_tac `update_var out z t` >>
  qabbrev_tac `w = if i.inst_opcode = ADD then xs+ys else xs-ys` >>
  qexists `update_var out w s` >>
  conj_tac
  >- (drule affine_step_success >>
      disch_then (qspecl_then [`update_var out w s`,`s`,`fuel`,`Cs`] mp_tac) >>
      simp[Abbr `w`] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `step_prov PG G i (update_var out w s) = set_prov G [out] (first_prov G [a;b]) /\
   step_taint i s (update_var out w s) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule affine_ghost_updates >> metis_tac[]) >>
  `step_prov PH H i (update_var out z t) = set_prov H [out] (first_prov H [a;b]) /\
   step_taint i t (update_var out z t) un =
     un with t_var := set_var_taint un.t_var [out] {}` by
    (irule affine_ghost_updates >> metis_tac[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V
    (set_prov G [out] (first_prov G [a;b])) (set_prov H [out] (first_prov H [a;b]))
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    (s with <|vs_vars := (update_var out w s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out z t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >> gvs[Abbr `w`, Abbr `z`]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_actual_affine_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> ~retpc_var f v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venomStateTheory.venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN {v | ~retpc_var f v} /\ v IN set (fn_ir_vars f)` by
    (simp[] >> metis_tac[fn_ir_vars_operand]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) dload_boundary_core_affine >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
