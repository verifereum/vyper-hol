(* Correlated public-copy byte and ghost effects. *)
Theory lowerDloadPublicEffect
Ancestors
  lowerDloadPublicTrace lowerDloadCodeDataBytes lowerDloadSafetyWriteBytes
  lowerDloadSafetyEmptyCopy lowerDloadExpansionGhost lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadSafetyAmbient lowerDloadOracleCallAssembly regularCallEmitSim ptrDiscipline venomWf codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst memLocDefs finite_map pred_set list words arithmetic

Theorem ld_dloadbytes_taint:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [d;r;n] /\
  inst.inst_outputs = [] /\ eval_operand d s = SOME dst /\
  eval_operand r s = SOME off /\
  eval_operand n s = SOME len /\ ss.vs_allocas = s.vs_allocas /\
  ss.vs_fmp = s.vs_fmp ==>
  step_taint inst s ss tn =
    tn with t_mem := tn.t_mem DIFF {w2n dst+j | j < w2n len}
Proof
  strip_tac >>
  `{i | w2n dst <= i /\ i < w2n dst+w2n len} =
   {w2n dst+j | j < w2n len}` by
    (simp[EXTENSION] >> qx_gen_tac `i` >> eq_tac
     >- (strip_tac >> qexists_tac `i-w2n dst` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       taint_component_equality, FLOOKUP_DEF, DRESTRICT_UNIV,
       fixed_source_write_range_def, sized_source_write_range_def] >>
  gvs[EXTENSION, SF CONJ_ss]
QED

Theorem ld_dloadbytes_outputs:
  fn_inst_wf fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DLOADBYTES ==> inst.inst_outputs = []
Proof
  simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> strip_tac >>
  `inst_wf inst` by metis_tac[] >>
  qpat_x_assum `!bb inst. _` kall_tac >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def, opcode_case_def]
QED

Theorem ld_empty_outputs_prov:
  inst.inst_outputs = [] ==> step_prov PG G inst ss = G
Proof
  simp[step_prov_def, set_prov_def, DRESTRICT_UNIV]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "public effect has hypotheses")
  [ld_dloadbytes_taint, ld_dloadbytes_outputs, ld_empty_outputs_prov];

Theorem ld_public_copy_memory:
  ld_memory lo A tn s t /\ LENGTH bytes = n /\
  (n = 0 \/ (d = d' /\ d+n <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     d = b+delta /\ d' = c+delta /\ delta+n <= sz)) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> lo <= b /\ lo <= c) /\
  (!k k' b c sz b' c' sz'.
    FLOOKUP A k = SOME (b,c,sz) /\ FLOOKUP A k' = SOME (b',c',sz') /\
    k <> k' /\ 0 < sz /\ 0 < sz' ==>
    (b+sz <= b' \/ b'+sz' <= b) /\ (c+sz <= c' \/ c'+sz' <= c)) /\
  tn'.t_mem = tn.t_mem DIFF {d+j | j < n} ==>
  ld_memory lo A tn'
    (write_memory_with_expansion d bytes s)
    (write_memory_with_expansion d' bytes t)
Proof
  strip_tac
  >- (gvs[ld_memory_def, ld_empty_write_read_byte] >> metis_tac[])
  >- (gvs[] >> irule (ld_memory_write_low |> Q.INST [`M` |-> `{}`]) >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`LENGTH bytes`,`tn`] >> simp[])
  >> gvs[] >>
  irule (ld_memory_write_slot |> Q.INST [`M` |-> `{}`]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`k`,`LENGTH bytes`,`sz`,`tn`] >>
  simp_tac (srw_ss()) [GSYM ADD_ASSOC] >> metis_tac[]
QED

Theorem ld_public_add_prefix_state:
  X = [<|inst_id := ai; inst_opcode := ADD;
         inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>; ci] /\
  ld_prefix C fn X p 1 t0 t1 ==>
  ?w. t1 = (update_var z w t0) with vs_inst_idx := p+1
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `v` (qx_choose_then `u` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  qpat_x_assum `step_inst 0 _ _ _ = OK u` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qexists_tac `v1+v2` >> simp[ADD1]
QED

Theorem ld_sync_dloadbytes_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  ptr_discipline lo C vs0 /\ mem_inv dload_offset_ok C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  ld_prefix C' fn' X p 1 t0 t1 /\ step_inst fuel C' (EL 1 X) t1 = OK u ==>
  ?ss H' G' tn'.
    step_inst 0 C inst s = OK ss /\
    tn' = step_taint inst s ss tn /\ G' = step_prov PG G inst ss /\
    G' = ld_erase A o_f H' /\ (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
                         lf_H := H'; lf_tv := tn'.t_var|>) /\
    ld_memory lo A tn' ss u /\ ld_nonghost tn' ss u /\
    ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t0.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t0.vs_alloca_next /\
    ss.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = p+1 /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_current_bb = t0.vs_current_bb /\ u.vs_prev_bb = t0.vs_prev_bb
Proof
  strip_tac >> drule_all ld_sync_dloadbytes_trace_evaluations >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  `fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_sync_source, ld_active_inst_member] >>
  `inst.inst_outputs = []` by metis_tac[ld_dloadbytes_outputs] >>
  `step_inst_base (EL 1 X) t1 = OK u` by
    (qpat_x_assum `step_inst fuel _ _ _ = OK u` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `((EL 1 X).inst_opcode = CODECOPY) /\
   (EL 1 X).inst_operands = [dest;Var z;len]` by simp[] >>
  drule_all ld_dloadbytes_codecopy_payload >> strip_tac >>
  `?w. t1 = (update_var z w t0) with vs_inst_idx := p+1` by
    (qpat_assum `ld_prefix _ _ _ _ _ _ _`
       (mp_then (Pat `ld_prefix _ _ _ _ _ _ _`) mp_tac ld_public_add_prefix_state) >>
     simp[]) >>
  `step_taint inst s ss tn =
    tn with t_mem := tn.t_mem DIFF {w2n dw+j | j < w2n nw}` by
    (irule ld_dloadbytes_taint >> simp[write_memory_with_expansion_def] >>
     metis_tac[]) >>
  qexistsl_tac [`ss`,`f.lf_H`] >>
  simp[ld_empty_outputs_prov, step_inst_non_invoke] >>
  conj_tac >- (rpt strip_tac >> irule ld_global_selected >>
    qexistsl_tac [`f`,`f::fs`,`lo`] >> simp[]) >>
  conj_tac >- suspend "observations_vars" >>
  conj_tac >- suspend "memory" >>
  conj_tac >- suspend "observations_nonghost" >>
  simp[write_memory_with_expansion_def, update_var_def]
QED

Resume ld_sync_dloadbytes_effect[observations_vars]:
  `f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H; lf_tv := tn.t_var|> =
   f with <|lf_src := ss; lf_tgt := u|>` by
    simp[ld_frame_component_equality] >>
  `f with <|lf_H := f.lf_H; lf_tv := tn.t_var|> = f` by
    simp[ld_frame_component_equality] >>
  asm_rewrite_tac[] >>
  irule ld_vars_observation_cong >>
  simp[write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `z = v` >> gvs[]
QED
Resume ld_sync_dloadbytes_effect[memory]:
  drule_all ld_sync_dloadbytes_destination_cases >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `ld_memory lo A tn s t1` by
    (qpat_x_assum `ld_memory lo A tn s t0` mp_tac >>
     simp[ld_memory_def, update_var_def] >> strip_tac >> asm_rewrite_tac[]) >>
  irule ld_public_copy_memory >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w2n nw`,`tn`] >>
  simp[ADD_COMM] >> metis_tac[]
QED
Resume ld_sync_dloadbytes_effect[observations_nonghost]:
  gvs[write_memory_with_expansion_def, update_var_def, ld_nonghost_def]
QED
Finalise ld_sync_dloadbytes_effect

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "public effect has hypotheses")
  [ld_public_copy_memory, ld_public_add_prefix_state, ld_sync_dloadbytes_effect];
