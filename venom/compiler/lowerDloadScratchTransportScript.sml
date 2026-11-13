(* Scratch trace transport and the configured active-frame budget. *)
Theory lowerDloadScratchTransport
Ancestors
  lowerDloadScratchOwnership lowerDloadExpansionGhost lowerDloadLiveAllocation
  lowerDloadSafetyAdvance lowerDloadSafetyUpdates
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyWriteBytes lowerDloadDefs
  venomExecSemantics venomState venomInst unitShapeDefs ptrDiscipline memLocDefs codegenRel finite_map pred_set list words arithmetic

Theorem ld_private_source_member:
  ld_private f d ai ==>
  MEM d (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f.lf_fn)))
Proof
  simp[ld_private_def] >> strip_tac >>
  simp[MEM_MAP, MEM_FILTER] >>
  qexists_tac `EL j (EL bi f.lf_fn.fn_blocks).bb_instructions` >> simp[] >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  qexists_tac `EL bi f.lf_fn.fn_blocks` >> metis_tac[MEM_EL]
QED

Theorem ld_site_subset_charge_bound:
  ALL_DISTINCT (MAP (\f. f.lf_fn) frames) /\
  set (MAP (\f. f.lf_fn) frames) SUBSET set C.ctx_functions /\
  EVERY (\f. f.lf_E SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f.lf_fn)))) frames ==>
  ld_charge frames <= ctx_dload_count C
Proof
  strip_tac >>
  `!f. MEM f frames ==> CARD f.lf_E <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f.lf_fn))` by
    (rpt strip_tac >> irule subset_ids_card_bound >>
     qexists_tac `\i. i.inst_id` >>
     fs[EVERY_MEM]) >>
  `SUM (MAP (\f. CARD f.lf_E) frames) <=
   SUM (MAP (\f. LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
                                   (fn_insts f.lf_fn))) frames)` by
    (qpat_x_assum `!f. MEM f frames ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Induct_on `frames` >> simp[] >> rpt strip_tac >>
     `CARD h.lf_E <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
                                    (fn_insts h.lf_fn))` by metis_tac[] >>
     `SUM (MAP (\f. CARD f.lf_E) frames) <=
      SUM (MAP (\f. LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
                                      (fn_insts f.lf_fn))) frames)` by
       (first_x_assum irule >> metis_tac[]) >> decide_tac) >>
  `SUM (MAP (\fn. LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)))
        (MAP (\f. f.lf_fn) frames)) <= ctx_dload_count C` by
    (simp[ctx_dload_count_def] >> irule sum_map_sublist_bound >> simp[]) >>
  gvs[ld_charge_def, MAP_MAP_o, combinTheory.o_DEF] >> decide_tac
QED

Theorem ld_configured_charge_bound:
  ALL_DISTINCT (MAP (\f. f.lf_fn) frames) /\
  set (MAP (\f. f.lf_fn) frames) SUBSET set C.ctx_functions /\
  EVERY (ld_maps A) frames ==>
  ld_charge frames <= ctx_dload_count C
Proof
  strip_tac >> irule ld_site_subset_charge_bound >> simp[] >>
  simp[EVERY_MEM, SUBSET_DEF] >> rpt strip_tac >>
  `ld_maps A f` by metis_tac[EVERY_MEM] >>
  `?ai. ld_private f x ai` by metis_tac[ld_maps_def] >>
  metis_tac[ld_private_source_member]
QED

Theorem ld_configured_charge_fresh_bound:
  ALL_DISTINCT (MAP (\f. f.lf_fn) (f::fs)) /\
  set (MAP (\f. f.lf_fn) (f::fs)) SUBSET set C.ctx_functions /\
  EVERY (ld_maps A) (f::fs) /\ ld_private f d ai /\ d NOTIN f.lf_E ==>
  ld_charge (f::fs) + 1 <= ctx_dload_count C
Proof
  strip_tac >>
  `EVERY (\g. g.lf_E SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g.lf_fn)))) (f::fs)` by
    (pure_rewrite_tac[EVERY_MEM, SUBSET_DEF] >>
     BETA_TAC >> qx_gen_tac `g` >> disch_tac >> qx_gen_tac `x` >> disch_tac >>
     `ld_maps A g` by (fs[EVERY_MEM]) >>
     `?aj. ld_private g x aj` by metis_tac[ld_maps_def] >>
     metis_tac[ld_private_source_member]) >>
  `FINITE f.lf_E` by
    (irule SUBSET_FINITE >>
     qexists_tac `set (MAP (\i. i.inst_id)
       (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f.lf_fn)))` >>
     gvs[]) >>
  `ld_charge ((f with lf_E := d INSERT f.lf_E)::fs) <= ctx_dload_count C` by
    (irule ld_site_subset_charge_bound >> simp[] >>
     gvs[INSERT_SUBSET] >> metis_tac[ld_private_source_member]) >>
  gvs[ld_charge_def, CARD_INSERT] >> decide_tac
QED

Theorem ld_dload_scratch_tail_transport:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a;Var z;Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ ld_prefix C fn X p 3 t0 t /\
  step_inst fuel C (EL 3 X) t = OK u ==>
  ?v. step_inst 0 C (HD X) t0 = OK v /\
    u.vs_allocas = v.vs_allocas /\ u.vs_alloca_next = v.vs_alloca_next /\
    (!lo A tn s dw.
      FLOOKUP v.vs_vars a = SOME dw /\
      ld_memory lo A tn s v /\ lo <= w2n dw /\
      (!k b c n. FLOOKUP A k = SOME (b,c,n) /\ 0 < n ==>
        c+n <= w2n dw \/ w2n dw+32 <= c) ==>
      ld_memory lo A tn s u)
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `2`] |> SRULE []) >>
  disch_then (qx_choose_then `t2` (qx_choose_then `u2` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `1`] |> SRULE []) >>
  disch_then (qx_choose_then `t1` (qx_choose_then `u1` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `tz` (qx_choose_then `u0` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  qpat_x_assum `step_inst 0 _ _ _ = OK u1` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst 0 _ _ _ = OK u2` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `step_inst fuel _ _ _ = OK u` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n dw) bytes tv` >>
  `ld_memory lo A tn s (write_memory_with_expansion (w2n dw) bytes tv)`
    suffices_by (simp[ld_memory_def] >> strip_tac >> asm_rewrite_tac[]) >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  `LENGTH bytes = 32` by simp[Abbr `bytes`, dimword_def] >>
  irule ld_memory_write_private >> simp[ADD_COMM] >>
  qpat_x_assum `ld_memory lo A tn s u0` mp_tac >>
  simp[Abbr `tv`, ld_memory_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem ld_dload_memory_frame:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  step_inst fuel C inst s = OK ss ==>
  ss.vs_memory = s.vs_memory /\
  (step_taint inst s ss tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "scratch transport has hypotheses")
  [ld_private_source_member, ld_configured_charge_bound,
   ld_dload_scratch_tail_transport, ld_dload_memory_frame];

Theorem ld_scratch_endpoint_ownership:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\ ld_private f d ai /\
  (!j. j < LENGTH (f::fs) ==>
    (EL j (f::fs)).lf_tgt.vs_alloca_next =
    (EL j (f::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (f::fs))) /\
  ld_global lo A (f::fs) /\ EVERY (ld_maps A) (f::fs) /\
  FDOM A = ld_slots A (f::fs) /\
  ld_intervals lo f.lf_tgt /\ lo <= f.lf_src.vs_alloca_next /\
  lo <= f.lf_tgt.vs_alloca_next /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE /\
  inst.inst_id = ai /\ inst.inst_outputs = [a] /\
  exec_alloca inst f.lf_tgt (32w:bytes32) = OK v /\
  ss.vs_allocas = f.lf_src.vs_allocas /\
  ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
  u.vs_allocas = v.vs_allocas /\ u.vs_alloca_next = v.vs_alloca_next /\
  (!k. k IN FRANGE H ==> k IN FDOM A) /\
  ALL_DISTINCT (MAP (\f. f.lf_fn) (f::fs)) /\
  set (MAP (\f. f.lf_fn) (f::fs)) SUBSET set C.ctx_functions /\
  g = f with <|lf_src := ss; lf_tgt := u; lf_H := H; lf_tv := tv;
                 lf_E := d INSERT f.lf_E|> ==>
  ld_global lo A (g::fs) /\ EVERY (ld_maps A) (g::fs) /\
  FDOM A = ld_slots A (g::fs) /\ ld_intervals lo u /\
  (!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
  ld_charge (g::fs) <= ctx_dload_count C /\
  (?c. FLOOKUP u.vs_allocas ai = SOME (c,32) /\ lo <= c /\
       c+32 <= u.vs_alloca_next /\
       (!k b e n. FLOOKUP A k = SOME (b,e,n) /\ 0 < n ==>
         e+n <= c \/ c+32 <= e))
Proof
  strip_tac >>
  qabbrev_tac `h = f with <|lf_tgt := v; lf_E := d INSERT f.lf_E|>` >>
  `ld_maps A f` by gvs[] >>
  `h = f with <|lf_tgt := v; lf_E := d INSERT f.lf_E|>` by
    simp[Abbr `h`] >>
  drule_all ld_scratch_alloca_ownership >> strip_tac >>
  `g = h with <|lf_src := ss; lf_tgt := u; lf_H := H; lf_tv := tv|>` by
    simp[Abbr `h`] >>
  `ld_maps A g = ld_maps A h /\
   ld_slots A (g::fs) = ld_slots A (h::fs) /\
   (!source. ld_sites (g::fs) source = ld_sites (h::fs) source) /\
   (!xs. ld_charge (g::xs) = ld_charge (h::xs)) /\
   (ld_global lo A (h::fs) ==> ld_global lo A (g::fs))` by
    (irule ld_head_allocation_update >> simp[Abbr `h`] >>
     qexistsl_tac [`H`, `ss`, `u`, `tv`] >> gvs[]) >>
  `EVERY (ld_maps A) (g::fs)` by metis_tac[EVERY_DEF] >>
  `ld_intervals lo u` by
    (pure_rewrite_tac[ld_intervals_def] >>
     qpat_assum `ld_intervals lo v` mp_tac >>
     pure_rewrite_tac[ld_intervals_def] >> metis_tac[]) >>
  qpat_x_assum `g = f with <|lf_src := ss; lf_tgt := u; lf_H := H; lf_tv := tv; lf_E := d INSERT f.lf_E|>` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))` by
    (gen_tac >> Cases_on `j`
     >- (qpat_x_assum `!j. j < LENGTH (h::fs) ==> _`
           (qspec_then `0` mp_tac) >> simp[ld_charge_def]) >>
     qpat_x_assum `!j. j < LENGTH (h::fs) ==> _`
       (qspec_then `SUC n` mp_tac) >> simp[]) >>
  `ld_charge (g::fs) <= ctx_dload_count C` by
    (irule ld_configured_charge_bound >>
     conj_tac >- (qpat_x_assum `ALL_DISTINCT (MAP _ (f::fs))` mp_tac >> simp[]) >>
     conj_tac >- (qexists_tac `A` >> asm_rewrite_tac[]) >>
     qpat_x_assum `set (MAP _ (f::fs)) SUBSET _` mp_tac >> simp[]) >>
  `ld_global lo A (g::fs)` by metis_tac[] >>
  `FDOM A = ld_slots A (g::fs)` by metis_tac[] >>
  `FLOOKUP g.lf_src.vs_allocas ai = NONE /\
   FLOOKUP g.lf_tgt.vs_allocas ai = SOME (c,32)` by simp[] >>
  `!k b e n. FLOOKUP A k = SOME (b,e,n) /\ 0 < n ==>
     e+n <= c \/ c+32 <= e` by
    (`0 < (32:num)` by decide_tac >>
     drule_all ld_private_slot_separation >> metis_tac[]) >>
  asm_rewrite_tac[] >> qexists_tac `c` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem ld_dload_scratch_exit:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a; Var z; Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ out <> a /\ out <> z /\ off <> Var a /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  eval_operand off s = SOME ow /\ eval_operand off t0 = SOME ow /\
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME basew /\
  eval_operand (Label "code_end") t0 = SOME basew /\ t0.vs_code = s.vs_code /\
  w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256) /\
  t0.vs_inst_idx = p /\ ld_prefix C' fn' X p 3 t0 t /\
  step_inst fuel C' (EL 3 X) t = OK u /\
  f.lf_src = s /\ f.lf_tgt = t0 /\ f.lf_tv = tn.t_var /\
  ld_vars P A f /\ ld_nonghost tn s t0 /\ ld_memory lo A tn s t0 /\
  MEM out (fn_ir_vars f.lf_fn) /\
  ~MEM a (fn_ir_vars f.lf_fn) /\ ~MEM z (fn_ir_vars f.lf_fn) /\
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\ ld_private f inst.inst_id ai /\
  (!j. j < LENGTH (f::fs) ==>
    (EL j (f::fs)).lf_tgt.vs_alloca_next =
    (EL j (f::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (f::fs))) /\
  ld_global lo A (f::fs) /\ EVERY (ld_maps A) (f::fs) /\
  FDOM A = ld_slots A (f::fs) /\
  ld_intervals lo s /\ ld_intervals lo t0 /\
  lo <= s.vs_alloca_next /\ lo <= t0.vs_alloca_next /\
  FLOOKUP s.vs_allocas ai = NONE /\
  ALL_DISTINCT (MAP (\f. f.lf_fn) (f::fs)) /\
  set (MAP (\f. f.lf_fn) (f::fs)) SUBSET set C.ctx_functions /\
  dload_headroom_ok C f.lf_fn inst s ==>
  ?ss v g.
    step_inst 0 C inst s = OK ss /\ step_inst 0 C' (HD X) t0 = OK v /\
    g = f with <|lf_src := ss with vs_inst_idx := SUC ss.vs_inst_idx;
                 lf_tgt := u with vs_inst_idx := SUC u.vs_inst_idx;
                 lf_H := set_prov f.lf_H [out] NONE;
                 lf_tv := (step_taint inst s ss tn).t_var;
                 lf_E := inst.inst_id INSERT f.lf_E|> /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H [out] NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_erase A o_f set_prov f.lf_H [out] NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\
    u.vs_current_bb = t0.vs_current_bb /\ u.vs_prev_bb = t0.vs_prev_bb /\
    u.vs_inst_idx = p+3 /\
    u.vs_allocas = v.vs_allocas /\ u.vs_alloca_next = v.vs_alloca_next /\
    ld_global lo A (g::fs) /\ EVERY (ld_maps A) (g::fs) /\
    FDOM A = ld_slots A (g::fs) /\
    ld_intervals lo g.lf_src /\ ld_intervals lo g.lf_tgt /\
    (!j. j < LENGTH (g::fs) ==>
      (EL j (g::fs)).lf_tgt.vs_alloca_next =
      (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
    ld_charge (g::fs) <= ctx_dload_count C /\
    (?c. FLOOKUP u.vs_allocas ai = SOME (c,32) /\ lo <= c /\
      c+32 <= u.vs_alloca_next /\
      (!k b e n. FLOOKUP A k = SOME (b,e,n) /\ 0 < n ==>
        e+n <= c \/ c+32 <= e))
Proof
  strip_tac >>
  drule_all ld_dload_expansion_ghost_exit >>
  disch_then (qspecl_then [`PG`, `C`] (qx_choose_then `ss` strip_assume_tac)) >>
  qpat_x_assum `eval_operand off s = _` kall_tac >>
  qpat_x_assum `eval_operand off t0 = _` kall_tac >>
  qpat_x_assum `code_layout_valid s` kall_tac >>
  qpat_x_assum `eval_operand (Label _) s = _` kall_tac >>
  qpat_x_assum `eval_operand (Label _) t0 = _` kall_tac >>
  qpat_x_assum `t0.vs_code = _` kall_tac >>
  qpat_x_assum `w2n ow + _ < _` kall_tac >>
  drule_all ld_dload_scratch_tail_transport >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  qexistsl_tac [`ss`, `v`] >>
  qabbrev_tac `g = f with <|lf_src := ss with vs_inst_idx := SUC ss.vs_inst_idx;
    lf_tgt := u with vs_inst_idx := SUC u.vs_inst_idx;
    lf_H := set_prov f.lf_H [out] NONE;
    lf_tv := (step_taint inst s ss tn).t_var;
    lf_E := inst.inst_id INSERT f.lf_E|>` >>
  qexists_tac `g` >>
  asm_rewrite_tac[] >> conj_tac >- suspend "memory" >>
  rpt (qpat_x_assum `ld_vars _ _ _` kall_tac) >>
  rpt (qpat_x_assum `ld_nonghost _ _ _` kall_tac) >>
  qpat_x_assum `ld_memory _ _ _ _ _` kall_tac >>
  qpat_x_assum `ld_erase _ o_f _ = _` kall_tac >>
  qpat_x_assum `ld_prefix _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = _` kall_tac >>
  qpat_x_assum `!lo A tn s dw. _` kall_tac >>
  rpt (qpat_x_assum `_.vs_params = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_current_bb = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_prev_bb = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_inst_idx = _` kall_tac) >>
  qpat_x_assum `FLOOKUP u.vs_vars out = _` kall_tac >>
  `exec_alloca (HD X) f.lf_tgt (32w:bytes32) = OK v` by
    (qpat_x_assum `step_inst 0 C' (HD X) t0 = OK v` mp_tac >>
     simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def, eval_operand_def]) >>
  `!k. k IN FRANGE (set_prov f.lf_H [out] NONE) ==> k IN FDOM A` by
    (rpt strip_tac >>
     `FRANGE (set_prov f.lf_H [out] NONE) SUBSET FRANGE f.lf_H` by
       (simp[set_prov_def, SUBSET_DEF, IN_FRANGE, FDOM_DRESTRICT, DRESTRICT_DEF] >>
        metis_tac[]) >>
     `k IN FRANGE f.lf_H` by metis_tac[SUBSET_DEF] >>
     qpat_x_assum `ld_global lo A (f::fs)` mp_tac >>
     pure_rewrite_tac[ld_global_def] >> strip_tac >>
     qpat_x_assum `!h a. MEM h _ /\ _ ==> _`
       (qspecl_then [`f`, `k`] mp_tac) >> simp[]) >>
  `ld_global lo A (g::fs) /\ EVERY (ld_maps A) (g::fs) /\
   FDOM A = ld_slots A (g::fs) /\ ld_intervals lo g.lf_tgt /\
   (!j. j < LENGTH (g::fs) ==>
     (EL j (g::fs)).lf_tgt.vs_alloca_next =
     (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
   ld_charge (g::fs) <= ctx_dload_count C /\
   (?c. FLOOKUP g.lf_tgt.vs_allocas ai = SOME (c,32) /\ lo <= c /\
     c+32 <= g.lf_tgt.vs_alloca_next /\
     (!k b e n. FLOOKUP A k = SOME (b,e,n) /\ 0 < n ==>
       e+n <= c \/ c+32 <= e))` by
    (irule ld_scratch_endpoint_ownership >>
     qexistsl_tac [`set_prov f.lf_H [out] NONE`, `a`, `inst.inst_id`, `f`, `HD X`,
       `ss with vs_inst_idx := SUC ss.vs_inst_idx`, `(step_taint inst s ss tn).t_var`, `v`] >>
     simp[Abbr `g`]) >>
  asm_rewrite_tac[] >>
  `ld_intervals lo g.lf_src` by
    (qpat_x_assum `ld_intervals lo s` mp_tac >>
     simp[ld_intervals_def, Abbr `g`]) >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `c` >>
  qpat_x_assum `FLOOKUP g.lf_tgt.vs_allocas ai = _` mp_tac >>
  qpat_x_assum `c+32 <= g.lf_tgt.vs_alloca_next` mp_tac >>
  simp[Abbr `g`] >> metis_tac[]
QED

Resume ld_dload_scratch_exit[memory]:
  rpt (qpat_x_assum `ld_vars _ _ _` kall_tac) >>
  rpt (qpat_x_assum `ld_nonghost _ _ _` kall_tac) >>
  qpat_x_assum `ld_erase _ o_f _ = _` kall_tac >>
  qpat_x_assum `ld_prefix _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `_.vs_params = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_current_bb = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_prev_bb = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_inst_idx = _` kall_tac) >>
  qpat_x_assum `FLOOKUP u.vs_vars out = _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `exec_alloca (HD X) f.lf_tgt (32w:bytes32) = OK v` by
    (qpat_x_assum `step_inst 0 C' (HD X) t0 = OK v` mp_tac >>
     simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def, eval_operand_def]) >>
  qabbrev_tac `h = f with <|lf_tgt := v; lf_E := inst.inst_id INSERT f.lf_E|>` >>
  `h = f with <|lf_tgt := v; lf_E := inst.inst_id INSERT f.lf_E|>` by simp[Abbr `h`] >>
  `ld_maps A f` by gvs[] >>
  `(HD X).inst_id = ai /\ (HD X).inst_outputs = [a] /\
   ld_intervals lo f.lf_tgt /\ lo <= f.lf_src.vs_alloca_next /\
   lo <= f.lf_tgt.vs_alloca_next /\ FLOOKUP f.lf_src.vs_allocas ai = NONE` by simp[] >>
  drule_all ld_scratch_alloca_ownership >> strip_tac >>
  `EVERY (ld_maps A) (h::fs)` by gvs[] >>
  `ALL_DISTINCT (MAP (\f. f.lf_fn) (h::fs)) /\
   set (MAP (\f. f.lf_fn) (h::fs)) SUBSET set C.ctx_functions` by
    (conj_tac
     >- (qpat_x_assum `ALL_DISTINCT (MAP _ (f::fs))` mp_tac >> simp[Abbr `h`]) >>
     qpat_x_assum `set (MAP _ (f::fs)) SUBSET _` mp_tac >> simp[Abbr `h`]) >>
  `ld_charge (h::fs) <= ctx_dload_count C` by
    (drule_all ld_configured_charge_bound >> simp[]) >>
  `v.vs_alloca_next = s.vs_alloca_next + 32 * ld_charge (h::fs)` by
    (qpat_x_assum `!j. j < LENGTH (h::fs) ==> _` (qspec_then `0` mp_tac) >>
     simp[Abbr `h`]) >>
  `c < dimword (:256)` by
    (qpat_x_assum `dload_headroom_ok _ _ _ _` mp_tac >>
     pure_rewrite_tac[dload_headroom_ok_def] >> decide_tac) >>
  `!k b e n. FLOOKUP A k = SOME (b,e,n) /\ 0 < n ==>
      e+n <= c \/ c+32 <= e` by
    (`ld_private h inst.inst_id ai` by
       (qpat_x_assum `ld_private f inst.inst_id ai` mp_tac >>
        simp[ld_private_def, Abbr `h`]) >>
     `FLOOKUP h.lf_src.vs_allocas ai = NONE /\
      FLOOKUP h.lf_tgt.vs_allocas ai = SOME (c,32)` by simp[Abbr `h`] >>
     `0 < (32:num)` by decide_tac >>
     `FDOM A = ld_slots A (h::fs)` by metis_tac[] >>
     drule_all ld_private_slot_separation >> metis_tac[]) >>
  `v.vs_memory = t0.vs_memory` by
    (qpat_x_assum `exec_alloca _ _ _ = OK v` mp_tac >>
     qpat_x_assum `f.lf_tgt = t0` (fn th => pure_rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >>
     simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >> gvs[AllCaseEqs(), update_var_def]) >>
  `ss.vs_memory = s.vs_memory /\ (step_taint inst s ss tn).t_mem = tn.t_mem` by
    (drule_all ld_dload_memory_frame >> simp[]) >>
  `ld_memory lo A (step_taint inst s ss tn) ss v` by
    (qpat_x_assum `ld_memory lo A tn s t0` mp_tac >>
     simp[ld_memory_def] >> metis_tac[]) >>
  qpat_x_assum `!lo A tn s dw. _` irule >>
  asm_rewrite_tac[] >> qexists_tac `n2w c : bytes32` >> simp[w2n_n2w] >> metis_tac[]
QED

Finalise ld_dload_scratch_exit

val _ = if null (hyp ld_dload_scratch_exit) then () else
  raise Fail "scratch exit has hypotheses";

