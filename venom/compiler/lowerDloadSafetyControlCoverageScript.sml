(* Correlated owned coverage after a branch and its PHI entry. *)
Theory lowerDloadSafetyControlCoverage
Ancestors
  lowerDloadSafetyControl lowerDloadSafetyEntry lowerDloadSafetyOrdinaryCoverage
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyAdvance ptrDiscipline o1PassContract
  unitShapeDefs venomExecProofs venomState venomInst finite_map list pred_set

(* The ghost relation between a selected erasure Ke and the live
   provenance G: G agrees wherever Ke is defined, and holds nothing or a
   dynamic site elsewhere. A write and a PHI entry keep it. *)
Theorem ld_ghost_rel_set_prov[local]:
  (!v x. FLOOKUP Ke v = SOME x ==> FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP Ke v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) /\
  (!x. po = SOME x ==> po' = SOME x) /\
  (po = NONE ==>
     po' = NONE \/ ?b z. po' = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!v x. FLOOKUP (set_prov Ke outs po) v = SOME x ==>
     FLOOKUP (set_prov G outs po') v = SOME x) /\
  (!v. FLOOKUP (set_prov Ke outs po) v = NONE ==>
     FLOOKUP (set_prov G outs po') v = NONE \/
     ?b z. FLOOKUP (set_prov G outs po') v = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  strip_tac >>
  Cases_on `outs`
  >- (simp[set_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t`
  >- (Cases_on `po` >> Cases_on `po'` >>
      gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      rw[] >> gvs[] >> metis_tac[]) >>
  Cases_on `po` >> Cases_on `po'` >>
  gvs[set_prov_def, FLOOKUP_DRESTRICT] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem ld_ghost_rel_phi_prov[local]:
  (!v x. FLOOKUP Ke v = SOME x ==> FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP Ke v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!x. phi_prov prev Ke inst = SOME x ==> phi_prov prev G inst = SOME x) /\
  (phi_prov prev Ke inst = NONE ==>
     phi_prov prev G inst = NONE \/
     ?b z. phi_prov prev G inst = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  strip_tac >> simp[phi_prov_def] >>
  Cases_on `prev` >> simp[] >> rename1 `resolve_phi lbl _` >>
  Cases_on `resolve_phi lbl inst.inst_operands` >> simp[] >>
  rename1 `op_prov Ke op` >> Cases_on `op` >> simp[op_prov_def] >>
  metis_tac[]
QED

Theorem ld_ghost_rel_phis[local]:
  (!v x. FLOOKUP Ke v = SOME x ==> FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP Ke v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  !insts.
    (!v x. FLOOKUP (phis_prov prev Ke insts) v = SOME x ==>
       FLOOKUP (phis_prov prev G insts) v = SOME x) /\
    (!v. FLOOKUP (phis_prov prev Ke insts) v = NONE ==>
       FLOOKUP (phis_prov prev G insts) v = NONE \/
       ?b z. FLOOKUP (phis_prov prev G insts) v = SOME (b,z) /\ fl <= b /\
             b + z < dimword (:256))
Proof
  strip_tac >> Induct >- (simp[phis_prov_def] >> metis_tac[]) >>
  gen_tac >> pop_assum strip_assume_tac >>
  `(!x. phi_prov prev Ke h = SOME x ==> phi_prov prev G h = SOME x) /\
   (phi_prov prev Ke h = NONE ==>
      phi_prov prev G h = NONE \/
      ?b z. phi_prov prev G h = SOME (b,z) /\ fl <= b /\
            b + z < dimword (:256))` by
    (irule ld_ghost_rel_phi_prov >> conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[phis_prov_def] >>
  Cases_on `h.inst_opcode = PHI` >> asm_rewrite_tac[] >>
  irule ld_ghost_rel_set_prov >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ld_ghost_ok_entry_prov[local]:
  ld_ghost_ok fl A H G /\
  entry_prov fn s (ld_erase A o_f H) = ld_erase A o_f H' ==>
  ld_ghost_ok fl A H' (entry_prov fn s G)
Proof
  rewrite_tac[ld_ghost_ok_erased] >> strip_tac >>
  qpat_x_assum `entry_prov _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[entry_prov_def] >> CASE_TAC >- metis_tac[] >>
  irule ld_ghost_rel_phis >> metis_tac[]
QED

Theorem ld_sync_control_entry:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) ==>
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C' inst t = OK ts /\ ~ts.vs_halted /\
  enters_block (ld_image f) ts t1 /\ active_inst (ld_image f) ti t1 /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ?lbl H' G' ni s1 g X.
    ts = jump_to lbl t /\ step_inst fuel C inst s = OK (jump_to lbl s) /\
    enters_block fn (jump_to lbl s) s1 /\
    g = f with <|lf_src := s1; lf_tgt := t1; lf_H := H';
      lf_tv := (entry_taint_vars fn (jump_to lbl s) tn).t_var|> /\
    ld_sync lo P C vs0 stk PG G'
      (entry_taint_vars fn (jump_to lbl s) tn) fn ni s1 t1 A (g::fs) N /\
    ld_global lo A (g::fs) /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (g::fs) /\
    (!j k. j < k /\ k < LENGTH (g::fs) ==>
      list_precedes (EL j (g::fs)).lf_fn.fn_name
                    (EL k (g::fs)).lf_fn.fn_name names) /\
    ld_image f = ld_image g /\
    ld_envelope g.lf_supply fn s1 s1.vs_inst_idx X t1.vs_inst_idx /\
    ld_prefix C' (ld_image f) X t1.vs_inst_idx 0 t1 t1 /\ ti = HD X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) (g::fs)
Proof
  rpt strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  `MEM fn C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions` by
    fs[ld_sync_def] >>
  `fn_shape_ok fn /\ fn_ptr_ok P fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[lowerDloadOracleCallAssemblyTheory.ld_active_inst_member] >>
  `f.lf_src.vs_labels = f.lf_tgt.vs_labels` by
    fs[lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
  drule ld_control_destination >>
  simp[] >>
  disch_tac >>
  `?lbl. ts = jump_to lbl t /\
    step_inst fuel C inst s = OK (jump_to lbl s)` by metis_tac[MEM] >>
  qpat_x_assum `!tn' t1' inst' fuelT fuelS CT CS. _` kall_tac >>
  drule_all ld_jump_effect >> disch_then (qspec_then `lbl` strip_assume_tac) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     pure_rewrite_tac [o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
       venomWfTheory.wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    (fs[ld_global_def] >> metis_tac[MEM]) >>
  qabbrev_tac `jf = f with <|lf_src := jump_to lbl s; lf_tgt := jump_to lbl t|>` >>
  `ld_image jf = ld_image f` by simp[ld_image_def, Abbr `jf`] >>
  `enters_block (FST (lower_dload_function_supply f.lf_supply fn))
     (jump_to lbl t) t1` by metis_tac[ld_image_def] >>
  mp_tac (Q.INST [`f` |-> `jf`, `ss` |-> `jump_to lbl s`] ld_entry_effect) >>
  simp[Abbr `jf`, Once ld_image_def] >>
  strip_tac >>
  `?ni X. active_inst fn ni s1 /\
    ld_envelope f.lf_supply fn s1 s1.vs_inst_idx X t1.vs_inst_idx /\
    X <> [] /\ ti = HD X` by
    (irule ld_entry_active_envelope >> conj_tac >- simp[] >>
     qexistsl_tac [`ld_image f`,`jump_to lbl s`,`jump_to lbl t`,
       `SND (lower_dload_function_supply f.lf_supply fn)`] >>
     simp[ld_image_def] >> metis_tac[pairTheory.PAIR]) >>
  `~(jump_to lbl s).vs_halted` by
    fs[lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
  `frame_reachable vs0 C stk PG (entry_prov fn (jump_to lbl s) G)
    (entry_taint_vars fn (jump_to lbl s) tn) fn ni s1` by
    (irule frame_reachable_block >>
     metis_tac[MEM, is_terminator_def]) >>
  `ld_ghost_ok (dyn_floor C vs0) A H' (entry_prov fn (jump_to lbl s) G)` by
    (irule ld_ghost_ok_entry_prov >> metis_tac[]) >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := t1; lf_H := H';
    lf_tv := (entry_taint_vars fn (jump_to lbl s) tn).t_var|>` >>
  `s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
   s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
   s1.vs_current_bb = t1.vs_current_bb /\ s1.vs_prev_bb = t1.vs_prev_bb` by
    (qpat_x_assum `s1 = jump_to lbl s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `t1 = jump_to lbl t with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[jump_to_def]) >>
  `ld_dyn_agree (dyn_floor C vs0)
     (entry_taint_vars fn (jump_to lbl s) tn).t_mem s1.vs_memory t1.vs_memory` by
    (`(entry_taint_vars fn (jump_to lbl s) tn).t_mem = tn.t_mem` by
       (simp[entry_taint_vars_def] >> CASE_TAC >> simp[]) >>
     pop_assum (fn th => rewrite_tac[th]) >>
     qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[jump_to_def] >> metis_tac[ld_sync_dyn_agree]) >>
  `ld_sync lo P C vs0 stk PG (entry_prov fn (jump_to lbl s) G)
     (entry_taint_vars fn (jump_to lbl s) tn) fn ni s1 t1 A (g::fs) N /\
   ld_global lo A (g::fs)` by
    (irule ld_sync_head_update >> simp[Abbr `g`] >> metis_tac[]) >>
  qexistsl_tac [`lbl`,`H'`,`entry_prov fn (jump_to lbl s) G`,`ni`,`s1`,`X`] >>
  qpat_x_assum `MEM inst.inst_opcode [JMP; JNZ; DJMP]` kall_tac >>
  gvs[Abbr `g`, ld_image_def] >>
  conj_tac
  >- (qpat_x_assum `!j k. _` mp_tac >> rpt (pop_assum kall_tac) >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`j`,`k`] mp_tac) >>
      Cases_on `j` >> Cases_on `k` >> simp[]) >>
  simp[ld_prefix_zero] >> Cases_on `X` >> fs[ld_image_def]
QED

Theorem ld_sync_control_owned_coverage:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) ==>
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C' inst t = OK ts /\ ~ts.vs_halted /\
  enters_block (ld_image f) ts t1 /\ active_inst (ld_image f) ti t1 /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    ld_image f = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' (ld_image f) X p h t0 t1 /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
Proof
  rpt strip_tac >> drule_all ld_sync_control_entry >> strip_tac >>
  qexistsl_tac [`stk`,`PG`,`G'`,
    `entry_taint_vars fn (jump_to lbl s) tn`,`fn`,`ni`,`s1`,`t1`,
    `A`,`g::fs`,`N`,`X`,`t1.vs_inst_idx`,`0`] >>
  qpat_x_assum `MEM inst.inst_opcode [JMP; JNZ; DJMP]` kall_tac >>
  gvs[]
QED
