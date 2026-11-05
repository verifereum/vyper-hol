(* Location-independent endpoints of actual generated expansions. *)
Theory lowerDloadExpansionEndpoint
Ancestors
  lowerDloadScratchTransport lowerDloadPublicEffect lowerDloadSafetyAdvance
  lowerDloadPublicTrace lowerDloadSafetyLocations lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadSafetyAmbient
  o1PassContract ptrDiscipline venomWf codegenRel unitShapeDefs venomExecSemantics venomState venomInst
  finite_map pred_set list words arithmetic

Theorem ld_sync_envelope_position:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p ==> t.vs_inst_idx = p
Proof
  strip_tac >> drule ld_sync_active >> simp[] >> strip_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ld_sync_def] >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH (f::fs) ==> ?X p. _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `ld_envelope _ _ _ _ X p` mp_tac >>
  qpat_x_assum `ld_envelope _ _ _ _ X' p'` mp_tac >>
  simp[ld_envelope_def] >> rpt strip_tac >>
  `bi = bi'` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ fn.fn_blocks)`
      (mp_then Any mp_tac ALL_DISTINCT_EL_IMP) >>
     disch_then (qspecl_then [`bi`, `bi'`] mp_tac) >> simp[EL_MAP]) >> gvs[]
QED

Theorem ld_head_order_cong:
  g.lf_fn = f.lf_fn ==>
  ((!j k. j < k /\ k < LENGTH (g::fs) ==>
      list_precedes (EL j (g::fs)).lf_fn.fn_name
                    (EL k (g::fs)).lf_fn.fn_name names) <=>
   (!j k. j < k /\ k < LENGTH (f::fs) ==>
      list_precedes (EL j (f::fs)).lf_fn.fn_name
                    (EL k (f::fs)).lf_fn.fn_name names))
Proof
  strip_tac >>
  `!j. (EL j (g::fs)).lf_fn = (EL j (f::fs)).lf_fn` by
    (Cases >> simp[]) >> simp[]
QED

Theorem ld_sync_scratch_reconstruct:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  g.lf_src = s' /\ g.lf_tgt = t' /\ g.lf_tv = tn'.t_var /\
  frame_reachable vs0 C stk PG G' tn' fn next s' /\ active_inst fn next s' /\
  G' = ld_erase A o_f g.lf_H /\ ld_vars P A g /\
  EVERY (ld_maps A) (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
  ld_intervals lo s' /\ ld_intervals lo t' /\
  s'.vs_current_bb = t'.vs_current_bb /\ s'.vs_prev_bb = t'.vs_prev_bb /\
  (!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
  ld_charge (g::fs) <= ctx_dload_count C /\
  (?X. ld_envelope f.lf_supply fn s' s'.vs_inst_idx X t'.vs_inst_idx) /\
  ld_memory lo A tn' s' t' /\ ld_nonghost tn' s' t' ==>
  ld_sync lo P C vs0 stk PG G' tn' fn next s' t' A (g::fs) N
Proof
  strip_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_sync_def] >> strip_tac >> simp[] >>
  conj_tac >- (gvs[EVERY_DEF] >> metis_tac[]) >>
  gen_tac >> Cases_on `j`
  >- (simp[] >> metis_tac[]) >>
  qpat_x_assum `!j. _ ==> ?X. ld_envelope _ _ _ _ X _`
    (qspec_then `SUC n` mp_tac) >> gvs[]
QED

Theorem ld_dloadbytes_endpoint:
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  reserved_intervals_wf C.ctx_global_reserved /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs0 /\ fmp_free_ctx C /\
  mem_inv raw_mem_ok C vs0 /\ mem_inv dload_offset_ok C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    lookup_function fn.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  fn' = ld_image f /\ ir_supply_covers_fn f.lf_supply fn /\
  ~in_revert_forward fn s /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ SUC h = LENGTH X /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  step_inst fuel C' (EL h X) t = OK u ==>
  ?ss Ar g.
    Ar = A /\ step_inst 0 C inst s = OK ss /\
    u.vs_inst_idx = t.vs_inst_idx /\
    (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = p + LENGTH X /\
    g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
    g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := p + LENGTH X) /\
    g.lf_tv = (step_taint inst s ss tn).t_var /\
    step_prov PG G inst ss = ld_erase Ar o_f g.lf_H /\
    ld_vars P Ar g /\ ld_maps Ar g /\
    ld_memory lo Ar (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_global lo Ar (g::fs) /\ FDOM Ar = ld_slots Ar (g::fs) /\
    EVERY (ld_maps Ar) fs /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (g::fs) /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) (g::fs) /\
    (!j k. j < k /\ k < LENGTH (g::fs) ==>
      list_precedes (EL j (g::fs)).lf_fn.fn_name
                    (EL k (g::fs)).lf_fn.fn_name names) /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N)
Proof
  strip_tac >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     gvs[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
  `h = 1` by gvs[] >> qpat_x_assum `h = 1` SUBST_ALL_TAC >>
  drule_all ld_sync_dloadbytes_effect >>
  disch_then (qx_choose_then `ss` (qx_choose_then `H'`
    (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  `t0.vs_inst_idx = p` by (drule_all ld_sync_envelope_position >> simp[]) >>
  `t.vs_inst_idx = p+1` by (irule ld_prefix_position >> metis_tac[]) >>
  qabbrev_tac `g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := u with vs_inst_idx := p + LENGTH X;
    lf_H := H'; lf_tv := tn'.t_var|>` >>
  `g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := u with vs_inst_idx := p + LENGTH X;
    lf_H := H'; lf_tv := tn'.t_var|>` by simp[Abbr `g`] >>
  drule_all ld_nonallocating_endpoint >> strip_tac >>
  `g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
   g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\ g.lf_H = H' /\
   g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := p+LENGTH X) /\ g.lf_tv = tn'.t_var` by
    simp[NoAsms, Abbr `g`] >>
  qpat_x_assum `g = _` kall_tac >> qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `tn' = _` SUBST_ALL_TAC >>
  qpat_x_assum `G' = _` SUBST_ALL_TAC >>
  qexistsl_tac [`ss`, `A`, `g`] >>
  asm_simp_tac std_ss [] >>
  conj_tac >- simp[NoAsms] >>
  conj_tac >- (qpat_x_assum `EVERY (\f. f.lf_supply = _) (f::fs)` mp_tac >>
    asm_simp_tac std_ss [EVERY_DEF]) >>
  conj_tac >- (qpat_x_assum `EVERY (\f. !j a. _) (f::fs)` mp_tac >>
    asm_simp_tac std_ss [EVERY_DEF]) >>
  conj_tac >- (drule ld_head_order_cong >> disch_then (fn th => rewrite_tac[th]) >>
    qpat_x_assum `!j k. _` ACCEPT_TAC) >>
  qpat_x_assum `!next. _` mp_tac >> asm_rewrite_tac[]
QED

val _ = app (fn th => if null (hyp th) then ()
  else raise Fail "expansion endpoint boundary has hypotheses")
  [ld_sync_envelope_position, ld_head_order_cong,
   ld_sync_scratch_reconstruct, ld_dloadbytes_endpoint];
