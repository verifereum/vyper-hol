Theory lowerDloadNormalAlloca
Ancestors
  lowerDloadNormalData lowerDloadNormalTransport lowerDloadAllocaProducer
  lowerDloadOwnerTransport lowerDloadSharedState lowerDloadOwnership
  lowerDloadAllocationOwner
  lowerDloadLifetime lowerDloadCoverageInvariant lowerDloadFrameCertificate
  venomState venomExecSemantics ptrDiscipline finite_map pred_set list

Theorem ld_alloca_restore_normalize[local]:
  (z with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next|>) = s ==>
  z = (s with <|vs_vars := z.vs_vars; vs_allocas := z.vs_allocas;
               vs_alloca_next := z.vs_alloca_next|>)
Proof
  strip_tac >> pop_assum (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem ld_alloca_frontier_floor:
  exec_alloca i s n = OK z /\ allocas_from f s /\ f <= s.vs_alloca_next ==>
  allocas_from f z /\ f <= z.vs_alloca_next /\
  z.vs_alloca_next <= s.vs_alloca_next + w2n n
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_alloca_normal_data_backward_fresh_bounds:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  (!v. op = Var v ==> v IN U) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\ eval_operand op s = SOME n /\
  lo <= s.vs_alloca_next /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  (FLOOKUP L i.inst_id = NONE ==>
    s.vs_alloca_next + w2n n < dimword(:256) /\
    t.vs_alloca_next + w2n n < dimword(:256)) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' E' k' L' H'.
    step_inst fuelS CS i s = OK s' /\
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    E' = (if FLOOKUP L i.inst_id = NONE then
      E |+ ((0,k),(FST (THE (FLOOKUP s'.vs_allocas i.inst_id)),
                    FST (THE (FLOOKUP t'.vs_allocas i.inst_id)),w2n n)) else E) /\
    (!owner. owner IN live ==> FLOOKUP E' owner = FLOOKUP E owner) /\
    ld_normal_data CS fn V U lo E' L' H' AP BP
      (ld_step_prov AP AG L' i) (ld_step_prov BP BH H' i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live)
      keys d A suspended gstk f
Proof
  strip_tac >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_memory >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `!owner bs bt sz. ld_live astk L AP AG (owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)` by
    metis_tac[] >>
  drule_all ld_alloca_certificate_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >>
  `n' = n` by fs[] >> qpat_x_assum `n' = n` SUBST_ALL_TAC >>
  qexistsl [`s'`,`k'`,`L'`,`H'`] >> simp[] >>
  `FLOOKUP L i.inst_id = NONE ==> sz = w2n n` by
    (strip_tac >>
     `FLOOKUP s.vs_allocas i.inst_id = NONE` by
       metis_tac[ld_frame_embedding_source, ld_erase_lookup,
                 optionTheory.OPTION_MAP_EQ_NONE] >>
     drule_all ld_alloca_step_effects >> strip_tac >>
     qpat_x_assum `i.inst_outputs = [out]` mp_tac >>
     qpat_x_assum `exec_alloca i s _ = OK s'` mp_tac >>
     qpat_x_assum `FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz)` mp_tac >>
     qpat_x_assum `FLOOKUP s.vs_allocas i.inst_id = NONE` mp_tac >>
     qpat_x_assum `eval_operand op s = SOME n'` mp_tac >>
     qpat_x_assum `eval_operand op s = SOME n` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE]) >>
  `((if FLOOKUP L i.inst_id = NONE then E |+ ((0,k),(bs,bt,w2n n)) else E)) = E'` by
    (Cases_on `FLOOKUP L i.inst_id = NONE` >> gvs[]) >>
  qpat_x_assum `E' = _` (fn extension =>
    qpat_x_assum `(if _ then _ else _) = E'` (fn th =>
      once_rewrite_tac[th]) >>
    conj_tac >- asm_rewrite_tac[] >>
    irule ld_normal_data_assemble >>
    asm_rewrite_tac[ld_frame_data_def] >> rpt conj_tac >>
    assume_tac extension)
  >- suspend "noncurrent_storage"
  >- suspend "noncurrent_transient"
  >- suspend "provenance_support"
  >- suspend "strict_endpoints"
  >- suspend "live_representation"
  >- suspend "frontier_floor"
  >- suspend "gas_equal"
  >- suspend "parameter_envelope"
  >- suspend "allocas_floor"
  >> suspend "shared_and_account"
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[noncurrent_storage]:
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  fs[ld_shared_state_def, ld_alloca_nonmemory_taints] >>
  drule ld_normal_data_companions >> simp[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[noncurrent_transient]:
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  drule ld_normal_data_companions >> simp[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[provenance_support]:
  map_every qx_gen_tac [`v`,`owner`,`b0`,`n0`] >> strip_tac >>
  `ld_live astk L' AP (ld_step_prov AP AG L' i) (owner,(b0,n0))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  metis_tac[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[strict_endpoints]:
  Cases_on `FLOOKUP L i.inst_id = NONE`
  >- suspend "fresh_strict_endpoints" >>
  gvs[] >> metis_tac[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[fresh_strict_endpoints]:
  `s.vs_alloca_next + w2n n < dimword(:256) /\
   t.vs_alloca_next + w2n n < dimword(:256)` by metis_tac[] >>
  qpat_assum `step_inst fuelS CS i s = OK s'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `step_inst fuelT CT i t = OK t'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `n' = n /\ n'' = n` by fs[] >>
  qpat_x_assum `n' = n` SUBST_ALL_TAC >>
  qpat_x_assum `n'' = n` SUBST_ALL_TAC >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `0 <= s.vs_alloca_next` by simp[] >>
  drule_all ld_alloca_frontier_floor >> strip_tac >>
  qpat_assum `exec_alloca i s n = OK s'`
    (mp_then Any (qspec_then `0` mp_tac) ld_alloca_frontier_floor) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `s'.vs_alloca_next < dimword(:256) /\
   t'.vs_alloca_next < dimword(:256)` by decide_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!owner b c n. _ IN _ /\ _ ==> _`
    drule >> strip_tac >> first_x_assum drule >> strip_tac >> decide_tac
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[live_representation]:
  map_every qx_gen_tac [`owner`,`b0`,`c0`,`n0`] >> strip_tac >>
  Cases_on `FLOOKUP L i.inst_id = NONE /\ owner = (0,k)`
  >- (`b0 = bs /\ c0 = bt /\ n0 = sz` by
        (qpat_x_assum `ld_site_entry E' owner b0 c0 n0` mp_tac >>
         qpat_x_assum `E' = _` mp_tac >>
         qpat_x_assum `FLOOKUP L i.inst_id = NONE /\ owner = (0,k)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[ld_site_entry_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
      disj2_tac >> qexists_tac `i.inst_id` >> metis_tac[]) >>
  `owner IN live /\ ld_site_entry E owner b0 c0 n0` by
    (qpat_x_assum `ld_site_entry E' owner b0 c0 n0` mp_tac >>
     qpat_x_assum `owner IN (if _ then _ else _)` mp_tac >>
     qpat_x_assum `E' = _` mp_tac >>
     qpat_x_assum `~(FLOOKUP L i.inst_id = NONE /\ owner = (0,k))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `FLOOKUP L i.inst_id = NONE` >>
     simp[ld_site_entry_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `c0+n0 <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(c0,n0)` by
    metis_tac[] >>
  metis_tac[ld_alloca_preserves_entry]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[frontier_floor]:
  qpat_assum `step_inst fuelT CT i t = OK t'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >> decide_tac
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[gas_equal]:
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  drule ld_normal_data_companions >> simp[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[parameter_envelope]:
  qpat_x_assum `E' = _` kall_tac >>
  drule ld_normal_data_envelope >> strip_tac
  >- (disj1_tac >> asm_rewrite_tac[]) >>
  disj2_tac >> asm_rewrite_tac[] >> qx_gen_tac `q` >> strip_tac >>
  irule ld_owned_value_support >> qexists_tac `E` >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  map_every qx_gen_tac [`owner`,`b0`,`n0`] >> strip_tac >>
  `MEM (SOME(owner,(b0,n0))) AP` by metis_tac[EL_MEM] >>
  `ld_live astk L AP AG (owner,(b0,n0))` by
    simp[ld_live_def, ld_selected_def] >>
  metis_tac[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[allocas_floor]:
  qpat_assum `step_inst fuelT CT i t = OK t'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all ld_alloca_frontier_floor >> simp[]
QED

Resume ld_alloca_normal_data_backward_fresh_bounds[shared_and_account]:
  markerLib.RESUME_TAC >> gvs[] >>
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_alloca_restore_normalize >> disch_then SUBST_ALL_TAC >>
  fs[ld_shared_state_def, ld_alloca_nonmemory_taints]
QED

Finalise ld_alloca_normal_data_backward_fresh_bounds

(* Compatibility interface; the substantive assembly is branch-sensitive. *)
Theorem ld_alloca_normal_data_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  (!v. op = Var v ==> v IN U) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\ eval_operand op s = SOME n /\
  lo <= s.vs_alloca_next /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  s.vs_alloca_next + w2n n < dimword(:256) /\
  t.vs_alloca_next + w2n n < dimword(:256) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' E' k' L' H'.
    step_inst fuelS CS i s = OK s' /\
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    E' = (if FLOOKUP L i.inst_id = NONE then
      E |+ ((0,k),(FST (THE (FLOOKUP s'.vs_allocas i.inst_id)),
                    FST (THE (FLOOKUP t'.vs_allocas i.inst_id)),w2n n)) else E) /\
    (!owner. owner IN live ==> FLOOKUP E' owner = FLOOKUP E owner) /\
    ld_normal_data CS fn V U lo E' L' H' AP BP
      (ld_step_prov AP AG L' i) (ld_step_prov BP BH H' i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live)
      keys d A suspended gstk f
Proof
  strip_tac >> irule ld_alloca_normal_data_backward_fresh_bounds >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
