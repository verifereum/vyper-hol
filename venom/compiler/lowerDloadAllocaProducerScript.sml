Theory lowerDloadAllocaProducer
Ancestors
  lowerDloadAllocationOwner lowerDloadAllocationMemory lowerDloadTargetGeometry
  lowerDloadAllocaRepresentation lowerDloadTableSupport lowerDloadMaskBounds
  lowerDloadOwnership lowerDloadFrameCertificate lowerDloadPairedBoundary
  lowerDloadRelocation lowerDloadLifetime lowerDloadAllocation
  venomExecSemantics venomState venomInst ptrDiscipline finite_map pred_set list

(* The execution layer uses step_inst, whereas the allocation boundaries use
   exec_alloca. Keep the conversion here, once, including all unchanged fields. *)
Theorem ld_alloca_step_effects:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK z ==>
  ?n. eval_operand op s = SOME n /\ exec_alloca i s n = OK z /\
    (z with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next|>) = s /\
    z.vs_params = s.vs_params /\ s.vs_alloca_next <= z.vs_alloca_next /\
    (!v. v <> out ==> lookup_var v z = lookup_var v s)
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qexists `alloc_size` >> simp[eval_operand_def] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def,
      FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[]
QED

Theorem ld_alloca_pair_memory:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME(bs,sz) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME(bt,sz) /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  lo <= t.vs_alloca_next /\
  (!owner b c n. owner IN live /\ ld_site_entry E owner b c n ==>
    c+n <= t.vs_alloca_next) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) ==>
  let E' = if FLOOKUP L i.inst_id = NONE
           then E |+ ((0,k),(bs,bt,sz)) else E in
  let live' = if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live in
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E' live' a b)
    (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `?n:bytes32. exec_alloca i s n = OK s' /\ exec_alloca i t n = OK t'` by
    (qpat_x_assum `step_inst fuelS CS i s = OK s'` mp_tac >>
     qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
     simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
     Cases_on `op` >> simp[] >> rpt strip_tac >>
     rename1 `exec_alloca i s n = OK s'` >> qexists `n` >> simp[]) >>
  Cases_on `FLOOKUP L i.inst_id`
  >- suspend "fresh"
  >> suspend "cached"
QED

Resume ld_alloca_pair_memory[fresh]:
  `FLOOKUP s.vs_allocas i.inst_id = NONE` by
    metis_tac[ld_frame_embedding_source, ld_erase_lookup,
              optionTheory.OPTION_MAP_EQ_NONE] >>
  `FLOOKUP t.vs_allocas i.inst_id = NONE` by
    metis_tac[ld_alloc_account_old_absent] >>
  `bs = s.vs_alloca_next /\ bt = t.vs_alloca_next /\ sz = w2n n` by
    (gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE, AllCaseEqs()]) >>
  gvs[] >> simp[step_taint_def] >>
  irule ld_alloca_fresh_site_memory >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume ld_alloca_pair_memory[cached]:
  `?p. FLOOKUP s.vs_allocas i.inst_id = SOME p` by
    (drule ld_frame_embedding_source >>
     disch_then (SUBST1_TAC o SYM) >> simp[ld_erase_lookup]) >>
  PairCases_on `p` >>
  `?q. FLOOKUP t.vs_allocas i.inst_id = SOME q` by
    metis_tac[ld_alloc_account_old_entry] >>
  PairCases_on `q` >>
  drule_all (SRULE [] (Q.INST [`j` |-> `i`, `out'` |-> `out`]
    ld_alloca_cached_memory)) >> simp[step_taint_def]
QED

Finalise ld_alloca_pair_memory

Theorem ld_alloca_definedness:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  lookup_var out s' = SOME x /\ lookup_var out t' = SOME y /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)
Proof
  strip_tac >>
  `!v. v <> out ==> lookup_var v s' = lookup_var v s` by
    (metis_tac[ld_alloca_step_effects]) >>
  `!v. v <> out ==> lookup_var v t' = lookup_var v t` by
    (metis_tac[ld_alloca_step_effects]) >>
  gen_tac >> strip_tac >> Cases_on `v = out` >> simp[]
QED

Theorem ld_alloca_nonmemory_taints:
  i.inst_opcode = ALLOCA ==>
  (step_taint i s z tn).t_stor = tn.t_stor /\
  (step_taint i s z tn).t_trans = tn.t_trans /\
  (step_taint i s z tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem ld_alloca_pair_selections:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] /\
  ld_frame_embedding E' L' H' s' t' /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  LIST_REL (ld_owned_selection E') AP BP /\
  (!v. ld_owned_selection E'
    (FLOOKUP (ld_step_prov AP AG L' i) v)
    (FLOOKUP (ld_step_prov BP BH H' i) v))
Proof
  strip_tac >> conj_tac
  >- (irule lowerDloadOwnerTransportTheory.ld_owned_params_support >>
      qexists `E` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
      simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  `!v. ld_owned_selection E' (FLOOKUP AG v) (FLOOKUP BH v)` by
    (gen_tac >> irule lowerDloadOwnerTransportTheory.ld_owned_selection_support >>
     qexists `E` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  `ld_owned_selection E' (FLOOKUP L' i.inst_id) (FLOOKUP H' i.inst_id)` by
    metis_tac[ld_frame_embedding_selection] >>
  Cases_on `FLOOKUP L' i.inst_id` >>
  gvs[ld_owned_selection_def] >>
  simp[ld_step_prov_def, ld_set_prov_def, ld_out_prov_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gen_tac >> Cases_on `v = out` >> simp[ld_owned_selection_def]
QED

Theorem ld_alloca_fresh_extent[local]:
  FLOOKUP s.vs_allocas i.inst_id = NONE /\
  exec_alloca i s (n:bytes32) = OK z /\
  FLOOKUP z.vs_allocas i.inst_id = SOME(b,sz) ==>
  b = s.vs_alloca_next /\ sz = w2n n /\
  b + sz = z.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  strip_tac >> gvs[FLOOKUP_UPDATE]
QED

Theorem ld_site_extend_separation[local]:
  fresh NOTIN live /\
  (!owner b c n. owner IN live /\ ld_site_entry E owner b c n ==>
    b+n <= bs /\ c+n <= bt) /\
  (!owner other b c n e g h.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner b c n /\ ld_site_entry E other e g h ==>
    (b+n <= e \/ e+h <= b) /\ (c+n <= g \/ g+h <= c)) ==>
  !owner other b c n e g h.
    owner IN fresh INSERT live /\ other IN fresh INSERT live /\ owner <> other /\
    ld_site_entry (E |+ (fresh,(bs,bt,sz))) owner b c n /\
    ld_site_entry (E |+ (fresh,(bs,bt,sz))) other e g h ==>
    (b+n <= e \/ e+h <= b) /\ (c+n <= g \/ g+h <= c)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `owner = fresh` >> Cases_on `other = fresh` >>
  simp[ld_site_entry_def, FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >>
  fs[ld_site_entry_def] >> metis_tac[]
QED

Theorem ld_alloca_certificate_backward:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  ld_alloc_account keys d A s t /\ ld_owned_vars U E AG BH tn un s t /\
  (!v. op = Var v ==> v IN U) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\ step_inst fuelT CT i t = OK t' /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\
  lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next /\
  (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
    owner IN live /\ lo <= b) /\
  (FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  (!owner bs bt sz. ld_live astk L AP AG (owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) ==>
  ?s' n bs bt sz E' k' L' H'.
    step_inst fuelS CS i s = OK s' /\
    eval_operand op s = SOME n /\ eval_operand op t = SOME n /\
    FLOOKUP s'.vs_allocas i.inst_id = SOME(bs,sz) /\
    FLOOKUP t'.vs_allocas i.inst_id = SOME(bt,sz) /\
    lookup_var out s' = SOME(n2w bs) /\ lookup_var out t' = SOME(n2w bt) /\
    bs <= bt /\ bt <= bs + d + 32 * CARD A /\
    E' = (if FLOOKUP L i.inst_id = NONE
          then E |+ ((0,k),(bs,bt,sz)) else E) /\
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    ld_alloc_account keys d A s' t' /\
    ld_owned_vars U E' (ld_step_prov AP AG L' i) (ld_step_prov BP BH H' i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!owner. owner IN live ==> FLOOKUP E' owner = FLOOKUP E owner) /\
    LIST_REL (ld_owned_selection E') AP BP /\
    (!v. ld_owned_selection E' (FLOOKUP (ld_step_prov AP AG L' i) v)
      (FLOOKUP (ld_step_prov BP BH H' i) v)) /\
    ld_frame_bound t'.vs_alloca_next H' BP (ld_step_prov BP BH H' i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    (!owner b n. ld_live astk L' AP (ld_step_prov AP AG L' i) (owner,(b,n)) ==>
      owner IN (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live) /\
      lo <= b) /\
    (!owner b c n. owner IN
        (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live) /\
      ld_site_entry E' owner b c n ==>
      lo <= b /\ lo <= c /\ b+n <= s'.vs_alloca_next /\ c+n <= t'.vs_alloca_next) /\
    (!owner other b c n e g h.
      owner IN (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live) /\
      other IN (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live) /\
      owner <> other /\ ld_site_entry E' owner b c n /\
      ld_site_entry E' other e g h ==>
      (b+n <= e \/ e+h <= b) /\ (c+n <= g \/ g+h <= c)) /\
    (!owner b c n. ld_live astk L' AP (ld_step_prov AP AG L' i) (owner,(b,n)) /\
      ld_site_entry E' owner b c n ==>
      c+n <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(c,n)) /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E'
      (if FLOOKUP L i.inst_id = NONE then (0,k) INSERT live else live) a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    s'.vs_params = s.vs_params /\ t'.vs_params = t.vs_params /\
    (s' with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next|>) = s /\
    (t' with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
               vs_alloca_next := t.vs_alloca_next|>) = t
Proof
  strip_tac >> drule_all ld_owned_alloca_transition_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`,`BP`] strip_assume_tac) >>
  drule_all ld_alloca_pair_selections >> strip_tac >>
  qpat_assum `step_inst fuelT CT i t = OK t'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `step_inst fuelS CS i s = OK s'`
    (mp_then Any (qspecl_then [`out`,`op`] mp_tac) ld_alloca_step_effects) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `n' = n /\ n'' = n` by fs[] >>
  qpat_x_assum `n' = n` SUBST_ALL_TAC >>
  qpat_x_assum `n'' = n` SUBST_ALL_TAC >>
  drule_all ld_embedded_alloca_geometry >> strip_tac >>
  qexistsl [`s'`,`n`,`bs`,`bt`,`sz`,`E'`,`k'`,`L'`,`H'`] >>
  qpat_x_assum `E' = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- suspend "agreement"
  >- suspend "live"
  >- suspend "endpoints"
  >- suspend "separation"
  >- suspend "representation"
  >- suspend "memory"
  >- (gen_tac >> strip_tac >> Cases_on `v = out` >> simp[])
  >- (irule ld_step_taint_bound >> simp[])
  >- (irule ld_step_taint_bound >> simp[])
  >> simp[ld_alloca_nonmemory_taints]
QED

Resume ld_alloca_certificate_backward[agreement]:
  Cases_on `FLOOKUP L i.inst_id` >> gvs[] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >> metis_tac[]
QED

Resume ld_alloca_certificate_backward[memory]:
  `!owner b c n. owner IN live /\ ld_site_entry E owner b c n ==>
    c+n <= t.vs_alloca_next` by metis_tac[] >>
  drule_all ld_alloca_pair_memory >> simp[]
QED

Resume ld_alloca_certificate_backward[representation]:
  drule_all ld_alloca_live_representation >> simp[] >> strip_tac >>
  gvs[]
QED

Resume ld_alloca_certificate_backward[live]:
  rpt gen_tac >> strip_tac >>
  `ld_live astk L' AP AG (owner,(b,n'))` by
    (fs[ld_live_def] >> metis_tac[ld_step_selected]) >>
  qpat_x_assum `ld_live _ _ _ (ld_step_prov _ _ _ _) _` kall_tac >>
  `ld_live astk L AP AG (owner,(b,n')) \/
   (FLOOKUP L i.inst_id = NONE /\ owner = (0,k) /\ b = bs /\ n' = sz)` by
    (qpat_x_assum `ld_live astk L' AP AG _` mp_tac >>
     qpat_x_assum `ld_select_alloca k L i s' = _` mp_tac >>
     simp[ld_select_alloca_def] >>
     Cases_on `FLOOKUP L i.inst_id` >> simp[] >>
     strip_tac >> gvs[] >>
     rw[ld_live_def, ld_selected_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
     metis_tac[]) 
  >- (Cases_on `FLOOKUP L i.inst_id` >> simp[] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas i.inst_id = NONE` by
    metis_tac[ld_frame_embedding_source, ld_erase_lookup,
              optionTheory.OPTION_MAP_EQ_NONE] >>
  `bs = s.vs_alloca_next` by
    (qpat_x_assum `exec_alloca i s _ = _` mp_tac >>
     simp[exec_alloca_def, update_var_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[FLOOKUP_UPDATE]) >>
  simp[]
QED

Resume ld_alloca_certificate_backward[endpoints]:
  Cases_on `FLOOKUP L i.inst_id`
  >- (`FLOOKUP s.vs_allocas i.inst_id = NONE` by
        metis_tac[ld_frame_embedding_source, ld_erase_lookup,
                  optionTheory.OPTION_MAP_EQ_NONE] >>
      `FLOOKUP t.vs_allocas i.inst_id = NONE` by
        metis_tac[ld_alloc_account_old_absent] >>
      `bs = s.vs_alloca_next /\ bs+sz = s'.vs_alloca_next` by
        metis_tac[ld_alloca_fresh_extent] >>
      `bt = t.vs_alloca_next /\ bt+sz = t'.vs_alloca_next` by
        metis_tac[ld_alloca_fresh_extent] >>
      gvs[] >> rpt gen_tac >>
      simp[ld_site_entry_def, FLOOKUP_UPDATE] >>
      Cases_on `owner = (0,k)` >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!owner bs bt sz. _ IN live /\ _ ==> _`
        (qspecl_then [`owner`,`b`,`c`,`n'`] mp_tac) >>
      simp[ld_site_entry_def] >> strip_tac >> simp[]) >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!owner bs bt sz. _ IN live /\ _ ==> _`
    (qspecl_then [`owner`,`b`,`c`,`n'`] mp_tac) >>
  simp[] >> strip_tac >> simp[]
QED

Resume ld_alloca_certificate_backward[separation]:
  Cases_on `FLOOKUP L i.inst_id`
  >- (`FLOOKUP s.vs_allocas i.inst_id = NONE` by
        metis_tac[ld_frame_embedding_source, ld_erase_lookup,
                  optionTheory.OPTION_MAP_EQ_NONE] >>
      `FLOOKUP t.vs_allocas i.inst_id = NONE` by
        metis_tac[ld_alloc_account_old_absent] >>
      `bs = s.vs_alloca_next /\ bs+sz = s'.vs_alloca_next` by
        metis_tac[ld_alloca_fresh_extent] >>
      `bt = t.vs_alloca_next /\ bt+sz = t'.vs_alloca_next` by
        metis_tac[ld_alloca_fresh_extent] >>
      `!owner b c n. owner IN live /\ ld_site_entry E owner b c n ==>
        b+n <= bs /\ c+n <= bt` by
        (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!owner bs bt sz. _ IN live /\ _ ==> _`
           (qspecl_then [`owner`,`b`,`c`,`n'`] mp_tac) >> simp[]) >>
      gvs[] >>
      mp_tac (Q.INST [`fresh` |-> `(0,k)`, `E` |-> `E`,
        `live` |-> `live`, `bs` |-> `s.vs_alloca_next`,
        `bt` |-> `t.vs_alloca_next`, `sz` |-> `sz`]
        ld_site_extend_separation) >>
      (impl_tac >- asm_rewrite_tac[]) >> simp[IN_INSERT]) >>
  gvs[] >> asm_rewrite_tac[]
QED

Finalise ld_alloca_certificate_backward

(* Local certificate audit:
   C1 frame embedding; C2 paired parameter and successor provenance selections;
   C3 owned values on U; C4 original-name definedness on V; C5 allocation
   account with unchanged keys/d/A; C6 successor target frame/stack bounds and
   lower bound; C7 successor source live coverage; C8 natural endpoints on
   both sides; C9 pairwise non-strict separation, including zero-size sites;
   C10 masked byte relation at actual step_taint successors; C11 both variable
   mask bounds; C12 storage/transient/immutable taint subsets.

   Source success is produced from target success. Scalar support, provenance
   absence and source operand cleanliness remain explicit consumer obligations;
   this theorem does not claim their discharge at every reachable instruction.
   E' agrees with E on all pre-live owners, not just the currently selected
   owner. Together with pre-live coverage and ld_live_saved_projection this
   preserves each saved frame's table snapshot agreement; the existing
   ld_alloca_saved_snapshot supplies the same transport directly from the
   produced source/target steps and allocation entries. Saved frames, astk,
   gstk, AP/BP and the charge/support parameters are unchanged. Parameters are
   preserved explicitly and restoration retains every field except variables,
   allocation maps and the frontier. No saved memory restoration is asserted.
   Current representation retains the separate frame floor f.

   Every suspended branch above is resumed and Finalised. This is ordinary
   ALLOCA local production only, not annotated alignment, DLOAD scratch
   allocation, whole-call execution or temporal certificate closure.
*)
