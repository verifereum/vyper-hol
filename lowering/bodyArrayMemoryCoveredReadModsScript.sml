Theory bodyArrayMemoryCoveredReadMods
Ancestors
  bodyFullSubscriptCoveredRow bodyFullShadowBodyInv exprSimProps
  bodyPtrDefs ptrDiscipline loweringStateRelDefs vyperPlaceStatePreservation
  vyperState vyperValueOperation arithmetic words finite_map

(* The covered-row read needs only the zero-prefix core. Keep the original
   lo in the linked hypotheses and discard it only for this application. *)
Theorem covered_read_core_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s ==>
  ghost_inv_at D 0 d ce cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem array_memory_covered_read_mods:
  lookup_scopes id es.scopes = SOME initial /\
  lookup_scopes id fin.scopes = SOME entry /\ entry.type = initial.type /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
  lookup_var q s0 = SOME B /\ lookup_var q it = SOME B /\
  local_region ce mid.scopes s id (w2n B) sz /\
  type_memory_size initial.type <= sz /\ w2n B + sz < dimword (:256) /\
  popped_keys_indexed es.scopes /\ entry_pop_trace initial events entry /\
  entry_pop_trace_valid events /\ well_formed_type_value initial.type /\
  value_has_type initial.type initial.value /\ value_has_type entry.type entry.value /\
  ghost_inv_at_mods D0 lo d ce cx es G0 tn0 s0 /\
  ghost_inv_at_mods D1 lo d ce cx fin Gi tni it /\
  popped_kept ce es fin s0 it /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo ce mid sm G1 tn1 s Gi tni ==>
  !r k tv. (?v0. evaluate_subscripts initial.type initial.value r = INL v0) /\
    live_memory_result fin (PlaceR (MemoryPlace id r)) /\
    mem_path_offset entry.type r = SOME (k,tv) ==>
    ?v. read_result cx (PlaceR (MemoryPlace id r)) fin = (INL v,fin) /\
        value_has_type tv v /\ well_formed_type_value tv /\
        k + type_memory_size tv <= sz /\
        !m. mem_agree_outside tni.t_mem it.vs_memory m ==>
            val_in_memory tv v (w2n B + k) m
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `w2n B + k < dimword (:256)` by
    (qpat_assum `entry.type = initial.type` (fs o single) >> decide_tac) >>
  qabbrev_tac `a = (n2w (w2n B + k) : 256 word)` >>
  `w2n a = w2n B + k` by simp[Abbr `a`, w2n_n2w_compute] >>
  `ghost_inv_at D0 0 d ce cx es G0 tn0 s0` by
    (irule covered_read_core_ghost >> goal_assum drule) >>
  `ghost_inv_at D1 0 d ce cx fin Gi tni it` by
    (irule covered_read_core_ghost >> goal_assum drule) >>
  `ghost_kept_at 0 ce es sa G0 tn0 s0 G1 tn1` by
    (qpat_assum `ghost_kept_at lo _ es _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at 0 ce mid sm G1 tn1 s Gi tni` by
    (qpat_assum `ghost_kept_at lo _ mid _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  qpat_assum `w2n a = _` (once_rewrite_tac o single o SYM) >>
  irule subscript_covered_row_read_robust >>
  simp[] >>
  qpat_assum `ghost_kept_at 0 ce es sa G0 tn0 s0 G1 tn1` (irule_at Any) >>
  qpat_assum `ghost_kept_at 0 ce mid sm G1 tn1 s Gi tni` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[]
QED
