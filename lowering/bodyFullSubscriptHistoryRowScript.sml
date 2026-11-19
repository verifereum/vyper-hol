(* The history arm reads from one selected snapshot, not every saved owner. *)
Theory bodyFullSubscriptHistoryRow
Ancestors
  targetSubscriptMemory exprSimSource exprSimPopNestedLocalPath
  vyperTypeEvalProofs vyperPlaceResultTyping vyperPlaceStatePreservation
  vyperPlaceInvariants valueEncodingTyping list words loweringPosts vyperState
  exprSimProps exprSimHypsDefs arithmetic

Theorem history_prefix_initially_absent[local]:
  popped_keys_indexed es.scopes /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value (prefix ++ suffix) = INL v ==>
  ~MEM (prefix,owner) entry.popped
Proof
  rpt strip_tac >>
  drule_all popped_keys_indexed_lookup_dead >>
  disch_then (assume_tac o REWRITE_RULE [EVERY_MEM]) >>
  `MEM prefix (MAP FST entry.popped)` by
    (simp[MEM_MAP] >> qexists `(prefix,owner)` >> simp[]) >>
  first_x_assum (drule_then (strip_assume_tac o BETA_RULE)) >>
  drule evaluate_subscripts_append_err >>
  disch_then (qspec_then `suffix` assume_tac) >> gvs[]
QED

(* The originating path must be live before the base and index runs.
   The endpoint live-result certificate instead supplies read coverage,
   possibly via a trusted history prefix. *)
Theorem subscript_history_row_physical:
  popped_kept ce es fin s0 u /\
  local_region ce es.scopes s0 id b sz /\
  popped_keys_indexed es.scopes /\
  lookup_scopes id es.scopes = SOME initial /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  lookup_scopes id fin.scopes = SOME entry /\
  live_memory_result fin (PlaceR (MemoryPlace id path)) /\
  evaluate_subscripts entry.type entry.value path = INR err /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  w2n a = b + k ==>
  ?v. read_popped entry.type path entry.popped = SOME v /\
      read_memory_path entry path = INL v /\
      read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
      value_has_type tv v /\ val_wf tv v /\ well_formed_type_value tv /\
      val_in_memory tv v (w2n a) u.vs_memory /\
      k + type_memory_size tv <= sz
Proof
  strip_tac >>
  fs[live_memory_result_def] >> gvs[] >>
  fs[memory_history_region_def, memory_path_covered_def] >>
  rename1 `read_popped entry.type path fresh = SOME v` >>
  drule read_popped_prefix_noninterference >>
  disch_then (qspec_then `old` assume_tac) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `value_has_type tv v` by (drule_all read_popped_type >> simp[]) >>
  qpat_assum `read_popped _ _ fresh = SOME v`
    (mp_then Any strip_assume_tac read_popped_owner) >>
  gvs[] >> drule mem_path_offset_append_decompose >> strip_tac >>
  qpat_assum `mem_path_offset entry.type prefix = SOME _`
    (mp_then Any strip_assume_tac mem_path_offset_sound) >> gvs[] >>
  `well_formed_type_value ptv /\ value_has_type ptv owner` by
    (fs[popped_history_typed_def] >> res_tac >> gvs[]) >>
  `!old_entry. lookup_scopes id es.scopes = SOME old_entry /\
               MEM (prefix,owner) old_entry.popped ==>
               snapshot_in old_entry.type b sz (prefix,owner) s0.vs_memory` by
    (simp[] >> metis_tac[history_prefix_initially_absent]) >>
  `MEM (prefix,owner) entry.popped` by simp[] >>
  drule_all_then strip_assume_tac popped_snapshot_path_in_memory >>
  `read_memory_path entry (prefix ++ suffix) = INL v` by simp[read_memory_path_def] >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `well_formed_type_value tv` by
    (qpat_assum `mem_path_offset ptv suffix = SOME _`
       (mp_then Any strip_assume_tac mem_path_offset_sound) >>
     metis_tac[subscripts_type_well_formed]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `val_in_memory tv v _ u.vs_memory` mp_tac >>
      pure_rewrite_tac[ADD_ASSOC] >> disch_then ACCEPT_TAC) >>
  qpat_assum `d + r + type_memory_size tv <= sz` mp_tac >>
  pure_rewrite_tac[ADD_ASSOC] >> disch_then ACCEPT_TAC
QED
