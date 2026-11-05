Theory makeSsaCurrentFinalWriteSlots
Ancestors makeSsaCurrentFinalWrites list rich_list pair

Definition current_table_final_slots_def:
  current_table_final_slots table outs outs' <=>
    LENGTH outs = LENGTH outs' /\
    !v n. MEM (v,n) table ==>
      (~MEM v outs /\ ~MEM n outs') \/
      ?j. j < LENGTH outs /\ EL j outs = v /\ EL j outs' = n /\
        !k. j < k /\ k < LENGTH outs ==>
          EL k outs <> v /\ EL k outs' <> n
End

Theorem current_full_events_index[local]:
  MAP FST events = GENLIST I numslots /\ k < LENGTH events ==>
  FST (EL k events) = k /\ k < numslots
Proof
  rpt strip_tac >>
  `LENGTH events = numslots` by metis_tac[LENGTH_MAP, LENGTH_GENLIST] >>
  `EL k (MAP FST events) = EL k (GENLIST I numslots)` by simp[] >>
  gvs[EL_MAP, EL_GENLIST]
QED

Theorem current_full_events_split[local]:
  MAP FST events = GENLIST I numslots /\ j < numslots ==>
  ?pre value post. events = pre ++ (j,value)::post /\
    EVERY (\kv. j < FST kv /\ FST kv < numslots) post
Proof
  rpt strip_tac >>
  `LENGTH events = numslots` by metis_tac[LENGTH_MAP, LENGTH_GENLIST] >>
  `FST (EL j events) = j` by metis_tac[current_full_events_index] >>
  qexistsl_tac [`TAKE j events`, `SND (EL j events)`, `DROP (SUC j) events`] >>
  conj_tac
  >- (mp_tac (Q.ISPEC `events:(num # 'a) list` (Q.SPEC `j` TAKE_DROP_SUC)) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      impl_tac >- simp[] >>
      `EL j events = (j,SND (EL j events))` by metis_tac[PAIR] >>
      metis_tac[]) >>
  simp[EVERY_MEM] >> qx_gen_tac `kv` >> strip_tac >>
  fs[MEM_EL] >>
  `SUC j + n < LENGTH events` by decide_tac >>
  `FST (EL (SUC j + n) events) = SUC j + n /\
   SUC j + n < numslots` by metis_tac[current_full_events_index] >>
  gvs[EL_DROP]
QED

Theorem current_table_final_slots_events:
  current_table_final_slots table outs outs' /\
  MAP FST events = GENLIST I (LENGTH outs) ==>
  current_table_final_events table outs outs' events
Proof
  simp[current_table_final_slots_def, current_table_final_events_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (disj1_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      `?k. k < LENGTH events /\ kv = EL k events` by metis_tac[MEM_EL] >>
      `FST kv < LENGTH outs` by metis_tac[current_full_events_index] >>
      metis_tac[MEM_EL]) >>
  disj2_tac >>
  drule_all current_full_events_split >> strip_tac >>
  qexistsl_tac [`pre`, `j`, `value`, `post`] >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_singleton_agree_final_slots:
  current_singleton_agree table st st' /\
  current_indexed_writes outs events st after /\
  current_indexed_writes outs' events st' after' /\
  current_table_final_slots table outs outs' /\
  MAP FST events = GENLIST I (LENGTH outs) ==>
  current_singleton_agree table after after'
Proof
  rpt strip_tac >> irule current_singleton_agree_final_events >>
  metis_tac[current_table_final_slots_events]
QED

Theorem current_singleton_agree_repeated_destination:
  current_singleton_agree [("x","canonical")] st st' /\
  current_indexed_writes ["x";"x"] [(0,a);(1,b)] st after /\
  current_indexed_writes ["early";"canonical"] [(0,a);(1,b)] st' after' ==>
  current_singleton_agree [("x","canonical")] after after'
Proof
  rpt strip_tac >> irule current_singleton_agree_final_slots >>
  qexistsl_tac [`[(0,a);(1,b)]`, `["x";"x"]`, `["early";"canonical"]`, `st`, `st'`] >>
  simp[GENLIST, current_table_final_slots_def] >>
  qexists_tac `1` >> simp[]
QED
