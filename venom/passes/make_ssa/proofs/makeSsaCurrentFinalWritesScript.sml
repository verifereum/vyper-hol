Theory makeSsaCurrentFinalWrites
Ancestors makeSsaCurrentInstructionSingleton makeSsaCurrentValueInvariant
  makeSsaCurrentPairedWrites venomState finite_map list

(* Only final effective writes matter; the earlier prefix may write either key. *)
Definition current_table_final_events_def:
  current_table_final_events table outs outs' events <=>
    !v n. MEM (v,n) table ==>
      EVERY (\kv. EL (FST kv) outs <> v /\ EL (FST kv) outs' <> n) events \/
      ?pre j value post. events = pre ++ (j,value)::post /\
        EL j outs = v /\ EL j outs' = n /\
        EVERY (\kv. EL (FST kv) outs <> v /\ EL (FST kv) outs' <> n) post
End

Theorem current_singleton_agree_final_events:
  current_singleton_agree table st st' /\
  current_indexed_writes outs events st after /\
  current_indexed_writes outs' events st' after' /\
  current_table_final_events table outs outs' events ==>
  current_singleton_agree table after after'
Proof
  simp[current_singleton_agree_def, current_indexed_writes_def,
    current_table_final_events_def, lookup_var_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (`EVERY (\kv. EL (FST kv) outs <> v) events /\
       EVERY (\kv. EL (FST kv) outs' <> n) events` by
        (gvs[EVERY_MEM] >> metis_tac[]) >>
      simp[current_indexed_fold_avoids]) >>
  gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule current_indexed_fold_last_pair >> simp[]
QED
