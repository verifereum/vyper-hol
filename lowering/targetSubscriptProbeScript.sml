(* Relation-level probes only: not a counterexample to target_case. *)
Theory targetSubscriptProbe
Ancestors
  compileEnv vyperStoragePlaceRegion vyperStorageLayoutSafety vfmState
  words finite_map combin vyperValue

Theorem nested_capacity_probe:
  storage_subregion
    (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] 1
    (ArrayTV (BaseTV BoolT) (Dynamic 1))
Proof
  EVAL_TAC >> simp[]
QED

(* Conditional on a declared isolated region. Inhabitation of a full context
   and reachability after an actual index are separate obligations. *)
Theorem nested_dead_header_discrepancy_probe:
  !cx mid name subs st.
    declared_storage_region cx mid name subs =
      SOME (F,0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) /\
    (!mid' name' subs' slot' tv'.
      declared_storage_region cx mid' name' subs' = SOME (F,slot',tv') /\
      (slot',tv') <>
        (0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) ==>
      ranges_disjoint 0 3 (w2n slot') (type_slot_size tv')) /\
    lookup_storage 0w st = 0w /\ lookup_storage 1w st = 0w ==>
    storage_agree (storage_dead cx F st) st (update_storage 1w 1w st) /\
    lookup_storage 0w (update_storage 1w 1w st) = 0w /\
    lookup_storage 1w st <> lookup_storage 1w (update_storage 1w 1w st)
Proof
  rpt strip_tac
  >- (simp[storage_agree_def] >> rpt strip_tac >>
      Cases_on `k = 1w`
      >- (gvs[] >>
          `storage_dead cx F st 1 b` by
            (pure_rewrite_tac[storage_dead_def] >>
             qexistsl [`mid`,`name`,`subs`,`0w`,
               `ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)`] >>
             simp[type_slot_size_def, dead_bytes_def, dimword_def,
                  fcpLib.INDEX_CONV ``dimindex (:256)``] >>
             rpt strip_tac >> first_x_assum irule >> simp[] >>
             goal_assum (drule_at Any)) >>
          gvs[]) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM])
  >- gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
  >> gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED
