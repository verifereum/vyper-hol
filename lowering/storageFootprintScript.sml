(* Finite observation counterpart of compileEnv's declared-region mask. *)
Theory storageFootprint
Ancestors
  compileEnv accountsRelProps vyperStorageFootprint vyperStorageFrame
  vyperValue
Libs
  wordsLib

(* Consistency supplies the mask's finite separation checks. *)
Theorem consistent_storage_dead_on:
  regions_consistent regions ==>
  (storage_dead_on (regions,locks) tr st j b <=>
   (tr ==> ~MEM j locks) /\
   ?slot tv. MEM (tr,slot,tv) regions /\ dead_bytes st (w2n slot) tv j b)
Proof
  rw[storage_dead_on_def] >> eq_tac >> strip_tac
  >- metis_tac[] >>
  qexistsl [`slot`, `tv`] >>
  fs[regions_consistent_def] >> metis_tac[]
QED


(* A second observation overlapping the inactive word keeps that word live. *)
Theorem nested_array_tail_observation:
  (storage_dead_on
     ([(F,0w,ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 1))],[])
     F (apply_writes 0w [(0,1w);(1,1w);(2,7w)] empty_storage) 3 b <=>
   b < 32) /\
  ~storage_dead_on
     ([(F,0w,ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 1));
      (F,3w,BaseTV (UintT 256))],[])
     F (apply_writes 0w [(0,1w);(1,1w);(2,7w)] empty_storage) 3 b
Proof
  conj_tac
  >- (simp[storage_dead_on_def, type_slot_size_def, ranges_disjoint_def,
           dead_bytes_def] >> EVAL_TAC >> simp[] >>
      eq_tac >- metis_tac[] >> strip_tac >> qexists_tac `1` >> simp[]) >>
  strip_tac >>
  drule_at Any (Q.INST [`w` |-> `3w`, `tv` |-> `BaseTV (UintT 256)`]
    observed_storage_region_read_live) >>
  simp[type_slot_size_def, dead_bytes_def]
QED
