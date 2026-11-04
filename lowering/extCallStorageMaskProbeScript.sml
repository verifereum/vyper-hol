(* Diagnostic only: this is not a counterexample to compile_extcall_case. *)
Theory extCallStorageMaskProbe
Ancestors compileEnv vyperState vyperValue vfmState words venomMemProps

Definition mask_store_def:
  mask_store len child = update_storage 0w len (update_storage 1w child (K 0w))
End

Theorem empty_child_dead:
  !child j b.
    dead_bytes (mask_store 0w child) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) j b <=>
    j = 1 /\ b < 32
Proof
  simp[dead_bytes_def, mask_store_def, lookup_storage_def,
       update_storage_def, type_slot_size_def]
QED

Theorem nonempty_child_live:
  !child j b.
    ~dead_bytes (mask_store 1w child) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) j b
Proof
  simp[dead_bytes_def, mask_store_def, lookup_storage_def,
       update_storage_def, type_slot_size_def]
QED

Theorem captured_child_reads_differ:
  lookup_storage 1w (mask_store 0w 7w) = 7w /\
  lookup_storage 1w (mask_store 0w 9w) = 9w /\ (7w:bytes32) <> 9w
Proof
  EVAL_TAC >> simp[dimword_def, dimindex_256]
QED

(* A local dead-byte predicate only; no declared-region context is asserted. *)
Theorem child_difference_masked_locally:
  storage_agree
    (dead_bytes (mask_store 0w 7w) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))
    (mask_store 0w 7w) (mask_store 0w 9w)
Proof
  simp[storage_agree_def, empty_child_dead] >> rpt strip_tac >>
  `k <> 1w` by (strip_tac >> gvs[]) >>
  simp[mask_store_def, lookup_storage_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

(* Every context that actually declares this child dead fails the child
   live-read test. This conditional fact is not a stmt_state_rel witness. *)
Theorem dead_child_not_read_live:
  storage_dead cx tr (mask_store 0w child) 1 0 ==>
  ~storage_read_live cx tr (mask_store 0w child) 1w
    (BaseTV (UintT 256))
Proof
  simp[storage_read_live_def, dead_bytes_def, type_slot_size_def] >>
  strip_tac >> qexistsl_tac [`1`,`0`] >> simp[]
QED
