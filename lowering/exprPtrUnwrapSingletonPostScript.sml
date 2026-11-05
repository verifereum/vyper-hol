Theory exprPtrUnwrapSingletonPost
Ancestors
  exprPtrUnwrapSingleton exprSimStorageCopy slotCopyExecution venomInst
  words arithmetic

(* The singleton's concrete endpoint satisfies the same representation
   boundary as the loop. This reuses ordinary storage-content reconstruction. *)
Theorem copy_singleton_prefix:
  (loc = LocStorage \/ loc = LocTransient) /\
  t = (mstore (w2n addr)
    (slot_copy_word (if loc = LocStorage then SLOAD else TLOAD) s key)
    (update_var out
      (slot_copy_word (if loc = LocStorage then SLOAD else TLOAD) s key) s))
      with vs_inst_idx := ix ==>
  copy_prefix loc key (w2n addr) 1 s 1 t
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >>
  drule copy_singleton_static >> disch_tac >>
  drule copy_singleton_word >> disch_tac >>
  drule copy_singleton_exterior >> disch_tac >>
  simp[copy_prefix_def] >> conj_tac
  >- (rpt strip_tac >> `i = 0` by decide_tac >>
      gvs[slot_copy_word_def, copy_runtime_word_def]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
