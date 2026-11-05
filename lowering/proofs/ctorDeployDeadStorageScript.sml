(* Storage agreement up to dead bytes: the facts the deploy dead-transport
 * needs.  Copies of e2eComposition's [local] helpers, kept here until
 * e2eComposition exports them.
 *)
Theory ctorDeployDeadStorage
Ancestors
  ptrDiscipline compileEnv accountsRelProps

Theorem storage_agree_except_storage_dead:
  storage_agree_except {(k,b) | storage_dead cx tr st (w2n k) b} st st' <=>
  storage_agree (storage_dead cx tr st) st st'
Proof
  simp[storage_agree_except_def, word_agree_except_def, key_taint_def,
       storage_agree_def, vfmStateTheory.lookup_storage_def] >>
  metis_tac[]
QED

Theorem storage_agree_except_empty:
  storage_agree_except {} st st' <=> st' = st
Proof
  simp[storage_agree_except_def, word_agree_except_def, key_taint_def,
       FUN_EQ_THM] >>
  metis_tac[word_to_bytes_EL_eq]
QED

Theorem storage_agree_dead_trans:
  storage_agree (storage_dead cx tr st0) st0 st1 /\
  storage_agree (storage_dead cx tr st1) st1 st2 ==>
  storage_agree (storage_dead cx tr st0) st0 st2
Proof
  strip_tac >>
  `storage_dead cx tr st1 = storage_dead cx tr st0` by
    (irule storage_agree_storage_dead >> simp[]) >>
  gvs[storage_agree_def]
QED
