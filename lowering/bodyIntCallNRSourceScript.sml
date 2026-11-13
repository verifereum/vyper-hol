(* Source lock operations are equivariant under replacement of scopes.
   This does not commute a failed lock past a function-stack push. *)
Theory bodyIntCallNRSource
Ancestors
  vyperInterpreter vyperState

Theorem intcall_lock_scopes:
  !cx nr view es sc.
    lock_if_nr cx nr view (es with scopes := sc) =
    let (r,ee) = lock_if_nr cx nr view es in (r,ee with scopes := sc)
Proof
  rpt gen_tac >>
  reverse (Cases_on `nr`) >- simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[lock_if_nr_def, acquire_nonreentrant_lock_def,
       ignore_bind_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def, raise_def] >>
  rpt IF_CASES_TAC >>
  gvs[update_transient_def, return_def, raise_def, bind_def]
QED

Theorem intcall_unlock_scopes:
  !cx nr view es sc.
    unlock_if_nr cx nr view (es with scopes := sc) =
    let (r,ee) = unlock_if_nr cx nr view es in (r,ee with scopes := sc)
Proof
  rpt gen_tac >>
  reverse (Cases_on `nr /\ ~view`) >-
    simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_def,
       bind_def, get_transient_storage_def, update_transient_def,
       return_def]
QED
