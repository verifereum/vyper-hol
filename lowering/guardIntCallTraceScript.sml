(* Trace-only boundaries: intermediate outputs prefix one selected trace. *)
Theory guardIntCallTrace
Ancestors
  vyperStorageTrace vyperState

Theorem selected_prefix_bind:
  storage_trace_frame (k v) /\
  m st = (INL v,mid) /\
  bind m k st = (res,out) /\
  (?sfx. selected = out.storage_trace ++ sfx) ==>
  ?sfx. selected = mid.storage_trace ++ sfx
Proof
  strip_tac >> gvs[bind_def] >>
  drule_all storage_trace_frame_prefix >> strip_tac >>
  metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem selected_prefix_finally:
  storage_trace_frame cleanup /\
  action st = (br,mid) /\
  finally action cleanup st = (res,out) /\
  (?sfx. selected = out.storage_trace ++ sfx) ==>
  ?sfx. selected = mid.storage_trace ++ sfx
Proof
  strip_tac >> Cases_on `cleanup mid` >>
  rename1 `cleanup mid = (cr,fin)` >>
  `?delta. fin.storage_trace = mid.storage_trace ++ delta` by
    metis_tac[storage_trace_frame_prefix] >>
  Cases_on `br` >> Cases_on `cr` >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def] >>
  metis_tac[listTheory.APPEND_ASSOC]
QED
