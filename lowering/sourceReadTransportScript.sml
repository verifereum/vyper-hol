Theory sourceReadTransport
Ancestors
  exprSimSubscriptArraySource vyperStorageBackend vyperStatePreservation
  vyperState vyperInterpreter

Theorem read_result_source_fields_frame:
  s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
  (!tr. get_storage cx s' tr = get_storage cx s tr) ==>
  FST (read_result cx r s') = FST (read_result cx r s)
Proof
  strip_tac >>
  Cases_on `?tr slot vt. r = PlaceR (StoragePlace tr slot vt)`
  >- (gvs[] >>
      simp[read_result_def, read_place_def, read_storage_slot_eq] >>
      CASE_TAC >> simp[]) >>
  irule read_result_nonstorage_frame >> gvs[]
QED

Theorem read_result_source_fields_success:
  s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
  (!tr. get_storage cx s' tr = get_storage cx s tr) /\
  read_result cx r s' = (INL v,s') ==>
  read_result cx r s = (INL v,s)
Proof
  strip_tac >> drule_all read_result_source_fields_frame >>
  Cases_on `read_result cx r s` >> simp[] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  first_x_assum (qspec_then `r` mp_tac) >> simp[]
QED
