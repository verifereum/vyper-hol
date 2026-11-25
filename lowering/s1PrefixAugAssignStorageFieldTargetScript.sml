Theory s1PrefixAugAssignStorageFieldTarget
Ancestors
  bodyAugPlaceTarget s1PrefixFrame s1PrefixNames vyperStorageTrace
  vyperPlaceFrames vyperInterpreter vyperState

Theorem extend_attr_state[local]:
  extend_place cx v (AttrSubscript fld) st = (res,st') ==> st' = st
Proof
  Cases_on `v`
  >- simp[extend_place_def, raise_def]
  >- metis_tac[extend_place_PlaceR_state] >>
  simp[extend_place_def, raise_def]
QED

Theorem storage_field_target_no_outcome[local]:
  eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld) st =
    (res,ee) ==>
  EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
    (DROP (LENGTH st.storage_trace) ee.storage_trace)
Proof
  simp[evaluate_def, bind_def] >>
  namedCases_on `lookup_global cx src id st` ["result mid"] >>
  drule lookup_global_no_outcome >>
  Cases_on `result` >> simp[]
  >- (namedCases_on `extend_place cx x (AttrSubscript fld) mid` ["extended after"] >>
      drule_then SUBST_ALL_TAC extend_attr_state >>
      Cases_on `extended` >> simp[] >>
      rpt strip_tac >> imp_res_tac get_place_state >> gvs[]) >>
  rw[] >> first_assum ACCEPT_TAC
QED

Theorem augassign_storage_field_target_prefix_entry:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
  supported_storage_field_write tops nsid fld ==>
  (?pt. supported_target_info tops bindings
     (AttributeTarget (TopLevelNameTarget nsid) fld) = SOME pt) /\
  ~immutable_root cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
  (!P st0 es s G tn. ~s.vs_halted ==>
    gas_prefix_full P cx st0
      (eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld))
      (es,s,G,tn))
Proof
  strip_tac >> conj_tac
  >- (irule aug_place_supported_stmt_target_info >>
      qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[aug_place_storage_field_root] >>
  PairCases_on `nsid` >> rpt strip_tac >>
  irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
  rpt strip_tac >> drule storage_field_target_no_outcome >> simp[]
QED
