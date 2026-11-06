(* Common observation and zero-prefix transport below storage-place consumers. *)
Theory augAssignPtrStorageCommon
Ancestors
  vyperInterpreter vyperState vyperStorageBackend gasSummaryComposePtr
  fragGasPathPtr fragGasSeqPtr gasSummary gasCount gasContext

Theorem read_storage_slot_gas_obs_ptr:
  read_storage_slot cx tr slot tv es = (res,ee) ==>
  read_storage_slot cx tr slot tv (es with gas_obs := gs) =
    (res,ee with gas_obs := gs)
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def, get_accounts_def,
       get_transient_storage_def, bind_def, return_def, lift_option_def,
       AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `decode_value storage offset tv` >>
  Cases_on `decode_value storage offset tv` >> simp[return_def, raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem gas_marked_exec_ptr_zero_prefix:
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG source
    (es with gas_obs := [],t,H,tm) marks res ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG source
    (es,s0,G,tn) marks res ee J un r
Proof
  strip_tac >> drule gas_path_ptr_ok_suffix >> simp[] >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
