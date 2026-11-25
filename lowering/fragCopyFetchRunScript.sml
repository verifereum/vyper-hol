(* The guard describes the fetch, not the successor (which may be the exit). *)
Theory fragCopyFetchRun
Ancestors
  fragGasOrigin venomExecSemantics venomInst venomState relation

Definition copy_fetch_run_def:
  copy_fetch_run Q E C f = RTC (\s t.
    ?bb i. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    Q s.vs_current_bb s.vs_inst_idx i.inst_id /\
    gas_origin_edge F E C f s [] (OK t))
End

Theorem copy_fetch_run_nil[simp]:
  copy_fetch_run Q E C f s s
Proof
  simp[copy_fetch_run_def]
QED

Theorem copy_fetch_run_edge:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  Q s.vs_current_bb s.vs_inst_idx i.inst_id /\
  gas_origin_edge F E C f s [] (OK t) ==>
  copy_fetch_run Q E C f s t
Proof
  strip_tac >> simp[copy_fetch_run_def] >> irule RTC_SINGLE >>
  qexistsl_tac [`bb`,`i`] >> simp[]
QED

Theorem copy_fetch_run_trans:
  copy_fetch_run Q E C f s u /\ copy_fetch_run Q E C f u t ==>
  copy_fetch_run Q E C f s t
Proof
  simp[copy_fetch_run_def] >> metis_tac[RTC_TRANS]
QED
