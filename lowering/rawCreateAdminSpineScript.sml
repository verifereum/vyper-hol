(* A successful, unmarked administrative run inside one compiler band. *)
Theory rawCreateAdminSpine
Ancestors
  abiEncoderProps compileEnv fragGasOrigin venomExecSemantics
  venomInst venomState relation list

Definition admin_ok_spine_def:
  admin_ok_spine a b E ctx f s t <=>
    RTC (\p q. ?bb i.
      (p.vs_current_bb <> b.cs_current_bb \/
       p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
      lookup_block p.vs_current_bb f.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\
      i.inst_id IN frag_ids a b /\
      gas_origin_edge T E ctx f p [] (OK q)) s t
End

Theorem admin_ok_spine_refl[simp]:
  admin_ok_spine a b E ctx f s s
Proof
  simp[admin_ok_spine_def]
QED

Theorem admin_ok_spine_single:
  (s.vs_current_bb <> b.cs_current_bb \/
   s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_id IN frag_ids a b /\
  gas_origin_edge T E ctx f s [] (OK t) ==>
  admin_ok_spine a b E ctx f s t
Proof
  rewrite_tac[admin_ok_spine_def] >> disch_tac >> irule RTC_SINGLE >>
  BETA_TAC >> qexistsl_tac [`bb`,`i`] >> fs[]
QED

Theorem admin_ok_spine_trans:
  admin_ok_spine a b E ctx f s t /\ admin_ok_spine a b E ctx f t u ==>
  admin_ok_spine a b E ctx f s u
Proof
  rewrite_tac[admin_ok_spine_def] >> metis_tac[RTC_TRANS]
QED
