  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`] mp_tac
    opt_entry_initial_venom_state_rel >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `rpolicy`,
               `out.po_unit`] mp_tac opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `opt_entry_state prog prog' cplan es`] mp_tac opt_entry_fields >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  (* The Venom run sees the unoptimized code: run the source side on txp. *)
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     drule code_layout_valid_code_length >> simp[]) >>
  `source_deployment_rel tops am txp` by
    (simp[Abbr `txp`, source_deployment_rel_code_update] >>
     fs[call_state_rel_def]) >>
