(* Confinement of the saved ABI-row materialization at its restore cut. *)
Theory entryCreateAbiRestoreScope
Ancestors
  entryCreatePathScope createCtorSegmentArrival
  createSizePrefixReplay createMarkedPath fragGasOrigin gasEvents
  fragExec compileEnv venomState venomExecSemantics venomExecProofs
  venomInst relation list pred_set

Theorem abi_restore_band_prefix:
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
       i.inst_id NOTIN frag_ids a b) /\
  (!u i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b ==>
       i.inst_opcode <> GAS) /\
  ~s.vs_halted /\
  RTC (\u v. ?i. ctor_segment_fetch f u = SOME i /\
               i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ctor_segment_next f u i = SOME v) s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  strip_tac >>
  `!u v i. ~u.vs_halted /\ ctor_segment_fetch f u = SOME i /\
      i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
      ctor_segment_next f u i = SOME v ==>
      ~v.vs_halted /\ create_expr_prefix a b E C f u [] v` by
    (rpt gen_tac >> strip_tac >>
     `?bb. lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME i` by
       fs[ctor_segment_fetch_def, AllCaseEqs()] >>
     `u.vs_current_bb <> b.cs_current_bb \/ u.vs_inst_idx <> LENGTH b.cs_current_insts` by
       metis_tac[] >>
     `i.inst_opcode <> GAS` by metis_tac[] >>
     `gas_origin_edge F E C f u [] (OK v) /\ ~v.vs_halted` by
       (qpat_x_assum `ctor_segment_next _ _ _ = _` mp_tac >>
        simp[ctor_segment_next_def, ctor_segment_entry_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[] >>
        imp_res_tac step_inst_base_OK_preserves_halted >>
        TRY (qpat_assum `OK _ = eval_phis _ _` (assume_tac o SYM) >>
             drule eval_phis_preserves_halted >> strip_tac) >>
        gvs[gas_origin_edge_def] >> qexists_tac `0` >>
        simp[step_inst_non_invoke, Once gas_events_step_def] >> metis_tac[]) >>
     simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  qabbrev_tac `P = \u. ~u.vs_halted /\ create_expr_prefix a b E C f s [] u` >>
  `P t` suffices_by simp[Abbr `P`] >>
  irule RTC_lifts_invariants >> first_assum (irule_at Any) >>
  conj_tac >- simp[Abbr `P`] >>
  simp_tac bool_ss [Abbr `P`, PULL_EXISTS] >> rpt strip_tac >>
  qpat_assum `!u v i. _ ==> ~v.vs_halted /\ _` (drule_all_then strip_assume_tac) >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED
