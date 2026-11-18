(* Raw-safety compatibility for the field-based C4 memory theorem. *)
Theory gasFocusFmpCutMemory
Ancestors
  gasFocusFmpCutFieldMemory o1SafeUpto o1LowerDloadPtrDiscipline
  lowerDloadPtrSupport o1ContractSimplifyCfgSrcFrame ptrStaticDiscipline
  unitMemInv allocaFrontierBound list

Theorem focus_fmp_cut_target_memory:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_pre 3 C3 C4 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ o1_safe_upto D eom n C3 root3 /\
  eom <= w2n root4.vs_initial_fmp /\ fmp_variant_room (SOME fmp) C4 root4 /\
  callee_first names C3.ctx_functions ==>
  mem_inv (\ctx fn inst t. gas_cut n root4 t ==> lowered_mem_fact eom ctx fn inst t)
    C4 root4
Proof
  strip_tac >>
  `fmp_free_ctx C3 /\ taint_within_upto D n C3 root3 /\
   ptr_discipline_upto eom n C3 root3 /\
   (!g i v. raw_reachable root3 C3 g i v /\ gas_cut n root3 v ==> dalloca_no_wrap i v)` by
    metis_tac[o1_safe_upto_def, o1_ptr_safe_upto_def, raw_mem_ok_def] >>
  irule focus_fmp_cut_target_memory_fields >> simp[] >>
  qexistsl [`C3`, `D`, `fmp`, `name`, `names`, `rp`, `src`, `src_lbl`] >>
  gvs[] >> conj_tac >- first_assum ACCEPT_TAC >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  simp[] >>
  `MEM fn C3.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    (drule frame_reachable_prov_supported >>
     disch_then (qspec_then `P` mp_tac) >> fs[EVERY_MEM]) >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM, fn_ptr_ok_static] >>
  `active_inst fn inst s` by metis_tac[scfg_frame_reachable_active] >>
  qexists `P` >> simp[] >>
  metis_tac[fn_static_ptr_ok_def, active_inst_mem_fn_insts, EVERY_MEM]
QED
