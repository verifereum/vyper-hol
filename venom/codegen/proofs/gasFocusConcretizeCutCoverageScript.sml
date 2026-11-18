Theory gasFocusConcretizeCutCoverage
Ancestors
  concretizePtrStagePairedBridge concretizePtrStagePlacements
  concretizePtrImportOrigins concretizePtrPairedFields
  concretizeStageShape concretizeStepStructure
  o1PassContract venomWf venomInst unitShapeDefs concretizeMemLocDefs
  venomPassDispatcher
  o1SafeUpto list finite_map

(* The pairing is determined by the stage's static layout equations. No
   execution, including one outside the cut, is needed to construct it. *)
Theorem concretize_cut_paired_row[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ptr_stage_placements C' positions /\ i < LENGTH C.ctx_functions /\
  R (EL i C.ctx_functions) (EL i C'.ctx_functions) ==>
  ?p. ptr_paired_code R (K p) positions (EL i C.ctx_functions) (EL i C'.ctx_functions) /\
    (!inst. MEM inst (fn_insts (EL i C.ctx_functions)) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP p (Allocation inst.inst_id)))
Proof
  strip_tac >> gvs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < _ ==> ?observed s out. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `MEM (EL i C.ctx_functions) C.ctx_functions /\
   MEM (EL i C'.ctx_functions) C'.ctx_functions` by metis_tac[EL_MEM] >>
  `(EL i C.ctx_functions).fn_eom = NONE` by fs[EVERY_MEM] >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  drule_all concretize_function_fresh_positions >> strip_tac >>
  `!bb inst. MEM bb (EL i C.ctx_functions).fn_blocks /\
     MEM inst bb.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
     FLOOKUP layout.cl_positions (Allocation inst.inst_id) =
       OPTION_MAP FST (FLOOKUP positions (Allocation inst.inst_id))` by
    (rpt gen_tac >> strip_tac >> irule ptr_layout_stage_lookup >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexists_tac `layout.cl_positions` >>
  simp[ptr_paired_code_def, apply_context_concretize_layout_def,
       apply_concretize_layout_def] >>
  conj_tac >-
    (mp_tac (Q.SPECL [`layout.cl_positions`,`EL i C.ctx_functions`]
       (GEN_ALL concretize_positions_entry_label)) >>
     simp[fn_entry_label_def, entry_block_def]) >>
  metis_tac[]
QED

Theorem concretize_cut_stage_pairing[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ptr_safe_upto D lo n C vs /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name)
Proof
  strip_tac >> fs[o1_ptr_safe_upto_def] >>
  drule_all ptr_stage_placements_exists >> strip_tac >>
  drule ptr_stage_names >> simp[ctx_fn_names_def] >> strip_tac >>
  `LENGTH C.ctx_functions = LENGTH C'.ctx_functions` by metis_tac[LENGTH_MAP] >>
  `!i. i < LENGTH C.ctx_functions ==>
       (EL i C'.ctx_functions).fn_name = (EL i C.ctx_functions).fn_name` by
    (rpt strip_tac >>
     qpat_assum `MAP _ C.ctx_functions = MAP _ C'.ctx_functions`
       (mp_tac o AP_TERM (Term `EL i : string list -> string`)) >>
     simp[EL_MAP]) >>
  `ALL_DISTINCT C.ctx_functions` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
        ctx_fn_names_def] >> metis_tac[ALL_DISTINCT_MAP]) >>
  qabbrev_tac `R = \f g. ?i. i < LENGTH C.ctx_functions /\
    f = EL i C.ctx_functions /\ g = EL i C'.ctx_functions` >>
  `!f. MEM f C.ctx_functions ==> ?p.
     (!g. R f g ==> ptr_paired_code R (K p) positions f g) /\
     (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP p (Allocation inst.inst_id)))` by
    (rpt strip_tac >>
     qpat_x_assum `MEM f C.ctx_functions`
       (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     rename1 `j < LENGTH C.ctx_functions` >>
     qpat_x_assum `f = EL j C.ctx_functions` SUBST_ALL_TAC >>
     `R (EL j C.ctx_functions) (EL j C'.ctx_functions)` by
       (simp[Abbr `R`] >> metis_tac[]) >>
     drule_all concretize_cut_paired_row >> strip_tac >>
     qexists_tac `p` >> simp[] >> rpt strip_tac >>
     `g = EL j C'.ctx_functions` by (fs[Abbr `R`] >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
     simp[]) >>
  qpat_x_assum `!f. MEM f _ ==> ?p. _`
    (qx_choose_then `lp` assume_tac o
     SIMP_RULE bool_ss [cardinalityCoreTheory.RIGHT_IMP_EXISTS_THM, SKOLEM_THM]) >>
  `!f. MEM f C.ctx_functions ==>
     (!g. R f g ==> ptr_paired_code R lp positions f g) /\
     (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id)))` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!f. MEM f _ ==> _` (drule_then mp_tac) >>
     pure_rewrite_tac[ptr_paired_code_def, combinTheory.K_THM] >> simp[]) >>
  `LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `R (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` by
       (simp[Abbr `R`] >> metis_tac[]) >> metis_tac[EL_MEM]) >>
  qexistsl [`R`,`lp`,`positions`] >> simp[] >>
  conj_tac
  >- (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
         wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN, EVERY_EL, ptr_paired_code_def,
         o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >>
      rpt strip_tac >>
      qpat_x_assum `!i. _ ==> _ /\ _` (drule_then strip_assume_tac) >>
      fs[fn_labels_def] >> metis_tac[concretize_positions_labels, fn_labels_def, EL_MEM]) >>
  simp[ptr_paired_code_def, Abbr `R`] >> metis_tac[]
QED
