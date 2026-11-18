Theory gasFocusConcretizeCutFrameSupport
Ancestors
  concretizeStageStatic ptrStaticDiscipline lowerDloadPtrSupport
  ctxLookupAgreeHelpers frameAllocationHistory allocaFrontierBound
  o1SafeUpto o1PassContract unitMemInv unitTransformDefs
  lowerDloadPtrRawReachable stepWriteFootprintBase ptrDiscipline
  venomInst finite_map pred_set list

Theorem static_invoke_prov_supported[local]:
  fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  FDOM G SUBSET fn_pv P fn ==>
  !k. k < LENGTH ops /\
      EL k (MAP (op_prov G) ops) <> NONE ==> k IN P nm
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  gvs[ptr_use_static_ok_def] >> rpt strip_tac >> gvs[EL_MAP] >>
  spose_not_then assume_tac >>
  `op_prov G (EL k ops) = NONE` by
    (irule op_prov_outside_support >> qexists `fn_pv P fn` >>
     simp[] >> metis_tac[]) >>
  gvs[]
QED

(* In particular, the same parameter-position witness is used at each push
   and saved on the stack for the matching return. *)
Theorem static_frame_prov_supported[local]:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !P. (!f. MEM f C.ctx_functions ==> fn_static_ptr_ok P f) ==>
      MEM fn C.ctx_functions /\
      FDOM G SUBSET fn_pv P fn /\
      (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN P fn.fn_name) /\
      (!f. MEM f stk ==>
        MEM f.cf_fn C.ctx_functions /\
        FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
        (!k. k < LENGTH f.cf_params /\ EL k f.cf_params <> NONE ==>
             k IN P f.cf_fn.fn_name))
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> drule venomInstTheory.lookup_function_MEM >>
      rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
      simp[] >> irule step_prov_supported >> simp[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[] >> irule entry_prov_supported >> simp[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `MEM fn' C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
      `fn'.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
      `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
      `fn_static_ptr_ok P fn` by metis_tac[] >>
      simp[] >> conj_tac
      >- metis_tac[static_invoke_prov_supported]
      >> rpt strip_tac >> gvs[])
  >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM f.cf_fn C.ctx_functions /\ FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
   (!k. k < LENGTH f.cf_params /\ EL k f.cf_params <> NONE ==>
        k IN P f.cf_fn.fn_name)` by metis_tac[MEM] >>
  simp[FDOM_DRESTRICT] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem focus_concretize_cut_frame_support:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_safe_upto D lo n C vs /\ o1_initial_state_ok vs /\
  o1_ctx_shape C' /\ EVERY (o1_fn_row 3) C'.ctx_functions /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
    C' vs /\
  frame_reachable vs C' stk PG G tn fn inst s /\ gas_cut n vs s ==>
  (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
       FDOM G SUBSET fn_pv P fn) /\
  allocas_from eom s /\ (ctx_has_dalloca C' ==> allocas_below_fmp s)
Proof
  strip_tac >>
  `?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    (gvs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def,
         EVERY_MEM] >> metis_tac[fn_ptr_ok_static]) >>
  drule_all concretize_stage_static_ptr_ok >> strip_tac >>
  `MEM fn C'.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    (drule static_frame_prov_supported >>
     disch_then (qspec_then `P` mp_tac) >> impl_tac
     >- metis_tac[EVERY_MEM]
     >> simp[]) >>
  conj_tac
  >- (qexists `P` >> simp[] >>
      `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >> simp[] >>
      `MEM inst (fn_insts fn)` by
        metis_tac[lowerDloadPtrRawReachableTheory.frame_reachable_raw,
                  raw_reachable_active, active_inst_mem_fn_insts] >>
      metis_tac[fn_static_ptr_ok_def]) >>
  `o1_fn_row 3 fn` by metis_tac[EVERY_MEM] >>
  `!ai. MEM ai (fn_insts fn) ==> ai.inst_opcode <> ALLOCA` by
    gvs[o1_fn_row_def, EVERY_MEM] >>
  `vs.vs_allocas = FEMPTY` by gvs[o1_initial_state_ok_def] >>
  `!id off sz. FLOOKUP s.vs_allocas id <> SOME (off,sz)` by
    metis_tac[frame_reachable_current_allocation_syntax] >>
  `raw_reachable vs C' fn inst s` by
    metis_tac[lowerDloadPtrRawReachableTheory.frame_reachable_raw] >>
  `static_mem_ok eom C' fn inst s` by
    (qpat_x_assum `mem_inv _ _ _` mp_tac >>
     simp[mem_inv_raw_reachable] >> metis_tac[]) >>
  simp[allocas_from_def, allocas_below_fmp_def] >>
  metis_tac[static_mem_ok_def]
QED
