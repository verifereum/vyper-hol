(*
 * FmpLowering's coverage invariant (fmp_cov, used by fmpStageCoverage) and
 * the memory fact of every covered target state.
 *
 * TOP-LEVEL:
 *   fmp_cov_stack, fmp_cov - the coverage invariant
 *   fmp_stage_invoke_inst  - an INVOKE's image is an INVOKE
 *   fmp_cov_mem            - a covered state's memory fact
 *)
Theory fmpStageCoverInv
Ancestors
  fmpStageCoverMem lowerDloadPtrRawReachable fmpStageOpBase fmpStageControl fmpStageRel fmpStepLayout
  o1PassContract ptrDiscipline contextCodegenRel codegenRel unitMemInv
  fmpReclaimDefs fmpAnalysisDefs fmpLowerDefs analysisSimDefs
  passSimulationDefs venomExecSemantics venomExecProps venomWf venomState
  venomInst finite_map words list rich_list fmpStageControlWalk fmpLowerIndexedProps

(* The target's call stack mirrors the source's: each saved target frame
   is the state ts saved at the matching source call, in the lowered
   caller, at its INVOKE. *)
Definition fmp_cov_stack_def:
  (fmp_cov_stack C' [] [] [] <=> T) /\
  (fmp_cov_stack C' (f::stk) ((tc,lc)::ts) (g::stk') <=>
     g.cf_state = tc /\
     lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME g.cf_fn /\
     active_inst g.cf_fn g.cf_inst tc /\
     fmp_cov_stack C' stk ts stk') /\
  (fmp_cov_stack C' _ _ _ <=> F)
End

(* A target state of the lowered fn' is covered when it runs only
   inserted instructions, in its block, up to a state t1 related to a
   reachable source point, or when it is past the RETURNDATACOPY of a
   revert forwarding of its block.  The relation is past the point's
   restore (restored) only where a step lemma needs it: at a DALLOCA, an
   INVOKE or a terminator. *)
Definition fmp_cov_def:
  fmp_cov D C C' vs vs' fmp eom stk' fn' t <=>
    (?stk PG G tn fn inst s sm lo t1 ts restored bb'.
       frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
       ~s.vs_halted /\
       (restored ==>
          MEM inst.inst_opcode [DALLOCA; INVOKE] \/
          is_terminator inst.inst_opcode) /\
       fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
         stk PG G tn fn s lo t1 ts /\
       lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       fmp_cov_stack C' stk ts stk' /\
       t.vs_current_bb = t1.vs_current_bb /\
       lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       t.vs_inst_idx <= t1.vs_inst_idx /\
       (!k. fmp_target_run k C' fn.fn_name t
              (t1.vs_inst_idx - t.vs_inst_idx) t1) /\
       !i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb'.bb_instructions /\
           fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) \/
    (?bb' p j. ALL_DISTINCT (fn_labels fn') /\
       lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       revert_forward_pair bb' p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j)
End

Theorem fmp_cov_walk_invoke_head[local]:
  fmp_lower_indexed infos ctx runner lbl k s rs (inst::xs) = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  inst.inst_opcode = INVOKE ==>
  (if (lbl,k) IN FDOM plan then 1 else 0) < LENGTH out /\
  (EL (if (lbl,k) IN FDOM plan then 1 else 0) out).inst_opcode = INVOKE
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  qpat_x_assum `fmp_lower_inst _ _ _ _ _ = _` mp_tac >>
  simp[fmp_lower_inst_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST1_TAC o GSYM) >>
  simp[EL_APPEND_EQN]
QED

Theorem fmp_cov_invoke_suffix[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb'. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions idx +
      (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    (EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions idx +
      (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions).inst_opcode = INVOKE
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `idx <= LENGTH bb.bb_instructions` by decide_tac >>
  drule_all fmp_stage_tidx_code >> strip_tac >>
  `DROP idx bb.bb_instructions =
    EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  qpat_x_assum `DROP idx bb.bb_instructions = _` SUBST_ALL_TAC >>
  drule_all fmp_cov_walk_invoke_head >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  qpat_x_assum `DROP _ bb'.bb_instructions = code` (SUBST_ALL_TAC o GSYM) >>
  qmatch_asmsub_abbrev_tac `offset < LENGTH (DROP pos bb'.bb_instructions)` >>
  `offset + pos < LENGTH bb'.bb_instructions` by fs[LENGTH_DROP] >>
  fs[EL_DROP] >> simp[arithmeticTheory.ADD_COMM]
QED

(* Why: the lowering rewrites an INVOKE into one INVOKE (with the runner
   appended to its arguments and outputs when the callee takes or
   publishes the FMP), at the control map's index past its restore. *)
Theorem fmp_stage_invoke_inst:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    (EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
           (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
         (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
       bb'.bb_instructions).inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (Cases_on `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
        bb.bb_label = rl ==> rp <= idx`
      >- (drule fmp_cov_invoke_suffix >>
          disch_then (qspecl_then [`idx`, `bb`] mp_tac) >> gvs[]) >>
      gvs[NOT_FORALL_THM] >>
      `idx < rp` by decide_tac >>
      drule fmp_control_kept_prefix >>
      disch_then (qspec_then `rp` mp_tac) >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `idx` mp_tac) >>
      simp[] >> disch_then (qx_choose_then `target` strip_assume_tac) >>
      qexists_tac `target` >>
      `SUM (GENLIST (\j. (if (bb.bb_label,j) IN FDOM (fmp_stage_plan infos ctx fn)
          then 1 else 0) +
        (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx)
        = idx` by
        (irule fmp_control_width_one >> rpt strip_tac >>
         `j <= idx` by decide_tac >>
         qpat_x_assum `!j. j <= idx ==> _` drule >> simp[]) >>
      `~((bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
        (qpat_x_assum `!j. j <= idx ==> _` (qspec_then `idx` mp_tac) >> simp[]) >>
      simp[fmp_stage_tidx_def]) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  drule_all fmp_control_unlowered_no_raw >> strip_tac >>
  `!j. j < idx ==> (EL j bb.bb_instructions).inst_opcode <> DALLOCA` by
    (rpt strip_tac >>
     gvs[no_raw_fmp_ops_def, fn_insts_def, fn_insts_blocks_def,
         MEM_FLAT, MEM_MAP, is_raw_fmp_opcode_def] >>
     `j < LENGTH bb.bb_instructions` by decide_tac >>
     `MEM (EL j bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
       (irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
        qexists_tac `bb` >> simp[EL_MEM]) >>
     first_x_assum drule >> simp[is_raw_fmp_opcode_def]) >>
  qexists_tac `bb` >> simp[fmp_stage_tidx_def] >>
  `SUM (GENLIST (\j. (if (lbl,j) IN FDOM (FEMPTY:fmp_reclaim_plan) then 1 else 0) +
    (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx) = idx` by
    (irule fmp_control_width_one >> simp[]) >>
  gvs[]
QED

Theorem fmp_cov_quiet[local]:
  fmp_inserted_op ti.inst_opcode \/ MEM ti.inst_opcode [INVOKE; PHI] ==>
  lowered_mem_ok eom f C' fn' ti t
Proof
  rw[fmp_inserted_op_def, lowered_mem_ok_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem fmp_cov_tidx_lt:
  fmp_stage_tidx plan root lbl insts idx +
  (if (lbl,idx) IN FDOM plan then 1 else 0) <
  fmp_stage_tidx plan root lbl insts (SUC idx) /\
  fmp_stage_tidx plan root lbl insts idx <
  fmp_stage_tidx plan root lbl insts (SUC idx)
Proof
  rw[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >> BasicProvers.every_case_tac >> fs[]
QED

Theorem fmp_cov_target_distinct:
  fmp_stage_lowered infos ctx runner fn fn' /\ ALL_DISTINCT (fn_labels fn) ==>
  ALL_DISTINCT (fn_labels fn')
Proof
  rw[fmp_stage_lowered_def] >>
  `fmp_lower_function ctx sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  drule fmp_lower_function_preserves_labels >> simp[]
QED

Theorem fmp_cov_frame_pos:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?infos ctx runner.
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\ w2n t.vs_initial_fmp = fmp0 /\
    !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
      t.vs_inst_idx =
        fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
          s.vs_inst_idx +
        (if restored /\
            (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
         then 1 else 0)
Proof
  rw[fmp_stage_rel_def, fmp_frame_rel_def, LET_THM] >> gvs[] >>
  qexistsl [`infos`, `ctx`, `runner`] >> simp[]
QED

(* A state past a revert forwarding's RETURNDATACOPY is at an ASSIGN or at
   its REVERT. *)
Theorem fmp_cov_tail_mem[local]:
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  revert_forward_pair bb' p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j /\
  get_instruction bb' t.vs_inst_idx = SOME ti ==>
  lowered_mem_ok eom f C' fn' ti t
Proof
  rpt strip_tac >>
  Cases_on `t.vs_inst_idx = j`
  >- (simp[lowered_mem_ok_def, in_revert_forward_def, revert_forward_at_def] >>
      metis_tac[]) >>
  irule fmp_cov_quiet >> simp[fmp_inserted_op_def] >>
  fs[revert_forward_pair_def] >>
  `ti.inst_opcode = ASSIGN` by
    (first_x_assum irule >> qexists_tac `t.vs_inst_idx` >> simp[]) >>
  simp[]
QED

Theorem fmp_cov_forward_no_plan[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  (revert_forward_pair bb idx j \/ revert_forward_pair bb j idx) ==>
  ~((lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn))
Proof
  rpt strip_tac >> drule_all fmp_stage_plan_point >>
  gvs[revert_forward_pair_def, get_instruction_def, fmp_is_reclaim_point_def,
      fmp_callee_info_def, fmp_invoke_target_def]
QED

Theorem fmp_target_run_zero:
  fmp_target_run k C' name t 0 t' ==> t' = t
Proof
  rw[fmp_target_run_def, run_insts_def] >>
  simp[venom_state_component_equality]
QED

Theorem fmp_cov_target_labels:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ALL_DISTINCT (fn_labels fn')
Proof
  rpt strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  irule fmp_cov_target_distinct >>
  fs[o1_fn_shape_def, wf_function_def] >> metis_tac[]
QED

(* At a state related to a reachable source point: the restore and the
   expansions are inserted, a revert forwarding maps to one, an INVOKE or
   PHI touches no memory, and a kept instruction is fmp_stage_kept_mem's. *)
Theorem fmp_cov_point_mem[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ti t ==>
  lowered_mem_ok eom (w2n t.vs_initial_fmp) C' fn' ti t
Proof
  rpt strip_tac >> Cases_on `restored` >>
  (
    drule_all fmp_cov_target_labels >> strip_tac >>
    drule_all fmp_stage_frame_facts >> strip_tac >>
    drule_all fmp_cov_frame_pos >> strip_tac >>
    `ALL_DISTINCT (fn_labels fn)` by fs[o1_fn_shape_def, wf_function_def] >>
    `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb s.vs_inst_idx = SOME inst` by
      metis_tac[active_inst_block_lookup] >>
    `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
          get_instruction bt t.vs_inst_idx = SOME ti` by
      metis_tac[active_inst_block_lookup] >>
    qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
    qpat_x_assum `get_instruction bb _ = _` mp_tac >>
    simp[get_instruction_def] >> strip_tac >> gvs[] >>
    Cases_on `((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn) /\
               t.vs_inst_idx =
                 fmp_stage_tidx (fmp_stage_plan infos ctx fn)
                   (fmp_stage_root infos ctx fn) s.vs_current_bb
                   bb.bb_instructions s.vs_inst_idx) \/
              MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode
                [DALLOCA; RETPC_PARAM]`
    >- (mp_tac (Q.INST [`i` |-> `t.vs_inst_idx`, `idx` |-> `s.vs_inst_idx`,
                        `lbl` |-> `s.vs_current_bb`] fmp_stage_inserted_at) >>
        impl_tac
        >- (qspecl_then [`fmp_stage_plan infos ctx fn`,
                         `fmp_stage_root infos ctx fn`, `s.vs_current_bb`,
                         `bb.bb_instructions`, `s.vs_inst_idx`] assume_tac
              (Q.GENL [`plan`, `root`, `lbl`, `insts`, `idx`] fmp_cov_tidx_lt) >>
            rw[] >> gvs[]) >>
        strip_tac >> irule fmp_cov_quiet >> gvs[get_instruction_def]) >>
    Cases_on `in_revert_forward fn s`
    >- (`?p j. revert_forward_pair bb p j /\
               (s.vs_inst_idx = p \/ s.vs_inst_idx = j)` by
          (gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
        `~((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
          metis_tac[fmp_cov_forward_no_plan] >>
        drule_all fmp_stage_forward_lift >> strip_tac >>
        simp[lowered_mem_ok_def, in_revert_forward_def, revert_forward_at_def] >>
        gvs[] >> metis_tac[]) >>
    Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE`
    >- (drule_all fmp_stage_invoke_inst >> strip_tac >>
        irule fmp_cov_quiet >> gvs[get_instruction_def]) >>
    `pre_fmp_opcode (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
      fs[pre_fmp_ops_def, EVERY_MEM] >>
    mp_tac (Q.INST [`inst` |-> `EL s.vs_inst_idx bb.bb_instructions`,
                    `idx` |-> `s.vs_inst_idx`, `lbl` |-> `s.vs_current_bb`]
              fmp_stage_kept_inst) >>
    impl_tac >- gvs[] >>
    strip_tac >> gvs[get_instruction_def] >>
    Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI`
    >- (irule fmp_cov_quiet >> gvs[]) >>
    simp[lowered_mem_ok_def] >> disj2_tac >>
    mp_tac (Q.GEN `restored`
              (Q.INST [`fmp0` |-> `w2n vs'.vs_initial_fmp`, `raw0` |-> `w2n fmp`,
                       `inst` |-> `EL s.vs_inst_idx bb.bb_instructions`]
                 fmp_stage_kept_mem)) >>
    disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    impl_tac >- gvs[] >>
    simp[])
QED

Theorem fmp_cov_mem:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t ==>
  lowered_mem_fact eom C' fn' ti t
Proof
  rw[fmp_cov_def, lowered_mem_fact_def]
  >- (Cases_on `t.vs_inst_idx = t1.vs_inst_idx`
      >- (`t1 = t` by
            (qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `0` mp_tac) >>
             simp[] >> strip_tac >> drule fmp_target_run_zero >> simp[]) >>
          qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
          drule_all fmp_cov_point_mem >> simp[]) >>
      drule_all fmp_cov_target_labels >> strip_tac >>
      `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
            get_instruction bt t.vs_inst_idx = SOME ti` by
        metis_tac[active_inst_block_lookup] >>
      qpat_x_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
      simp[] >> strip_tac >>
      irule fmp_cov_quiet >> gvs[get_instruction_def]) >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  gvs[] >> irule fmp_cov_tail_mem >> metis_tac[]
QED
