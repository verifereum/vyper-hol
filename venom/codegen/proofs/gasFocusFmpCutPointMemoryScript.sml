(* Memory at an aligned, actually fetched FmpLowering instruction. *)
Theory gasFocusFmpCutPointMemory
Ancestors
  gasFocusFmpCutKeptRanges gasFocusFmpCutForwardLayout fmpStageCoverInv
  fmpStageCoverMem fmpStageCoverMemAssemble fmpCoverInvokeIndex fmpStageControl
  fmpStageRel lowerDloadPtrRawReachable o1PassContract ptrDiscipline contextCodegenRel
  unitMemInv codegenRel venomExecSemantics venomInst venomWf finite_map list

Theorem cut_point_quiet[local]:
  fmp_inserted_op ti.inst_opcode \/ MEM ti.inst_opcode [INVOKE; PHI] ==>
  lowered_mem_fact eom C4 fn' ti t
Proof
  rw[fmp_inserted_op_def, lowered_mem_fact_def, lowered_mem_ok_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem cut_point_forward[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_fn_row 3 fn /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fn.fn_fmp_signature = NONE /\ fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
    (if restored /\ (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
     then 1 else 0) /\ in_revert_forward fn s ==>
  in_revert_forward fn' t
Proof
  strip_tac >>
  `?p j. revert_forward_pair bb p j /\ (s.vs_inst_idx = p \/ s.vs_inst_idx = j)` by
    (gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all focus_fmp_cut_forward_layout >> simp[] >> strip_tac >>
  `p <= j` by (fs[revert_forward_pair_def] >> decide_tac) >>
  `s.vs_inst_idx - p <= j-p /\ (s.vs_inst_idx-p) + p = s.vs_inst_idx` by decide_tac >>
  qpat_x_assum `!h. h <= j-p ==> _` (qspec_then `s.vs_inst_idx-p` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[in_revert_forward_def, revert_forward_at_def, arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem focus_fmp_cut_point_memory:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) (o1_walk_view rpolicy 3) C C4 /\
  o1_ctx_shape C /\ o1_ctx_shape C4 /\ o1_fn_row 3 fn /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
  active_inst fn inst s /\ active_inst fn' ti t /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  wf_function fn /\ make_ssa_input_ok fn /\ pre_fmp_ops fn /\
  fn.fn_fmp_signature = NONE /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn inst s /\ access_ok eom G fn inst s /\
  (!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)) ==>
  lowered_mem_fact eom C4 fn' ti t
Proof
  strip_tac >>
  `o1_fn_shape C fn /\ o1_fn_shape C4 fn'` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `ALL_DISTINCT (fn_labels fn) /\ ALL_DISTINCT (fn_labels fn')` by
    fs[o1_fn_shape_def, wf_function_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by metis_tac[active_inst_block_lookup] >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  Cases_on `in_revert_forward fn s`
  >- (drule_all cut_point_forward >> simp[lowered_mem_fact_def, lowered_mem_ok_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ inst = EL s.vs_inst_idx bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  qabbrev_tac `q = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx` >>
  qabbrev_tac `d:num = if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
                   then 1 else 0` >>
  Cases_on `t.vs_inst_idx <> q+d \/ MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
  >- (irule cut_point_quiet >> disj1_tac >>
      `?b. lookup_block s.vs_current_bb fn'.fn_blocks = SOME b /\
           t.vs_inst_idx < LENGTH b.bb_instructions /\
           fmp_inserted_op (EL t.vs_inst_idx b.bb_instructions).inst_opcode` by
        (irule fmp_cover_inserted_from_root_structural >>
         qpat_assum `fmp_stage_lowered _ _ _ _ _` (irule_at Any) >>
         qpat_assum `lookup_block _ fn.fn_blocks = SOME bb` (irule_at Any) >>
         qexists_tac `s.vs_inst_idx` >>
         `q + d < fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
           s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx)` by
           simp[Abbr `q`, Abbr `d`, fmp_cov_tidx_lt] >>
         Cases_on `restored` >>
         Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)` >>
         gvs[fmp_inserted_op_def, Abbr `d`, Abbr `q`] >> rw[] >> gvs[]) >>
      gvs[get_instruction_def]) >>
  `pre_fmp_opcode inst.inst_opcode` by
    (fs[pre_fmp_ops_def, EVERY_MEM] >>
     metis_tac[lowerDloadOracleCallAssemblyTheory.ld_active_inst_member]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by gvs[] >>
      drule_all fmp_stage_invoke_inst >> strip_tac >>
      irule cut_point_quiet >> gvs[get_instruction_def, Abbr `q`, Abbr `d`]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by gvs[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  `ti = inst` by gvs[get_instruction_def, Abbr `q`, Abbr `d`] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (irule cut_point_quiet >> gvs[]) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= eom \/ w2n t.vs_initial_fmp <= off)
     (inst_mem_ranges inst t)` by
    (irule focus_fmp_cut_kept_ranges >>
     qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_use_static_ok _ _ _` (irule_at Any) >>
     qpat_assum `o1_fn_shape C fn` (irule_at Any) >>
     gvs[pre_fmp_opcode_def]) >>
  gvs[lowered_mem_fact_def, lowered_mem_ok_def]
QED
