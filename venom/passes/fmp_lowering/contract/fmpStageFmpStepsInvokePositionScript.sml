(*
 * Where FmpLowering puts a source instruction it rewrites in place: the
 * root sits past the entry's parameter prefix, and a source INVOKE sits
 * in the target block at the control map's index, as itself in a function
 * the lowering leaves alone and as its one-instruction lowering otherwise.
 *
 * TOP-LEVEL:
 *   fmp_stage_root_exists - a function that needs the FMP gets a root
 *   fmp_stage_past_root   - a non-parameter instruction is past the root
 *   fmp_lower_invoke_inst - INVOKE's lowering: the call with FMP extras
 *   fmp_walk_invoke_head  - INVOKE's lowering in an indexed walk
 *   fmp_stage_invoke_at   - a source INVOKE's place in the target
 *   fmp_frame_invoke_position - a related frame's target INVOKE
 *)
Theory fmpStageFmpStepsInvokePosition
Ancestors
  fmpStageControl fmpStageControlWalk fmpStageRel fmpLowerDefs
  fmpLowerIndexedProps fmpWfDefs fmpStepLayout callLayoutDefs venomInst
  finite_map list rich_list arithmetic

Theorem fmp_root_retpc[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc rest) /\
  ~fn_is_context_entry ctx fn ==> retpc <> NONE
Proof
  simp[fmp_stage_lowered_def, fmp_stage_root_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `FLOOKUP infos fn.fn_name` >> gvs[] >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _` mp_tac >>
  simp[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[fmp_make_root_layout_def, AllCaseEqs()]
QED

Theorem fmp_root_prefix_bound[local]:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix /\
  idx < LENGTH (prefix ++ rest) /\
  ~MEM (EL idx (prefix ++ rest)).inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM] ==>
  LENGTH prefix <= idx
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `idx < LENGTH prefix` by decide_tac >>
  fs[EVERY_EL, EL_APPEND1] >>
  first_x_assum (qspec_then `idx` mp_tac) >> simp[]
QED

(* Why: lowering a function that needs the FMP splits its entry, so the
   function has a root. *)
Theorem fmp_stage_root_exists:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  info.fi_needs_fmp ==>
  ?rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp)
Proof
  strip_tac >>
  `IS_SOME (split_fmp_entry fn)` by
    gvs[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
        fmp_lower_input_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
  Cases_on `split_fmp_entry fn` >> gvs[] >> Cases_on `x` >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  simp[fmp_stage_root_def] >> Cases_on `fn_is_context_entry ctx fn` >> simp[]
QED

(* Why: the root goes right after the entry's parameter prefix, so every
   other instruction of the entry block is at or past it. *)
Theorem fmp_stage_past_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  ~MEM (EL idx bb.bb_instructions).inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM] ==>
  rp <= idx
Proof
  rpt strip_tac >>
  qpat_assum `fmp_stage_root _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_stage_root_def, AllCaseEqs()]) >>
  gvs[] >> drule split_fmp_entry_reconstruct >> strip_tac >>
  `LENGTH (users ++ OPTION_TO_LIST retpc) <= idx` by
    (irule fmp_root_prefix_bound >> reverse conj_tac
     >- (drule split_fmp_entry_parameter_prefix >>
         Cases_on `retpc` >> simp[OPTION_TO_LIST_def]) >>
     qexists `rest` >> Cases_on `retpc` >>
     gvs[lookup_block_def, FIND_thm, OPTION_TO_LIST_def]) >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
  drule_all fmp_root_retpc >> strip_tac >>
  Cases_on `retpc` >> gvs[OPTION_TO_LIST_def]
QED

Theorem fmp_lower_invoke_inst:
  inst.inst_opcode = INVOKE /\
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') ==>
  ?callee info args.
    fmp_resolve_invoke infos ctx inst = SOME (callee,info,args) /\
    code = [inst with <| inst_operands := Label callee.fn_name ::
          (args ++ if info.fi_needs_fmp then [Var runner] else []);
       inst_outputs := inst.inst_outputs ++
          if info.fi_publishes_fmp then [runner] else [] |>]
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_walk_invoke_head:
  fmp_lower_indexed infos ctx runner lbl k s rs (inst::xs) = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  inst.inst_opcode = INVOKE ==>
  (if (lbl,k) IN FDOM plan then 1 else 0) < LENGTH out /\
  ?sp sp'. fmp_lower_inst infos ctx runner sp inst =
    SOME ([EL (if (lbl,k) IN FDOM plan then 1 else 0) out],sp')
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  drule_all fmp_lower_invoke_inst >> strip_tac >> gvs[] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST1_TAC o GSYM) >>
  simp[EL_APPEND_EQN] >> qexistsl [`s0`, `s1`] >> gvs[]
QED

(* Why: the call and return steps both read the target's INVOKE at the
   control map's index: the source's own INVOKE where the lowering leaves
   the function alone, its lowering otherwise. *)
Theorem fmp_stage_invoke_at:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    ((fmp_stage_root infos ctx fn = NONE /\
      EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
            (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
          (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
        bb'.bb_instructions = EL idx bb.bb_instructions) \/
     ?sp sp'. fmp_lower_inst infos ctx runner sp (EL idx bb.bb_instructions) =
       SOME ([EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
                    (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
                  (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
                bb'.bb_instructions],sp'))
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  gvs[] >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (pop_assum (fn th => map_every assume_tac (CONJUNCTS th)) >>
      `~MEM (EL idx bb.bb_instructions).inst_opcode
         [PARAM; RETPC_PARAM; FMP_PARAM]` by gvs[] >>
      `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
         bb.bb_label = rl ==> rp <= idx` by
        metis_tac[fmp_stage_past_root] >>
      `idx <= LENGTH bb.bb_instructions` by decide_tac >>
      drule_all fmp_stage_tidx_code >> strip_tac >>
      `DROP idx bb.bb_instructions =
        EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
        simp[DROP_CONS_EL] >>
      qpat_x_assum `DROP idx bb.bb_instructions = _` SUBST_ALL_TAC >>
      drule_all fmp_walk_invoke_head >> strip_tac >>
      qexists_tac `bb'` >> simp[] >>
      qpat_x_assum `DROP _ bb'.bb_instructions = code` (SUBST_ALL_TAC o GSYM) >>
      qmatch_asmsub_abbrev_tac `offset < LENGTH (DROP pos bb'.bb_instructions)` >>
      `offset + pos < LENGTH bb'.bb_instructions` by fs[LENGTH_DROP] >>
      fs[EL_DROP] >> metis_tac[ADD_COMM]) >>
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
  `SUM (GENLIST (\j. (if (bb.bb_label,j) IN FDOM (FEMPTY:fmp_reclaim_plan)
      then 1 else 0) +
    (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx) = idx` by
    (irule fmp_control_width_one >> simp[]) >>
  gvs[]
QED

Theorem fmp_stage_invoke_lowered_at[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_stage_invoke_at >> strip_tac >>
  qexists `bb'` >> simp[] >>
  imp_res_tac fmp_lower_invoke_inst >> gvs[]
QED

(* Why: a frame related at a source INVOKE sits at the target's INVOKE
   with the same id, whichever witness of the lowering relates them. *)
Theorem fmp_frame_invoke_position:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE ==>
  ?j. active_inst fn' j t /\ MEM j (fn_insts fn') /\
      j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[contextCodegenRelTheory.active_inst_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  gvs[fmp_frame_rel_def] >>
  drule_all fmp_stage_invoke_lowered_at >> strip_tac >>
  qexists `j` >> simp[] >>
  `MEM bb' fn'.fn_blocks /\ bb'.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> conj_tac
     >- (irule FIND_MEM >> goal_assum (drule_at Any)) >>
     qpat_assum `FIND _ fn'.fn_blocks = SOME bb'`
       (mp_then Any mp_tac FIND_P) >> simp[]) >>
  conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >>
      qexists `bb'` >>
      qpat_x_assum `_ + _ < LENGTH bb'.bb_instructions` mp_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >> strip_tac >>
      qpat_x_assum `EL (_ + _) bb'.bb_instructions = j` mp_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >> strip_tac >> simp[]) >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  qexists `bb'` >> simp[] >> metis_tac[EL_MEM]
QED
