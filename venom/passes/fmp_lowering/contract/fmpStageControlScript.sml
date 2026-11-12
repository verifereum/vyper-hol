(*
 * The control side of FmpLowering's stage simulation: where a source
 * instruction sits in the lowered block, how the control map moves over
 * one instruction.
 *
 * TOP-LEVEL:
 *   fmp_stage_tidx_code    - the lowered code from a source index on
 *   fmp_stage_unlowered    - an unrewritten function keeps its blocks
 *   fmp_stage_tidx_suc     - the control map over one kept instruction
 *   fmp_stage_plan_point   - a planned restore sits at a reclaim point
 *   fmp_stage_kept_inst    - a kept instruction's place in the target
 *   fmp_stage_root_crossing - the source step reaching the root
 *)
Theory fmpStageControl
Ancestors
  fmpStageRel o1PassContract fmpLowerDefs fmpReclaimDefs fmpWfDefs venomInst
  finite_map list rich_list

(* Why: the step proofs read the target's code at the control map's index
   off the lowering's own walk; a point's restores come first, then its
   expansion. *)
Theorem fmp_stage_tidx_code:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx <= LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb' restores sp code leftover sp'.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    (!j b. MEM ((bb.bb_label,j),b) restores <=>
           idx <= j /\
           FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,j) = SOME b) /\
    fmp_lower_indexed infos ctx runner bb.bb_label idx sp restores
      (DROP idx bb.bb_instructions) = SOME (code,leftover,sp') /\
    DROP (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
            (fmp_stage_root infos ctx fn) bb.bb_label
            bb.bb_instructions idx)
         bb'.bb_instructions = code
Proof
  cheat
QED

(* Why: the other branches of the lowering keep the blocks (a sealed
   function, or one that neither takes nor publishes the FMP, whose plan
   must be empty); there the control map is the identity. *)
Theorem fmp_stage_unlowered:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
           (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  fn'.fn_blocks = fn.fn_blocks /\
  fmp_stage_plan infos ctx fn = FEMPTY /\ fmp_stage_root infos ctx fn = NONE
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs(), fmp_stage_plan_def,
      fmp_stage_root_def, analyze_fmp_reclaims_def, fmp_checked_seal_def,
      fmp_seal_def] >>
  gvs[]
QED

(* Why: past a point with no restore and a one-instruction expansion, the
   next point is one further on, unless the root comes in between. *)
Theorem fmp_stage_tidx_suc:
  ~((lbl,idx) IN FDOM plan) /\ (EL idx insts).inst_opcode <> DALLOCA /\
  (!rl rp. root = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC idx) ==>
  fmp_stage_tidx plan root lbl insts (SUC idx) =
    SUC (fmp_stage_tidx plan root lbl insts idx)
Proof
  strip_tac >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  Cases_on `root` >> simp[] >> rename1 `SOME x` >> PairCases_on `x` >>
  simp[] >> rw[] >> fs[]
QED

(* Why: a restore is planned only where fmp_reclaim_step pops, and it pops
   only at a reclaim point. *)
Theorem fmp_stage_plan_point:
  (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  idx < LENGTH bb.bb_instructions /\
  fmp_is_reclaim_point infos (EL idx bb.bb_instructions)
Proof
  simp[fmp_stage_plan_def] >> CASE_TAC >> simp[] >> strip_tac >>
  rename1 `analyze_fmp_reclaims infos ctx fn = SOME plan` >>
  `fmp_reclaim_entry_ok infos ctx fn (lbl,idx) (plan ' (lbl,idx))` by
    gvs[analyze_fmp_reclaims_def, AllCaseEqs(), fmp_reclaim_plan_ok_def,
        FLOOKUP_DEF] >>
  pop_assum mp_tac >> simp[fmp_reclaim_entry_ok_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >> strip_tac >>
  spose_not_then assume_tac >>
  gvs[fmp_reclaim_step_def, fmp_pop_at_def, fmp_pop_target_def]
QED

(* Why: an instruction the lowering keeps as itself (every opcode but
   DALLOCA, INVOKE and RETPC_PARAM, which it rewrites, and the raw FMP
   ones, which row 3 has none of) sits in the target block at the control
   map's index, past its point's restore if it has one.  Before the root
   the target's prefix is the source's user parameters. *)
Theorem fmp_stage_kept_inst:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ inst = EL idx bb.bb_instructions /\
  ~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM] /\
  pre_fmp_opcode inst.inst_opcode ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
        (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
       bb'.bb_instructions = inst
Proof
  cheat
QED

(* Why: the root counts from rp on, so the source step that reaches rp
   runs it too.  Outside the context entry that step is RETPC_PARAM (the
   lowering puts the root right before it); in a context entry with no
   parameters there is no such step. *)
Theorem fmp_stage_root_crossing:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  SUC idx = rp /\ idx < LENGTH bb.bb_instructions /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  (EL idx bb.bb_instructions).inst_opcode = RETPC_PARAM
Proof
  cheat
QED
