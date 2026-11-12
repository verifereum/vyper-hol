(*
 * FmpLowering keeps make_ssa_input_ok.
 *
 * Lowering keeps labels, CFG edges and every PHI where it was.  Within a
 * block it replaces each instruction by a short run whose new variables
 * come from the supply and are defined before their uses in that run, and
 * inserts two kinds of instruction that read variables:
 *   - restores (runner := base) before a planned point, whose base the
 *     reclaim analysis proves written on every path to that point
 *     (analyze_fmp_reclaims_target_defined);
 *   - uses of the fresh runner, which the root instruction defines in the
 *     entry block, ahead of every body instruction there.
 * Every other use is an original use at a corresponding position, and
 * every original output survives, so original definitions still reach
 * their uses.  Distinct instruction ids pin a use to one position of its
 * block, which def_on_all_paths needs.
 *
 * TOP-LEVEL:
 *   fmp_lower_function_make_ssa_input_ok
 *)
Theory fmpStepMakeSsa
Ancestors
  fmpStepReclaimDefined fmpStepRetpcShape fmpStepShape fmpStepLayout
  fmpStepRewrite fmpLowerIndexedProps fmpLowerProps fmpLowerDefs
  fmpAnalysisProps fmpAnalysisDefs o1PassContract cfgWf venomWf venomInst
  irSupply venomFnScheduleRunner dretDesugarProofs cfgNormSupplyProofs list
  rich_list arithmetic

(* ===== One instruction ===== *)

Theorem fmp_lower_inst_use_position[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  m < LENGTH out /\ (EL m out).inst_opcode <> PHI /\
  MEM (Var v) (EL m out).inst_operands ==>
  (inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands) \/
  v = runner \/
  ?m'. m' < m /\ MEM v (EL m' out).inst_outputs
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      `m = 0 \/ m = 1 \/ m = 2 \/ m = 3` by decide_tac >>
      gvs[mk_inst_def] >> rpt disj2_tac >>
      FIRST [qexists `0` >> simp[] >> NO_TAC,
             qexists `1` >> simp[] >> NO_TAC,
             qexists `2` >> simp[] >> NO_TAC]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
  TRY (`m = 0` by decide_tac) >> gvs[MEM_APPEND] >>
  TRY (drule fmp_resolve_invoke_some >> strip_tac >> gvs[MEM_APPEND] >>
       qpat_x_assum `MEM _ (if _ then _ else _)` mp_tac >> rw[] >> NO_TAC) >>
  TRY (drule fmp_resolve_invoke_some >> strip_tac >> gvs[MEM_APPEND] >>
       NO_TAC) >>
  Cases_on `inst.inst_operands` >> gvs[MEM_LAST] >>
  drule MEM_FRONT >> simp[]
QED

Theorem fmp_lower_inst_output_kept[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM w inst.inst_outputs ==>
  ?j. MEM j out /\ MEM w j.inst_outputs
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
          mk_inst_def] >>
      simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
  simp[MEM_APPEND]
QED

Theorem fmp_lower_inst_output_count[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM v s.irs_used_vars /\ v <> runner ==>
  LENGTH (FILTER (\i. MEM v i.inst_outputs) out) <=
  LENGTH (FILTER (\i. MEM v i.inst_outputs) [inst])
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (drule (cj 1 fresh_ir_var_contract) >> strip_tac >>
           dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[mk_inst_def] >> rw[] >> gvs[]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
  rw[] >> gvs[MEM_APPEND]
QED

(* ===== Restores ===== *)

Theorem fmp_emit_restores_outputs[local]:
  fmp_emit_restores runner s bases = (out,s') /\ MEM j out ==>
  j.inst_outputs = [runner] /\
  ?base. MEM base bases /\ j.inst_operands = [Var base] /\
         j.inst_opcode = ASSIGN
Proof
  strip_tac >> drule_all fmp_emit_restores_assign_origin >> strip_tac >>
  gvs[mk_inst_def] >> metis_tac[]
QED

(* ===== One block ===== *)

(* Each use in a lowered block is an original use at a corresponding
   source position j, a planned restore at j, the runner, or a value
   written earlier in the lowered block; whatever the source writes
   before j, the lowered block writes before the use. *)
Theorem fmp_lower_indexed_use_position[local]:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  !j' v. j' < LENGTH out /\ (EL j' out).inst_opcode <> PHI /\
    MEM (Var v) (EL j' out).inst_operands ==>
    ?j. j < LENGTH insts /\
      (!i w. i < j /\ MEM w (EL i insts).inst_outputs ==>
         ?i'. i' < j' /\ MEM w (EL i' out).inst_outputs) /\
      (((EL j insts).inst_opcode <> PHI /\
        MEM (Var v) (EL j insts).inst_operands) \/
       MEM ((label,k + j),v) restores \/ v = runner \/
       ?i'. i' < j' /\ MEM v (EL i' out).inst_outputs)
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule fmp_select_point_restores_once >> strip_tac >>
  Cases_on `j' < LENGTH prefix`
  >- (`MEM (EL j' prefix) prefix` by simp[EL_MEM] >>
      drule_all fmp_emit_restores_outputs >> strip_tac >>
      gvs[EL_APPEND_EQN] >> qexists `0` >> simp[]) >>
  Cases_on `j' < LENGTH prefix + LENGTH head`
  >- (`EL j' (prefix ++ head ++ tail) = EL (j' - LENGTH prefix) head` by
        simp[EL_APPEND_EQN] >>
      qabbrev_tac `m = j' - LENGTH prefix` >>
      `m < LENGTH head` by simp[Abbr `m`] >>
      `(EL m head).inst_opcode <> PHI /\
       MEM (Var v) (EL m head).inst_operands` by metis_tac[] >>
      drule_all fmp_lower_inst_use_position >> strip_tac >>
      qexists `0` >> simp[] >>
      disj2_tac >> disj2_tac >> disj2_tac >>
      qexists `LENGTH prefix + m'` >> simp[EL_APPEND_EQN, Abbr `m`]) >>
  `EL j' (prefix ++ head ++ tail) =
   EL (j' - (LENGTH prefix + LENGTH head)) tail` by simp[EL_APPEND_EQN] >>
  `j' - (LENGTH prefix + LENGTH head) < LENGTH tail` by gvs[] >>
  gvs[] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`j' - (LENGTH prefix + LENGTH head)`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  (qexists `SUC j` >> simp[] >> TRY conj_tac
  >- (Cases >> simp[] >> rpt strip_tac
      >- (drule_all fmp_lower_inst_output_kept >> strip_tac >>
          qpat_x_assum `MEM _ head`
            (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
          rename1 `nn < LENGTH head` >>
          qexists `LENGTH prefix + nn` >> gvs[EL_APPEND_EQN]) >>
      qpat_x_assum `!i w. i < j /\ MEM w _ ==> _` drule_all >>
      disch_then (qx_choose_then `ii` strip_assume_tac) >>
      qexists `ii + (LENGTH prefix + LENGTH head)` >> simp[EL_APPEND_EQN]) >>
  gvs[ADD_CLAUSES] >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexists `i' + (LENGTH prefix + LENGTH head)` >> simp[EL_APPEND_EQN])
QED

Theorem fmp_lower_indexed_output_kept[local]:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  !i w. MEM i insts /\ MEM w i.inst_outputs ==>
    ?i'. MEM i' out /\ MEM w i'.inst_outputs
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[MEM_APPEND]
  >- (drule_all fmp_lower_inst_output_kept >> metis_tac[]) >>
  first_x_assum drule >> disch_then drule_all >> metis_tac[]
QED

Theorem fmp_lower_indexed_output_count[local]:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ ir_supply_inst_ok s /\
  MEM v s.irs_used_vars /\ v <> runner ==>
  LENGTH (FILTER (\i. MEM v i.inst_outputs) out) <=
  LENGTH (FILTER (\i. MEM v i.inst_outputs) insts)
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[FILTER_APPEND] >>
  drule_all fmp_emit_restores_supply >> strip_tac >>
  drule_all fmp_lower_inst_supply >> strip_tac >>
  `MEM v s0.irs_used_vars /\ MEM v s1.irs_used_vars` by
    gvs[dret_supply_extends_def] >>
  `FILTER (\i. MEM v i.inst_outputs) prefix = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     drule_all fmp_emit_restores_outputs >> strip_tac >> gvs[]) >>
  drule_all fmp_lower_inst_output_count >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `MEM v h.inst_outputs` >> gvs[]
QED

(* ===== All blocks ===== *)

Theorem fmp_lower_blocks_correspond[local]:
  !bbs s restores out leftover s'.
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    (!i w. MEM i bb.bb_instructions /\ MEM w i.inst_outputs ==>
       ?i'. MEM i' bb'.bb_instructions /\ MEM w i'.inst_outputs) /\
    (!j' v. j' < LENGTH bb'.bb_instructions /\
       (EL j' bb'.bb_instructions).inst_opcode <> PHI /\
       MEM (Var v) (EL j' bb'.bb_instructions).inst_operands ==>
       ?j. j < LENGTH bb.bb_instructions /\
         (!i w. i < j /\ MEM w (EL i bb.bb_instructions).inst_outputs ==>
            ?i'. i' < j' /\ MEM w (EL i' bb'.bb_instructions).inst_outputs) /\
         (((EL j bb.bb_instructions).inst_opcode <> PHI /\
           MEM (Var v) (EL j bb.bb_instructions).inst_operands) \/
          MEM ((bb.bb_label,j),v) restores \/ v = runner \/
          ?i'. i' < j' /\ MEM v (EL i' bb'.bb_instructions).inst_outputs)))
    bbs out
Proof
  Induct >- simp[fmp_lower_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (drule fmp_lower_indexed_output_kept >> simp[])
  >- (drule fmp_lower_indexed_use_position >> simp[]) >>
  drule fmp_lower_indexed_leftover >> strip_tac >>
  first_x_assum drule >> match_mp_tac LIST_REL_mono >>
  rpt gen_tac >> simp[] >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists `j` >> gvs[] >> metis_tac[]
QED

Theorem fmp_lower_blocks_output_count[local]:
  !bbs s restores out leftover s'.
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\ ir_supply_inst_ok s /\
  MEM v s.irs_used_vars /\ v <> runner ==>
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts_blocks out)) <=
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts_blocks bbs))
Proof
  Induct >- simp[fmp_lower_blocks_def, fn_insts_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[fn_insts_blocks_def, FILTER_APPEND] >>
  drule_all fmp_lower_indexed_output_count >> strip_tac >>
  drule_all fmp_lower_indexed_supply >> strip_tac >>
  first_x_assum drule >> impl_tac >- gvs[dret_supply_extends_def] >>
  simp[]
QED

(* ===== The entry block ===== *)

(* Installing the root keeps the parameter prefix, replaces the optional
   RETPC parameter by one with the same outputs, and inserts the root,
   which writes the runner, before the body; so a runner use in the body
   becomes a use of a value written earlier in the block. *)
Theorem fmp_root_block_correspond[local]:
  !P bi ei fi users pc sfx tail xs r runner.
  bi = users ++ pc ++ sfx /\ ei = users ++ pc ++ tail /\
  fi = users ++ xs ++ tail /\
  LENGTH pc <= 1 /\ LENGTH xs = LENGTH pc + 1 /\
  MEM r xs /\ r.inst_outputs = [runner] /\
  (!i w. MEM i pc /\ MEM w i.inst_outputs ==>
     ?i'. MEM i' xs /\ MEM w i'.inst_outputs) /\
  (!m v. m < LENGTH xs /\ (EL m xs).inst_opcode <> PHI /\
     MEM (Var v) (EL m xs).inst_operands ==>
     m < LENGTH pc /\ EL m xs = EL m pc) /\
  (!i w. MEM i bi /\ MEM w i.inst_outputs ==>
     ?i'. MEM i' ei /\ MEM w i'.inst_outputs) /\
  (!j' v. j' < LENGTH ei /\ (EL j' ei).inst_opcode <> PHI /\
     MEM (Var v) (EL j' ei).inst_operands ==>
     ?j. j < LENGTH bi /\
       (!i w. i < j /\ MEM w (EL i bi).inst_outputs ==>
          ?i'. i' < j' /\ MEM w (EL i' ei).inst_outputs) /\
       (((EL j bi).inst_opcode <> PHI /\ MEM (Var v) (EL j bi).inst_operands) \/
        P j v \/ v = runner \/
        ?i'. i' < j' /\ MEM v (EL i' ei).inst_outputs)) ==>
  (!i w. MEM i bi /\ MEM w i.inst_outputs ==>
     ?i'. MEM i' fi /\ MEM w i'.inst_outputs) /\
  (!j' v. j' < LENGTH fi /\ (EL j' fi).inst_opcode <> PHI /\
     MEM (Var v) (EL j' fi).inst_operands ==>
     ?j. j < LENGTH bi /\
       (!i w. i < j /\ MEM w (EL i bi).inst_outputs ==>
          ?i'. i' < j' /\ MEM w (EL i' fi).inst_outputs) /\
       (((EL j bi).inst_opcode <> PHI /\ MEM (Var v) (EL j bi).inst_operands) \/
        P j v \/
        ?i'. i' < j' /\ MEM v (EL i' fi).inst_outputs))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i w. MEM i bi /\ _ ==> _` drule_all >> strip_tac >>
      gvs[MEM_APPEND] >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `j' < LENGTH users`
  >- (qexists `j'` >> gvs[EL_APPEND_EQN] >> rpt strip_tac >>
      qexists `i` >> gvs[EL_APPEND_EQN]) >>
  Cases_on `j' < LENGTH users + LENGTH xs`
  >- (`(EL (j' - LENGTH users) xs).inst_opcode <> PHI /\
       MEM (Var v) (EL (j' - LENGTH users) xs).inst_operands` by
        gvs[EL_APPEND_EQN] >>
      `j' - LENGTH users < LENGTH xs` by decide_tac >>
      qpat_x_assum `!m v. m < LENGTH xs /\ _ ==> _` drule_all >>
      strip_tac >>
      `j' = LENGTH users /\ LENGTH pc = 1` by decide_tac >>
      qexists `j'` >> gvs[EL_APPEND_EQN] >> rpt strip_tac >>
      qexists `i` >> gvs[EL_APPEND_EQN]) >>
  `j' - 1 < LENGTH ei /\ EL j' fi = EL (j' - 1) ei` by
    gvs[EL_APPEND_EQN] >>
  `!i' w. i' < j' - 1 /\ MEM w (EL i' ei).inst_outputs ==>
          ?i''. i'' < j' /\ MEM w (EL i'' fi).inst_outputs` by
    (rpt strip_tac >>
     Cases_on `i' < LENGTH users`
     >- (qexists `i'` >> gvs[EL_APPEND_EQN]) >>
     Cases_on `i' < LENGTH users + LENGTH pc`
     >- (`MEM (EL (i' - LENGTH users) pc) pc` by simp[EL_MEM] >>
         `MEM w (EL (i' - LENGTH users) pc).inst_outputs` by
           gvs[EL_APPEND_EQN] >>
         qpat_x_assum `!i w. MEM i pc /\ _ ==> _` drule_all >>
         disch_then (qx_choose_then `x0` strip_assume_tac) >>
         qpat_x_assum `MEM x0 xs` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
         rename1 `nn < LENGTH xs` >>
         qexists `LENGTH users + nn` >> gvs[EL_APPEND_EQN]) >>
     qexists `i' + 1` >> gvs[EL_APPEND_EQN]) >>
  qpat_x_assum `!j' v. j' < LENGTH ei /\ _ ==> _`
    (qspecl_then [`j' - 1`, `v`] mp_tac) >>
  impl_tac >- gvs[] >>
  disch_then (qx_choose_then `j` (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  qexists `j` >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!i w. i < j /\ _ ==> _` drule_all >> strip_tac >>
      qpat_x_assum `!i' w. i' < j' - 1 /\ _ ==> _` drule_all >>
      metis_tac[]) >>
  qpat_x_assum `_ \/ _ \/ _` strip_assume_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (qpat_x_assum `MEM r xs` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
      rename1 `nn < LENGTH xs` >> disj2_tac >> disj2_tac >>
      qexists `LENGTH users + nn` >> gvs[EL_APPEND_EQN]) >>
  disj2_tac >> disj2_tac >>
  qpat_x_assum `!i' w. i' < j' - 1 /\ _ ==> _` drule_all >> metis_tac[]
QED

(* ===== The rewrite branch ===== *)

(* Without DRET or RETFMP the function does not publish, so the rewrite
   branch is taken because it needs the runner, and installs a root. *)
Theorem fmp_pre_fmp_ops_not_publishing[local]:
  fmp_info_valid ctx infos /\
  lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  pre_fmp_ops fn ==> ~info.fi_publishes_fmp
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  gvs[fmp_info_valid_def] >>
  qpat_x_assum
    `!fn. MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = NONE ==> _`
    (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  drule fmp_join_target_info_publishes_iff >> simp[] >> strip_tac >>
  `!insts. EVERY (\i. pre_fmp_opcode i.inst_opcode) insts ==>
           ~(fmp_scan_insts insts).fi_publishes_fmp` by
    (Induct >>
     simp[fmp_scan_insts_def, fmp_info_bottom_def, fmp_info_join_def,
          fmp_opcode_publishes_fmp_def, pre_fmp_opcode_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[fmp_direct_info_def, pre_fmp_ops_def]
QED

Theorem fmp_make_root_layout_root[local]:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root newpc s') /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc sfx) /\
  info.fi_needs_fmp ==>
  ?r. root = SOME r /\ r.inst_outputs = [runner] /\
      (!v. ~MEM (Var v) r.inst_operands) /\
      (fn_is_context_entry ctx fn ==> newpc = oldpc) /\
      (~fn_is_context_entry ctx fn ==>
         !i v. MEM i (OPTION_TO_LIST newpc) ==> ~MEM (Var v) i.inst_operands)
Proof
  rw[fmp_make_root_layout_def] >>
  gvs[AllCaseEqs(), mk_inst_def, set_param_index_def,
      callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

(* What installing the root puts between the parameters and the body. *)
Theorem fmp_root_insert_facts[local]:
  !b oldpc newpc r xs runner.
  (newpc = NONE <=> oldpc = NONE) /\
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST newpc) =
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST oldpc) /\
  r.inst_outputs = [runner] /\ (!v. ~MEM (Var v) r.inst_operands) /\
  (b ==> newpc = oldpc) /\
  (~b ==> !i v. MEM i (OPTION_TO_LIST newpc) ==>
            ~MEM (Var v) i.inst_operands) /\
  xs = (if b then OPTION_TO_LIST oldpc ++ [r]
        else [r] ++ OPTION_TO_LIST newpc) ==>
  LENGTH (OPTION_TO_LIST oldpc) <= 1 /\
  LENGTH xs = LENGTH (OPTION_TO_LIST oldpc) + 1 /\ MEM r xs /\
  (!i w. MEM i (OPTION_TO_LIST oldpc) /\ MEM w i.inst_outputs ==>
     ?i'. MEM i' xs /\ MEM w i'.inst_outputs) /\
  (!m v. m < LENGTH xs /\ (EL m xs).inst_opcode <> PHI /\
     MEM (Var v) (EL m xs).inst_operands ==>
     m < LENGTH (OPTION_TO_LIST oldpc) /\
     EL m xs = EL m (OPTION_TO_LIST oldpc)) /\
  (!v. v <> runner ==>
     LENGTH (FILTER (\i. MEM v i.inst_outputs) xs) <=
     LENGTH (FILTER (\i. MEM v i.inst_outputs) (OPTION_TO_LIST oldpc)))
Proof
  rpt gen_tac >> Cases_on `b` >> Cases_on `newpc` >> Cases_on `oldpc` >>
  rw[callLayoutDefsTheory.OPTION_TO_LIST_def] >> gvs[] >>
  TRY (Cases_on `m` >> gvs[] >> TRY (Cases_on `n` >> gvs[]) >> NO_TAC) >>
  rw[] >> gvs[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem fmp_plan_alist_flookup[local]:
  MEM ((l,j),v) (fmp_plan_to_alist fn plan) ==> FLOOKUP plan (l,j) = SOME v
Proof
  simp[MEM_fmp_plan_to_alist]
QED

Theorem fmp_lower_function_correspond[local]:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  pre_fmp_ops fn /\ ir_supply_inst_ok s ==>
  (?x. fn' = fn with fn_fmp_signature := x) \/
  ?infos plan runner.
    analyze_fmp_reclaims infos ctx fn = SOME plan /\
    ~MEM runner s.irs_used_vars /\
    LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
      (!i w. MEM i bb.bb_instructions /\ MEM w i.inst_outputs ==>
         ?i'. MEM i' bb'.bb_instructions /\ MEM w i'.inst_outputs) /\
      (!j' v. j' < LENGTH bb'.bb_instructions /\
         (EL j' bb'.bb_instructions).inst_opcode <> PHI /\
         MEM (Var v) (EL j' bb'.bb_instructions).inst_operands ==>
         ?j. j < LENGTH bb.bb_instructions /\
           (!i w. i < j /\ MEM w (EL i bb.bb_instructions).inst_outputs ==>
              ?i'. i' < j' /\ MEM w (EL i' bb'.bb_instructions).inst_outputs) /\
           (((EL j bb.bb_instructions).inst_opcode <> PHI /\
             MEM (Var v) (EL j bb.bb_instructions).inst_operands) \/
            FLOOKUP plan (bb.bb_label,j) = SOME v \/
            (v = runner /\ fn_entry_label fn <> SOME bb.bb_label) \/
            ?i'. i' < j' /\ MEM v (EL i' bb'.bb_instructions).inst_outputs)))
      fn.fn_blocks fn'.fn_blocks /\
    fn'.fn_blocks <> [] /\
    (?i. MEM i (HD fn'.fn_blocks).bb_instructions /\
         MEM runner i.inst_outputs) /\
    !v. MEM v s.irs_used_vars ==>
      LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn')) <=
      LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn))
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >~ [`fn.fn_fmp_signature = SOME sig`]
  >- (disj1_tac >> qexists `SOME sig` >>
      simp[ir_function_component_equality]) >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def]
  >- (disj1_tac >> simp[ir_function_component_equality]) >>
  `~info.fi_publishes_fmp` by
    (irule fmp_pre_fmp_ops_not_publishing >> gvs[fmp_lower_input_def] >>
     metis_tac[]) >>
  gvs[] >> disj2_tac >>
  Cases_on `root_layout` >> gvs[] >>
  rename1 `fmp_make_root_layout ctx fn info runner s1 =
             SOME (FmpRootLayout n root newpc s2)` >>
  rename1 `fmp_lower_blocks _ _ _ s2 _ _ =
             SOME (FmpBlocksResult lowered [] s3)` >>
  qexistsl [`infos`, `plan`, `runner`] >> simp[] >>
  `?users oldpc sfx.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc sfx)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >>
  drule_all fmp_make_root_layout_root >> strip_tac >>
  drule_all fmp_make_root_layout_seed_correspondence >> strip_tac >>
  drule fmpStepOpaqueTheory.fmp_make_root_layout_used_vars >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  rename1 `fn.fn_blocks = b0::brest` >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  rename1 `lowered = e0::erest` >>
  rename1 `e0.bb_instructions = _ ++ _ ++ etail` >>
  `option_CASE oldpc [] (\i. [i]) = OPTION_TO_LIST oldpc` by
    (Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[] >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  `~MEM runner s.irs_used_vars /\
   s1.irs_used_vars = runner :: s.irs_used_vars` by
    metis_tac[fresh_ir_var_contract] >>
  `ir_supply_inst_ok s1` by metis_tac[fresh_ir_var_inst_ok] >>
  `ir_supply_inst_ok s2` by metis_tac[fmp_make_root_layout_inst_ok] >>
  `!v. MEM v s.irs_used_vars ==>
     LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts_blocks (e0::erest))) <=
     LENGTH (FILTER (\i. MEM v i.inst_outputs)
               (fn_insts_blocks (b0::brest)))` by
    (rpt strip_tac >> drule_then irule fmp_lower_blocks_output_count >>
     gvs[] >> strip_tac >> gvs[]) >>
  drule fmp_lower_blocks_correspond >>
  qpat_x_assum `fn.fn_blocks = b0::brest`
    (fn th => REWRITE_TAC [th, LIST_REL_def] >> assume_tac th) >>
  BETA_TAC >> strip_tac >>
  `fn_entry_label fn = SOME b0.bb_label` by
    simp[fn_entry_label_def, entry_block_def] >>
  `~MEM b0.bb_label (MAP (\b. b.bb_label) brest)` by
    gvs[o1_fn_shape_def, wf_function_def, fn_labels_def] >>
  qabbrev_tac `xs = if fn_is_context_entry ctx fn
                    then OPTION_TO_LIST oldpc ++ [r]
                    else [r] ++ OPTION_TO_LIST newpc` >>
  `!a. (if fn_is_context_entry ctx fn then
          users ++ OPTION_TO_LIST oldpc ++ OPTION_TO_LIST (SOME r) ++ a
        else users ++ OPTION_TO_LIST (SOME r) ++ OPTION_TO_LIST newpc ++ a) =
       users ++ xs ++ a` by
    rw[Abbr `xs`, callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  qspecl_then [`fn_is_context_entry ctx fn`, `oldpc`, `newpc`, `r`, `xs`,
               `runner`] mp_tac fmp_root_insert_facts >>
  impl_tac >- simp[Abbr `xs`] >> strip_tac >>
  qspecl_then [`\j v. MEM ((b0.bb_label,j),v) (fmp_plan_to_alist fn plan)`,
               `b0.bb_instructions`, `e0.bb_instructions`,
               `users ++ xs ++ etail`,
               `users`, `OPTION_TO_LIST oldpc`, `sfx`, `etail`, `xs`, `r`,
               `runner`] mp_tac fmp_root_block_correspond >>
  BETA_TAC >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!i w. MEM i b0.bb_instructions /\ _ ==> _`
        (qspecl_then [`i`, `w`] mp_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!j' v. j' < LENGTH (users ++ xs ++ etail) /\ _ ==> _`
        drule_all >>
      disch_then (qx_choose_then `j` (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
      qexists `j` >> rpt conj_tac
      >- gvs[]
      >- (rpt strip_tac >>
          qpat_x_assum `!i w. i < j /\ _ ==> _`
            (qspecl_then [`i`, `w`] mp_tac) >> gvs[]) >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >>
      metis_tac[fmp_plan_alist_flookup])
  >- (qpat_x_assum `LIST_REL _ brest erest` mp_tac >>
      simp[LIST_REL_EL_EQN] >> strip_tac >> qx_gen_tac `n` >> strip_tac >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      `(EL n brest).bb_label <> b0.bb_label` by
        (strip_tac >> qpat_x_assum `~MEM b0.bb_label _` mp_tac >>
         simp[MEM_MAP] >> metis_tac[EL_MEM]) >>
      simp[] >> TRY (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!j' v. j' < LENGTH (EL n erest).bb_instructions /\ _ ==> _`
        drule_all >> strip_tac >>
      qexists `j` >> simp[] >>
      metis_tac[fmp_plan_alist_flookup])
  >- (qexists `r` >> simp[])
  >- (rpt strip_tac >>
      `v <> runner` by (strip_tac >> gvs[]) >>
      qpat_x_assum `!v. v <> runner ==> _` drule >> strip_tac >>
      qpat_x_assum `!v. MEM v s.irs_used_vars ==> _` drule >> strip_tac >>
      gvs[fn_insts_def, fn_insts_blocks_def, FILTER_APPEND])
QED

(* ===== Transporting definite assignment ===== *)

Theorem fmp_is_fn_path_cfg_edge[local]:
  fn_cfg_edge g = fn_cfg_edge f ==> !p. is_fn_path g p = is_fn_path f p
Proof
  strip_tac >> Induct >> simp[is_fn_path_def] >>
  gen_tac >> Cases_on `p` >> gvs[is_fn_path_def]
QED

Theorem fmp_source_var_reserved[local]:
  ir_supply_covers_fn s f /\ MEM b f.fn_blocks /\
  MEM i b.bb_instructions /\ MEM v (inst_ir_vars i) ==>
  MEM v s.irs_used_vars
Proof
  simp[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def,
       block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS, EVERY_MEM] >>
  metis_tac[]
QED

(* A definition at the end of a source block is still there at the end of
   its lowered partner, or in the same earlier block of the path. *)
Theorem fmp_def_on_all_paths_end[local]:
  def_on_all_paths f a NONE v /\ b.bb_label = a.bb_label /\
  (!i w. MEM i a.bb_instructions /\ MEM w i.inst_outputs ==>
     ?i'. MEM i' b.bb_instructions /\ MEM w i'.inst_outputs) /\
  (!p. is_fn_path g p = is_fn_path f p) /\
  fn_entry_label g = fn_entry_label f /\
  (!a i w. MEM a f.fn_blocks /\ MEM i a.bb_instructions /\
     MEM w i.inst_outputs ==>
     ?b i'. MEM b g.fn_blocks /\ b.bb_label = a.bb_label /\
            MEM i' b.bb_instructions /\ MEM w i'.inst_outputs) ==>
  def_on_all_paths g b NONE v
Proof
  strip_tac >> simp[def_on_all_paths_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths f a NONE v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> impl_tac >- gvs[] >>
  strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  `MEM (EL i a.bb_instructions) a.bb_instructions` by simp[EL_MEM] >>
  qpat_x_assum `!i w. MEM i a.bb_instructions /\ _ ==> _` drule_all >>
  strip_tac >> gvs[MEM_EL] >> metis_tac[]
QED

(* A definition before a source occurrence is still before its partner. *)
Theorem fmp_def_on_all_paths_use[local]:
  def_on_all_paths f a (SOME (EL j a.bb_instructions)) v /\
  ALL_DISTINCT a.bb_instructions /\ j < LENGTH a.bb_instructions /\
  j' < LENGTH b.bb_instructions /\ b.bb_label = a.bb_label /\
  (!i w. i < j /\ MEM w (EL i a.bb_instructions).inst_outputs ==>
     ?i'. i' < j' /\ MEM w (EL i' b.bb_instructions).inst_outputs) /\
  (!p. is_fn_path g p = is_fn_path f p) /\
  fn_entry_label g = fn_entry_label f /\
  (!a i w. MEM a f.fn_blocks /\ MEM i a.bb_instructions /\
     MEM w i.inst_outputs ==>
     ?b i'. MEM b g.fn_blocks /\ b.bb_label = a.bb_label /\
            MEM i' b.bb_instructions /\ MEM w i'.inst_outputs) ==>
  def_on_all_paths g b (SOME (EL j' b.bb_instructions)) v
Proof
  strip_tac >> simp[def_on_all_paths_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths f a _ v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> impl_tac >- gvs[] >>
  strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  rename1 `EL jj a.bb_instructions = EL j a.bb_instructions` >>
  `jj = j` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  qpat_x_assum `jj = j` SUBST_ALL_TAC >>
  qpat_x_assum `!i w. i < j /\ _ ==> _` drule_all >> strip_tac >>
  qexists `i'` >> simp[] >> qexists `j'` >> simp[]
QED

(* The runner is written in the entry block, which every path from the
   entry to another block leaves first. *)
Theorem fmp_runner_def_on_all_paths[local]:
  g.fn_blocks <> [] /\
  (?i. MEM i (HD g.fn_blocks).bb_instructions /\ MEM v i.inst_outputs) /\
  fn_entry_label g <> SOME b.bb_label ==>
  def_on_all_paths g b use v
Proof
  rw[def_on_all_paths_def] >> disj1_tac >>
  qexistsl [`0`, `HD g.fn_blocks`, `i`] >>
  Cases_on `g.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  Cases_on `path` >> gvs[] >>
  rename1 `LAST (_ :: ys)` >> Cases_on `ys` >> gvs[]
QED

(* ===== The main theorem ===== *)

fun partner_tac bq nm =
  qpat_assum `LIST_REL _ fn.fn_blocks fn'.fn_blocks` (fn lr =>
    qpat_assum bq (fn th =>
      qx_choose_then nm strip_assume_tac
        (BETA_RULE (MATCH_MP LIST_REL_MEM_IMP_R (CONJ lr th)))));

fun source_partner_tac bq nm =
  qpat_assum `LIST_REL _ fn.fn_blocks fn'.fn_blocks` (fn lr =>
    qpat_assum bq (fn th =>
      qx_choose_then nm strip_assume_tac
        (BETA_RULE (MATCH_MP LIST_REL_MEM_IMP (CONJ lr th)))));

Theorem fmp_lower_function_make_ssa_input_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  pre_fmp_ops fn /\ make_ssa_input_ok fn ==> make_ssa_input_ok fn'
Proof
  strip_tac >>
  drule_all fmp_lower_function_correspond >> strip_tac
  >- gvs[] >>
  `fn_cfg_edge fn' = fn_cfg_edge fn` by
    (drule_all fmp_lower_function_cfg_edge >> simp[]) >>
  `!x y. fn_cfg_edge fn' x y <=> fn_cfg_edge fn x y` by simp[] >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (drule fmp_lower_function_preserves_entry_label >> simp[]) >>
  `fn_reachable fn' = fn_reachable fn` by
    (drule_all fmp_lower_function_reachable >> simp[]) >>
  `!p. is_fn_path fn' p = is_fn_path fn p` by
    (irule fmp_is_fn_path_cfg_edge >> first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
   fn_inst_ids_distinct fn` by
    gvs[o1_fn_shape_def, wf_function_def, fn_labels_def] >>
  `!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
         MEM inst a.bb_instructions` by
    (rpt strip_tac >> drule fmp_lower_function_phi_location >>
     disch_then (drule_then (qspec_then `bb.bb_label` mp_tac)) >>
     strip_tac >> metis_tac[]) >>
  `!a i w. MEM a fn.fn_blocks /\ MEM i a.bb_instructions /\
     MEM w i.inst_outputs ==>
     ?b i'. MEM b fn'.fn_blocks /\ b.bb_label = a.bb_label /\
            MEM i' b.bb_instructions /\ MEM w i'.inst_outputs` by
    (rpt strip_tac >> source_partner_tac `MEM a fn.fn_blocks` `b` >>
     metis_tac[]) >>
  qpat_x_assum `make_ssa_input_ok fn`
    (strip_assume_tac o REWRITE_RULE [make_ssa_input_ok_def]) >>
  simp[make_ssa_input_ok_def] >> rpt conj_tac
  >- (simp[all_reachable_def] >> rpt strip_tac >>
      partner_tac `MEM bb fn'.fn_blocks` `a` >>
      qpat_x_assum `all_reachable fn` mp_tac >>
      simp[all_reachable_def] >> metis_tac[])
  >- (simp[fn_defs_reach_uses_def] >> rpt gen_tac >> strip_tac >>
      IF_CASES_TAC
      >- (rpt strip_tac >>
          `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
               MEM inst a.bb_instructions` by metis_tac[] >>
          partner_tac `MEM pred_bb fn'.fn_blocks` `pa` >>
          `def_on_all_paths fn pa NONE v` by
            (qpat_x_assum `fn_defs_reach_uses fn` mp_tac >>
             simp[fn_defs_reach_uses_def] >>
             disch_then (qspecl_then [`a`, `inst`] mp_tac) >> simp[] >>
             disch_then (qspecl_then [`v`, `pa`] mp_tac) >>
             gvs[]) >>
          drule fmp_def_on_all_paths_end >> disch_then irule >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qx_gen_tac `v` >> strip_tac >>
      partner_tac `MEM bb fn'.fn_blocks` `a` >>
      `ALL_DISTINCT a.bb_instructions` by
        metis_tac[venomFnInstsProofsTheory.fn_inst_ids_block_distinct,
                  ALL_DISTINCT_MAP] >>
      qpat_x_assum `MEM inst bb.bb_instructions`
        (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
      rename1 `inst = EL j' bb.bb_instructions` >>
      qpat_x_assum `inst = _` SUBST_ALL_TAC >>
      qpat_x_assum `!j' v. j' < LENGTH bb.bb_instructions /\ _ ==> _`
        (qspecl_then [`j'`, `v`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qx_choose_then `j` (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac strip_assume_tac)))
      >- (`def_on_all_paths fn a (SOME (EL j a.bb_instructions)) v` by
            (qpat_x_assum `fn_defs_reach_uses fn` mp_tac >>
             simp[fn_defs_reach_uses_def] >>
             disch_then (qspecl_then [`a`, `EL j a.bb_instructions`] mp_tac) >>
             simp[EL_MEM]) >>
          drule fmp_def_on_all_paths_use >> disch_then irule >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (drule_all analyze_fmp_reclaims_target_defined >> strip_tac >>
          drule fmp_def_on_all_paths_use >> disch_then irule >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (irule fmp_runner_def_on_all_paths >> rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      simp[def_on_all_paths_def] >> rpt strip_tac >> disj2_tac >>
      rename1 `MEM v (EL ii bb.bb_instructions).inst_outputs` >>
      qexists `ii` >> simp[] >> qexists `j'` >> simp[])
  >- (simp[fn_phi_operands_single_def_def] >> rpt strip_tac >>
      `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
           MEM inst a.bb_instructions` by metis_tac[] >>
      `MEM v (inst_ir_vars inst)` by
        (simp[inst_ir_vars_def, inst_uses_def] >>
         metis_tac[MEM_phi_pairs_SND_operand_vars]) >>
      `MEM v s.irs_used_vars` by metis_tac[fmp_source_var_reserved] >>
      `LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1` by
        (qpat_x_assum `fn_phi_operands_single_def fn` mp_tac >>
         simp[fn_phi_operands_single_def_def] >> metis_tac[]) >>
      qpat_x_assum `!v. MEM v s.irs_used_vars ==> _` drule >> decide_tac)
  >- (simp[fn_phis_cover_preds_def] >> rpt strip_tac >>
      `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
           MEM inst a.bb_instructions` by metis_tac[] >>
      qpat_x_assum `fn_phis_cover_preds fn` mp_tac >>
      simp[fn_phis_cover_preds_def] >> metis_tac[])
  >- (simp[fn_phi_outputs_single_def_def] >> rpt strip_tac >>
      `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
           MEM inst a.bb_instructions` by metis_tac[] >>
      `MEM v (inst_ir_vars inst)` by simp[inst_ir_vars_def] >>
      `MEM v s.irs_used_vars` by metis_tac[fmp_source_var_reserved] >>
      `LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1` by
        (qpat_x_assum `fn_phi_outputs_single_def fn` mp_tac >>
         simp[fn_phi_outputs_single_def_def] >> metis_tac[]) >>
      qpat_x_assum `!v. MEM v s.irs_used_vars ==> _` drule >> decide_tac)
  >- (simp[fn_phis_non_degenerate_def] >> rpt strip_tac >>
      `?bb. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions` by
        (qpat_x_assum `MEM inst (fn_insts fn')` mp_tac >>
         simp[fn_insts_def, fn_insts_blocks_MEM]) >>
      `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
           MEM inst a.bb_instructions` by metis_tac[] >>
      `MEM inst (fn_insts fn)` by
        (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
      qpat_x_assum `fn_phis_non_degenerate fn` mp_tac >>
      simp[fn_phis_non_degenerate_def] >> disch_then drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?a. MEM a fn.fn_blocks /\ a.bb_label = bb.bb_label /\
       MEM inst a.bb_instructions` by metis_tac[] >>
  qpat_x_assum `!bb inst. MEM bb fn.fn_blocks /\ _ ==> ALL_DISTINCT _ /\ _`
    (qspecl_then [`a`, `inst`] mp_tac) >>
  simp[] >> metis_tac[]
QED
