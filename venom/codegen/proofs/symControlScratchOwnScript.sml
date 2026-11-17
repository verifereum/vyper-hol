(* Scratch-cell schedules, shared by canonical and relocated own-code runs.
   The control join supplies run correspondence and shallow preparation. *)
Theory symControlScratchOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel symControlPrefixOwn
  asmSplice asmSymSem asmSymPc asmSem frameRel contextCodegenRel
  stackPlanGen stackPlanTypes planExec symPlannerSim symShuffleSim
  spillPlanSim reorderStages inputMaterialised reduceDepthSim mixedPrefixSim
  symControlRestoreScheduleOwn

val scratch_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", scratch_bridge_core_tm);

Theorem mem_label_at_from_bytes:
  (!i. i < 32 ==> FLOOKUP labs (off+i) = SOME (l,d,i)) ==>
  mem_label_at labs off = SOME (l,d)
Proof
  strip_tac >> first_assum (qspec_then `0` assume_tac) >>
  gvs[mem_label_at_def, listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem sym_mstore_word_cell:
  ss.sym_stack = Val off :: Val w :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Val w) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       sval_val_def, asm_op_mem_reads_def, asm_op_mem_writes_def,
       mem_labels_hit_def, sym_lift_def, asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_arith_def,
       asmSemTheory.asm_step_compare_def, asmSemTheory.asm_step_bitwise_def,
       asmSemTheory.asm_step_memory_def,
       asm_op_arity_table_def, log_table_def,
       asm_mstore_def, mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, asm_next_def,
       finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_mstore_label_cell:
  ss.sym_stack = Val off :: Lab l d :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Lab l d) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  qspecl_then [`ss.sym_mem_labels`, `w2n off`, `l`, `d`] assume_tac
    (Q.GENL [`labs`, `off`, `l`, `d`] (SPEC_ALL mem_sval_at_store_label)) >>
  qspecl_then [`w2n off`, `ss.sym_mem_labels`, `l`, `d`] mp_tac
    (Q.GENL [`off`, `labs`, `l`, `d`, `i`] (SPEC_ALL store_label_lookup_outside)) >>
  strip_tac >> gvs[sym_mstore_def, sym_lift_def, asm_mstore_def, asm_next_def]
QED

Theorem sym_mload_label_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Lab l d :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[mem_sval_at_def] >> strip_tac >> simp[sym_mload_def]
QED

Theorem scratch_store_preserves_disjoint_cell:
  mem_sval_at labs cell sv /\
  (!b. in_mem_range cell 32 b ==> ~in_mem_range off 32 b) /\
  (!b. ~in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  mem_sval_at labs' cell sv
Proof
  metis_tac[mem_sval_at_cong]
QED

Theorem sym_mload_word_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) /\
  asm_mload (ss.sym_base with as_stack := [off]) = AsmOK loaded /\
  loaded.as_stack = [w] ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val w :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `FLOOKUP ss.sym_mem_labels (w2n off) = NONE` by
    (gvs[mem_sval_at_def] >> simp[finite_mapTheory.FLOOKUP_DEF] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[sym_mload_def, mem_label_at_def, sym_step_concrete_def,
       asm_op_arity_def, asm_op_arity_table_def, sval_val_def,
       asm_op_mem_reads_def, mem_labels_hit_def,
       asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_arith_def,
       asmSemTheory.asm_step_compare_def, asmSemTheory.asm_step_bitwise_def,
       asmSemTheory.asm_step_memory_def, sym_lift_def] >>
  `~?i. i IN FDOM ss.sym_mem_labels /\ in_mem_range (w2n off) 32 i` by
    metis_tac[mem_sval_at_def] >>
  simp[asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.IN_UNIV, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem sym_scratch_store_step:
  ss.sym_stack = Val off :: sv :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range (w2n off) 32 b)
Proof
  strip_tac >>
  `?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) sv /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)` by
    (Cases_on `sv` >- metis_tac[sym_mstore_word_cell] >>
     metis_tac[sym_mstore_label_cell]) >>
  qexists_tac `ss'` >> simp[] >> conj_tac
  >- (irule sym_step_pc_next >>
      qexistsl_tac [`env`, `AsmOp "MSTORE"`, `p`] >>
      simp[sym_step_def, sym_step_op_def]) >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem sym_scratch_spill_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  strip_tac >>
  qabbrev_tac `pushed = ss with
    <|sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack|>` >>
  `pushed.sym_stack = Val (n2w off) :: sv :: tail` by simp[Abbr `pushed`] >>
  drule sym_scratch_store_step >> strip_tac >> qexists_tac `ss'` >>
  gvs[execute_plan_def, exec_stack_op_def, Abbr `pushed`, asm_next_def,
      wordsTheory.w2n_n2w] >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_scratch_push, asm_next_def] >>
  gvs[sym_step_def, sym_step_op_def]
QED

Theorem sym_scratch_load_word_step:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) ==>
  ?ss' v. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val v :: tail /\
          ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `?loaded v. asm_mload (ss.sym_base with as_stack := [off]) = AsmOK loaded /\
              loaded.as_stack = [v]` by simp[asm_mload_def, asm_next_def] >>
  `mem_sval_at ss.sym_mem_labels (w2n off) (Val v)` by gvs[mem_sval_at_def] >>
  drule_all sym_mload_word_cell >> metis_tac[]
QED

Theorem sym_scratch_load_step:
  ss.sym_stack = Val off :: tail /\ mem_sval_at ss.sym_mem_labels (w2n off) sv ==>
  ?ss' sv'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = sv' :: tail /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >>
  `?ss' sv'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = sv' :: tail /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels` by
    (Cases_on `sv`
     >- (simp[] >> metis_tac[sym_scratch_load_word_step]) >>
     simp[] >> metis_tac[sym_mload_label_cell]) >>
  qexistsl_tac [`ss'`, `sv'`] >> simp[] >>
  irule sym_step_pc_next >> qexistsl_tac [`env`, `AsmOp "MLOAD"`, `p`] >>
  simp[sym_step_def, sym_step_op_def]
QED

Theorem sym_scratch_restore_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv ==>
  ?ss' sv'. sym_steps p env (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    ss'.sym_stack = sv' :: ss.sym_stack /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  strip_tac >>
  qabbrev_tac `pushed = ss with
    <|sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack|>` >>
  `pushed.sym_stack = Val (n2w off) :: ss.sym_stack /\
   mem_sval_at pushed.sym_mem_labels (w2n (n2w off : bytes32)) sv` by
    simp[Abbr `pushed`, wordsTheory.w2n_n2w] >>
  drule_all sym_scratch_load_step >> strip_tac >>
  qexistsl_tac [`ss'`, `sv'`] >>
  gvs[execute_plan_def, exec_stack_op_def, Abbr `pushed`, asm_next_def] >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_scratch_push, asm_next_def] >>
  gvs[sym_step_def, sym_step_op_def]
QED

Theorem sym_scratch_repeated_value_probe:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill 0; SOSpill 32]) /\
  ss.sym_stack = sv :: sv :: tail ==>
  ?ss'. sym_steps p env 4 ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels 0 sv /\ mem_sval_at ss'.sym_mem_labels 32 sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 4
Proof
  strip_tac >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill 0]) /\
   asm_block_at p (ss.sym_base.as_pc + 2) (execute_plan fmp [SOSpill 32])` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  `0 < dimword(:256) /\ 32 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan fmp [SOSpill 32])` by simp[] >>
  `ss'.sym_stack = sv :: tail` by simp[] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `mem_sval_at ss''.sym_mem_labels 0 sv` by
    (irule scratch_store_preserves_disjoint_cell >>
     qexistsl_tac [`ss'.sym_mem_labels`, `32`] >> simp[in_mem_range_def]) >>
  qexists_tac `ss''` >> gvs[execute_plan_def, exec_stack_op_def] >>
  mp_tac (Q.SPECL [`2`, `2`, `ss`] sym_steps_add) >> simp[]
QED

Theorem scratch_disjoint_bulk_cell:
  EVERY (\off. h + 32 <= off \/ off + 32 <= h) offsets /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP labs' b = FLOOKUP labs b) /\
  mem_sval_at labs h sv ==>
  mem_sval_at labs' h sv
Proof
  strip_tac >>
  `!b. in_mem_range h 32 b ==> FLOOKUP labs' b = FLOOKUP labs b`
    suffices_by metis_tac[mem_sval_at_cong] >> rpt strip_tac >>
  first_x_assum irule >>
  fs[listTheory.EVERY_MEM, in_mem_range_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem sym_scratch_spill_bulk_steps:
  !offsets ss.
    LENGTH offsets <= LENGTH ss.sym_stack /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
    asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill offsets)) ==>
    ?ss'. sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
      ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH offsets /\
      (!k. k < LENGTH offsets ==>
        mem_sval_at ss'.sym_mem_labels (EL k offsets) (EL k ss.sym_stack)) /\
      (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==>
        b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  Induct >> simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >>
  rpt strip_tac >>
  `(!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
   EVERY (\off. h + 32 <= off \/ off + 32 <= h) offsets` by
    (conj_tac
     >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
     simp[listTheory.EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  Cases_on `ss.sym_stack` >> gvs[] >> rename1 `ss.sym_stack = sv :: tail` >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill h]) /\
   asm_block_at p (ss.sym_base.as_pc + 2) (execute_plan fmp (MAP SOSpill offsets))` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  first_x_assum (qspec_then `ss'` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `ss''` >> simp[] >> conj_tac
  >- (gvs[execute_plan_def, exec_stack_op_def] >>
      mp_tac (Q.SPECL [`2`, `2 * LENGTH (offsets:num list)`, `ss`] sym_steps_add) >>
      simp[arithmeticTheory.MULT_SUC]) >> conj_tac
  >- (Cases >> simp[] >> metis_tac[scratch_disjoint_bulk_cell]) >> metis_tac[]
QED

Theorem sym_scratch_spill_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SOSpill off])) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    cs'.as_memory = mem_write32 off (HD cs.as_stack) cs.as_memory /\
    cs'.as_stack = TL cs.as_stack /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    cs'.as_pc = cs.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill off])` by simp[] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  `1 <= LENGTH cs.as_stack` by gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p cs.as_pc [AsmPush (encode_num_bytes off); AsmOp "MSTORE"]` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  drule_at (Pos last) spillSimTheory.spill_asm_steps >> simp[] >>
  disch_then (qspecl_then [`lo`, `build_offset_to_pc p`] strip_assume_tac) >>
  gvs[execute_plan_def, exec_stack_op_def] >> metis_tac[asm_result_11]
QED

Theorem sym_scratch_restore_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv /\
  (case sv of Val w =>
     word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP off (asm_expand_memory (off + 32) cs.as_memory))) = w
   | Lab l d => T) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SORestore off])) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ ss'.sym_stack = sv :: ss.sym_stack /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ cs'.as_pc = cs.as_pc + 2 /\
    cs'.as_memory = asm_expand_memory (off + 32) cs.as_memory
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SORestore off])` by simp[] >>
  drule_all sym_scratch_restore_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  `asm_block_at p cs.as_pc [AsmPush (encode_num_bytes off); AsmOp "MLOAD"]` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  drule_all spillSimTheory.restore_asm_steps >>
  disch_then (qspecl_then [`lo`, `build_offset_to_pc p`] strip_assume_tac) >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  Cases_on `sv` >> gvs[asmSymBridgeTheory.sval_conc_def] >> metis_tac[]
QED

Theorem sym_scratch_restore_bulk_sim_mode_conditional:
  !offsets vals cs ss.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
    asm_static_wf p /\ bridge_core lo code_ok cs ss /\
    EVERY (\off. off < dimword(:256)) offsets /\
    LIST_REL (\off sv. mem_sval_at ss.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs.as_memory)) = w | Lab l d => T) offsets vals /\
    asm_block_at p cs.as_pc (execute_plan fmp (MAP SORestore offsets)) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p (2 * LENGTH offsets) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (2 * LENGTH offsets) ss = SymOK ss' /\
      bridge_core lo code_ok cs' ss' /\
      ss'.sym_stack = REVERSE vals ++ ss.sym_stack /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\
      cs'.as_pc = cs.as_pc + 2 * LENGTH offsets
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  match_mp_tac (BETA_RULE (Q.INST [`R` |-> `bridge_core lo code_ok`]
    sym_restore_bulk_from_cell)) >>
  rpt gen_tac >> disch_tac >>
  irule (BETA_RULE sym_scratch_restore_sim_mode_conditional) >> asm_rewrite_tac[]
QED

Theorem sym_scratch_spill_bulk_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (MAP SOSpill offsets)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p (2 * LENGTH offsets) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (2 * LENGTH offsets) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets /\
    LIST_REL (\off sv. mem_sval_at ss'.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs'.as_memory)) = w | Lab l d => T)
      offsets (TAKE (LENGTH offsets) ss.sym_stack) /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (MAP SOSpill offsets))` by simp[] >>
  drule_all sym_scratch_spill_bulk_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  `LENGTH offsets <= LENGTH cs.as_stack` by
    (imp_res_tac listTheory.LIST_REL_LENGTH >> gvs[]) >>
  drule_all doSwapSimTheory.raw_spill_bulk_steps >>
  disch_then (qspecl_then [`lo`, `build_offset_to_pc p`] mp_tac) >>
  strip_tac >> qexistsl_tac [`cs'`, `ss'`] >>
  gvs[] >>
  conj_tac >- (conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]) >>
  simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >> simp[listTheory.EL_TAKE] >>
  `word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (EL n offsets)
      (FOLDL (\mem p. mem_write32 (FST p) (SND p) mem) cs.as_memory
        (ZIP (offsets, TAKE (LENGTH offsets) cs.as_stack))))) = EL n cs.as_stack` by
    (mp_tac (Q.SPECL [`offsets:num list`, `TAKE (LENGTH (offsets:num list)) cs.as_stack`,
       `cs.as_memory`, `n`] doSwapSimTheory.raw_spill_fold_read_occurrence) >>
     simp[listTheory.EL_TAKE]) >>
  Cases_on `EL n ss.sym_stack` >> simp[] >>
  fs[listTheory.LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < LENGTH ss.sym_stack ==> _`
    (qspec_then `n` mp_tac) >> simp[asmSymBridgeTheory.sval_conc_def]
QED

val scratch_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", scratch_bridge_core_tm);

Theorem sym_raw_spill_restore_schedule_steps_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\i. i < LENGTH offsets) desired /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP SORestore
      (MAP (\i. EL i offsets) (REVERSE desired)))) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\
    ss'.sym_stack = MAP (\i. EL i (TAKE (LENGTH offsets) ss.sym_stack)) desired ++
      DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets + 2 * LENGTH desired /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (MAP SOSpill offsets)) /\
   asm_block_at p (cs.as_pc + 2 * LENGTH offsets) (execute_plan initial_fmp
     (MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))` by
    gvs[stackOpSimTheory.asm_block_at_append, stackOpSimTheory.execute_plan_append,
        doSwapSimTheory.execute_plan_map_spill_length] >>
  drule_all (BETA_RULE sym_scratch_spill_bulk_sim_mode_conditional) >>
  disch_then (qx_choose_then `cs'` (qx_choose_then `ss'` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `EVERY (\off. off < dimword(:256)) (MAP (\i. EL i offsets) (REVERSE desired)) /\
   LIST_REL (\off sv. mem_sval_at ss'.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs'.as_memory)) = w | Lab l d => T)
     (MAP (\i. EL i offsets) (REVERSE desired))
     (MAP (\i. EL i (TAKE (LENGTH offsets) ss.sym_stack)) (REVERSE desired))` by
    (fs[listTheory.EVERY_EL, listTheory.LIST_REL_EL_EQN] >>
     simp[listTheory.EVERY_MAP, rich_listTheory.EVERY_REVERSE,
          listTheory.EVERY_EL, listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP] >>
     simp[listTheory.EL_REVERSE, listTheory.LENGTH_REVERSE]) >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp
     (MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))` by gvs[] >>
  drule_all (BETA_RULE sym_scratch_restore_bulk_sim_mode_conditional) >> strip_tac >>
  qexistsl_tac [`cs''`, `ss''`] >>
  simp[stackOpSimTheory.execute_plan_append,
       doSwapSimTheory.execute_plan_map_spill_length,
       doSwapSimTheory.execute_plan_map_restore_length] >>
  conj_tac >- (qpat_assum `asm_steps _ _ _ _ cs = AsmOK cs'`
    (mp_then (Pos hd) mp_tac blockSimHelpersTheory.asm_steps_compose_ok) >>
    disch_then drule >> simp[]) >>
  mp_tac (Q.SPECL [`2 * LENGTH (offsets:num list)`,
    `2 * LENGTH (desired:num list)`, `ss`] sym_steps_mode_add) >>
  gvs[listTheory.MAP_REVERSE] >> strip_tac >>
  conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]
QED

Theorem list_rel_reversed_index_schedule:
  LIST_REL R (REVERSE items) vals /\ LENGTH items = d + 1 /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < LENGTH items) ids ==>
  LIST_REL R (REVERSE (MAP (\i. EL i items) ids))
    (MAP (\i. EL i vals) ids)
Proof
  strip_tac >>
  `REVERSE (MAP (\i. EL i items) ids) =
     MAP (\i. EL i (REVERSE items)) ids` by
    (qpat_x_assum `ids = _` SUBST1_TAC >>
     irule doSwapSimTheory.reverse_desired_values >> simp[]) >>
  qpat_x_assum `REVERSE (MAP _ _) = _`
    (fn th => pure_rewrite_tac[th]) >>
  irule LIST_REL_select_indices >> gvs[]
QED

Theorem do_swap_deep_symbolic_resources:
  do_swap d ps = (ops,ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] ==>
  ops = MAP SOSpill offsets ++
    MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids)) /\
  LENGTH offsets = d + 1 /\ ALL_DISTINCT offsets /\
  EVERY (\i. i < LENGTH offsets) ids /\
  EVERY (\off. off < dimword(:256) /\ ps'.ps_alloc.sa_spill_base <= off /\
    off + 32 <= ps'.ps_alloc.sa_next_offset) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  (!i op old. i < LENGTH offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= EL i offsets \/ EL i offsets + 32 <= old) /\
  ps'.ps_spilled = ps.ps_spilled /\
  ps'.ps_stack = TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack ++
    MAP (\i. EL i (top_n (d + 1) ps.ps_stack)) ids
Proof
  strip_tac >>
  `LENGTH (top_n (d + 1) ps.ps_stack) = d + 1` by
    simp[stackPlanOpsTheory.top_n_def, listTheory.LENGTH_TAKE] >>
  `ops = MAP SOSpill offsets ++
     MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids)) /\
   ps' = ps with <|
     ps_stack := TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack ++
       MAP (\i. EL i (top_n (d + 1) ps.ps_stack)) ids;
     ps_alloc := FOLDL (\a off. free_spill_slot off a)
       (SND (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))) offsets |>` by
    (mp_tac (Q.SPECL [`d`, `ps`] doSwapSimTheory.do_swap_big_decompose) >>
     simp[LET_THM] >> metis_tac[]) >>
  `ps'.ps_alloc = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))) offsets` by simp[] >>
  drule_all doSwapSimTheory.spill_alloc_n_temporary_layout >> strip_tac >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    (qpat_x_assum `EVERY _ ops` mp_tac >> simp[listTheory.EVERY_MAP]) >>
  `EVERY (\i. i < LENGTH offsets) ids` by
    simp[listTheory.EVERY_GENLIST] >>
  simp[] >> conj_tac >- gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem list_rel_deep_swap_schedule:
  LIST_REL R (REVERSE xs) vals /\ d < LENGTH xs /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < d + 1) ids ==>
  LIST_REL R
    (REVERSE (TAKE (LENGTH xs - (d + 1)) xs ++
      MAP (\i. EL i (top_n (d + 1) xs)) ids))
    (MAP (\i. EL i (TAKE (d + 1) vals)) ids ++ DROP (d + 1) vals)
Proof
  strip_tac >> pure_rewrite_tac[listTheory.REVERSE_APPEND] >>
  irule rich_listTheory.EVERY2_APPEND_suff >> conj_tac
  >- (irule list_rel_reversed_index_schedule >>
      simp[stackPlanOpsTheory.top_n_def, listTheory.LENGTH_TAKE] >>
      gvs[rich_listTheory.EVERY2_TAKE]) >>
  `REVERSE (TAKE (LENGTH xs - (d + 1)) xs) = DROP (d + 1) (REVERSE xs)` by
    simp[rich_listTheory.DROP_REVERSE, rich_listTheory.BUTLASTN_TAKE_UNCOND] >>
  simp[] >> metis_tac[rich_listTheory.EVERY2_DROP]
QED

Theorem sym_scratch_frame_transfer_mode_conditional:
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  bridge_core lo code_ok cs' ss' /\ ps'.ps_spilled = ps.ps_spilled /\
  ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  EVERY (\off. r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) offsets /\
  (!off op old. MEM off offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= off \/ off + 32 <= old) /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. b IN FDOM ss'.sym_mem_labels ==>
    b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets) ==>
  bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps' ss' /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `!b off. MEM off offsets /\ in_mem_range off 32 b ==>
    r.sr_spill_base <= b /\ b < r.sr_spill_end` by
    (fs[listTheory.EVERY_MEM, in_mem_range_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[] >> conj_tac
  >- metis_tac[] >>
  conj_tac
  >- (simp[sym_kinds_ok_def] >> conj_tac
      >- (rpt strip_tac >>
          `?sv. op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels off sv` by
            metis_tac[sym_kinds_ok_def] >>
          qexists_tac `sv` >> simp[] >> irule scratch_disjoint_bulk_cell >>
          goal_assum (drule_at Any) >> qexists_tac `offsets` >>
          simp[] >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
      fs[sym_kinds_ok_def, listTheory.EXISTS_MEM] >>
      metis_tac[contextCodegenRelPropsTheory.context_spill_byte_of_region]) >>
  `!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  metis_tac[sym_frame_region_labels_transfer]
QED

Theorem sym_do_swap_deep_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  do_swap d ps = (ops, ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps' ss' /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))` >>
  qabbrev_tac `ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]` >>
  `offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) /\
   ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]` by
    simp[Abbr `offsets`, Abbr `ids`] >>
  drule_all do_swap_deep_symbolic_resources >> strip_tac >>
  qpat_x_assum `offsets = FST _` kall_tac >>
  `?top. ss.sym_stack = top ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top` by
    metis_tac[sym_kinds_ok_def] >> pop_assum strip_assume_tac >>
  `LENGTH top = LENGTH ps.ps_stack` by
    metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_REVERSE] >>
  `LENGTH offsets <= LENGTH ss.sym_stack /\
   EVERY (\off. off < dimword(:256)) offsets /\
   asm_block_at p cs.as_pc (execute_plan initial_fmp
     (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids))))` by
    (conj_tac >- (qpat_x_assum `ss.sym_stack = _` (fn th => pure_rewrite_tac[th]) >>
       simp[NoAsms, listTheory.LENGTH_APPEND] >> decide_tac) >>
     conj_tac >- (qpat_x_assum `EVERY (\off. off < dimword(:256) /\ _) offsets` mp_tac >>
       simp[NoAsms, listTheory.EVERY_MEM] >> metis_tac[]) >> metis_tac[]) >>
  drule_all (BETA_RULE sym_raw_spill_restore_schedule_steps_mode_conditional) >>
  disch_then (qx_choose_then `cs'` (qx_choose_then `ss'` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack)
    (MAP (\i. EL i (TAKE (d + 1) top)) ids ++ DROP (d + 1) top)` by
    (qpat_x_assum `ps'.ps_stack = _` (fn th => pure_rewrite_tac[th]) >>
     irule list_rel_deep_swap_schedule >>
     `0 < d` by decide_tac >> metis_tac[]) >>
  `LENGTH (execute_plan initial_fmp ops) = 2 * LENGTH offsets + 2 * LENGTH ids` by
    (qpat_assum `ops = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, stackOpSimTheory.execute_plan_append,
       doSwapSimTheory.execute_plan_map_spill_length,
       doSwapSimTheory.execute_plan_map_restore_length]) >>
  `ss'.sym_stack =
    (MAP (\i. EL i (TAKE (d + 1) top)) ids ++ DROP (d + 1) top) ++ srest` by
    (`d + 1 <= LENGTH top` by decide_tac >>
     `TAKE (d + 1) ss.sym_stack = TAKE (d + 1) top /\
      DROP (d + 1) ss.sym_stack = DROP (d + 1) top ++ srest` by
       metis_tac[listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1] >>
     metis_tac[listTheory.APPEND_ASSOC]) >>
  `EVERY (\off. r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) offsets /\
   (!off op old. MEM off offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
     old + 32 <= off \/ off + 32 <= old)` by
    (conj_tac >- (qpat_assum `EVERY (\off. off < dimword(:256) /\ _) offsets` mp_tac >>
       simp[NoAsms, listTheory.EVERY_MEM] >>
       metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[listTheory.MEM_EL]) >>
  drule_all (BETA_RULE sym_scratch_frame_transfer_mode_conditional) >>
  disch_then assume_tac >>
  qexistsl_tac [`cs'`, `ss'`] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  `cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)` by decide_tac >>
  metis_tac[]
QED

(* The shallow branch is supplied by the control preparation producer. *)

Theorem sym_do_swap_frame_sim_mode_conditional:
  (!d ps ops ps' initial_fmp cs ss r.
    do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps' ss' /\
      (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
      (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  do_swap d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps' ss' /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  Cases_on `d <= 16`
  >- (qpat_x_assum `!d ps ops ps' initial_fmp cs ss r. _`
        (drule_all_then mp_tac) >> simp[]) >>
  `16 < d` by decide_tac >>
  drule_all (BETA_RULE sym_do_swap_deep_frame_sim_mode_conditional) >> simp[]
QED

Theorem sym_do_swap_pair_frame_sim_mode_conditional:
  (!d ps ops ps' initial_fmp cs ss r.
    do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps' ss' /\
      (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
      (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (ops1 ++ ops2) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
  ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ sym_kinds_ok cplan fn ret srest ps2 ss' /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity_layout] >>
  `f < LENGTH ps1.ps_stack` by metis_tac[planWfTheory.do_swap_length, pairTheory.SND] >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
   ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    metis_tac[allocMonoTheory.do_swap_spill_base,
      allocMonoTheory.do_swap_next_offset, arithmeticTheory.LESS_EQ_TRANS] >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp ops1) /\
   asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp ops1))
     (execute_plan initial_fmp ops2)` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  qpat_x_assum `EVERY _ (ops1 ++ ops2)` mp_tac >>
  rewrite_tac[listTheory.EVERY_APPEND] >> strip_tac >>
  drule_all (BETA_RULE sym_do_swap_frame_sim_mode_conditional) >>
  disch_then (qx_choose_then `cs'` (qx_choose_then `ss'` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp ops2)` by metis_tac[] >>
  qpat_x_assum `do_swap d ps = (ops1,ps1)` kall_tac >>
  drule_all (BETA_RULE sym_do_swap_frame_sim_mode_conditional) >>
  disch_then (qx_choose_then `cs''` (qx_choose_then `ss''` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`cs''`, `ss''`] >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  conj_tac >- (qpat_assum `asm_steps _ _ _ _ cs = AsmOK cs'`
    (mp_then (Pos hd) mp_tac blockSimHelpersTheory.asm_steps_compose_ok) >>
    disch_then drule >> simp[]) >>
  conj_tac >- (mp_tac (Q.SPECL [`LENGTH (execute_plan initial_fmp ops1)`,
    `LENGTH (execute_plan initial_fmp ops2)`, `ss`] sym_steps_mode_add) >> simp[]) >>
  `cs''.as_pc = cs.as_pc +
    (LENGTH (execute_plan initial_fmp ops1) + LENGTH (execute_plan initial_fmp ops2))` by decide_tac >>
  simp[] >> metis_tac[]
QED
