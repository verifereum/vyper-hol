(* Numerical boundary algorithms, independent of the frame relation. *)
Theory symFrameBoundaryNumeric
Ancestors
  codegenSymRel fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary
  asmSymBridge asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst dfgDefs symShuffleSim reorderStages codegenSymOwnRel

Theorem scratch_fold_outside:
  !xs labs b.
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs ==>
    FLOOKUP (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) b = FLOOKUP labs b
Proof
  Induct >> simp[] >>
  Cases_on `h` >> simp[] >>
  metis_tac[scratch_store_labels_outside]
QED

Theorem scratch_fold_preserves_saved:
  !xs labs old saved.
    EVERY (\p. old + 32 <= FST p \/ FST p + 32 <= old) xs ==>
    (mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  Induct >> simp[] >>
  Cases_on `h` >> simp[] >>
  metis_tac[scratch_store_labels_preserves_saved]
QED

Theorem scratch_fold_saved:
  !xs labs.
    ALL_DISTINCT (MAP FST xs) /\
    (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
       FST p + 32 <= FST q \/ FST q + 32 <= FST p) ==>
    !off sv. MEM (off,sv) xs ==>
      mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) off sv
Proof
  Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >> rw[]
  >- (gvs[] >> rename1 `~MEM off (MAP FST xs)` >>
      `EVERY (\p. off + 32 <= FST p \/ FST p + 32 <= off) xs` by
        (simp[listTheory.EVERY_MEM] >>
         metis_tac[listTheory.MEM_MAP, pairTheory.FST]) >>
      metis_tac[scratch_fold_preserves_saved, scratch_store_labels_at]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem sym_kinds_stack_poke:
  !cp fn ret srest ps ss d op.
  sym_kinds_ok cp fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
        op_kind_ok fn ret op sv) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  rw[sym_kinds_ok_def] >> qexists `top` >>
  gvs[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def] >>
  rpt strip_tac >>
  simp[listTheory.EL_REVERSE, listTheory.EL_LUPDATE] >>
  IF_CASES_TAC >> gvs[stackModelTheory.stack_peek_def,
    listTheory.EL_REVERSE] >> metis_tac[]
QED

Theorem sym_mload_mem_sval_label:
  !ss off l d stk.
  ss.sym_stack = Val off :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Lab l d) ==>
  sym_mload ss = SymOK
    (ss with <| sym_base := asm_next (ss.sym_base with
                  as_memory := asm_expand_memory (w2n off + 32)
                    ss.sym_base.as_memory);
                sym_stack := Lab l d :: stk |>)
Proof
  simp[mem_sval_at_def, sym_mload_def]
QED

Theorem sym_steps_two:
  !p env ss i j s1 s2.
    asm_block_at p ss.sym_base.as_pc [i;j] /\
    sym_step p env i ss = SymOK s1 /\
    s1.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    sym_step p env j s1 = SymOK s2 ==>
    sym_steps p env 2 ss = SymOK s2
Proof
  simp[stackOpSimTheory.asm_block_at_cons] >> rpt strip_tac >>
  simp[asmSpliceTheory.sym_steps_compute]
QED

Theorem sym_push_offset_then:
  !p env ss off inst pushed out.
    off < dimword(:256) /\
    asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes off); inst] /\
    pushed = ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack |> /\
    sym_step p env inst pushed = SymOK out ==>
    sym_steps p env 2 ss = SymOK out
Proof
  rpt strip_tac >>
  `pushed.sym_base.as_pc = ss.sym_base.as_pc + 1` by
    gvs[asmSemTheory.asm_next_def] >>
  metis_tac[sym_steps_two, sym_scratch_push]
QED

Theorem sym_pushed_mstore:
  !p env ss off sv stk pushed.
    off < dimword(:256) /\ ss.sym_stack = sv :: stk /\
    pushed = ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack |> ==>
    ?out. sym_step p env (AsmOp "MSTORE") pushed = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = scratch_store_labels ss.sym_mem_labels off sv /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >>
  qspec_then `pushed` mp_tac sym_mstore_scratch_step >>
  gvs[sym_step_def, sym_step_op_def, asmSemTheory.asm_next_def]
QED

Theorem sym_spill_offset_steps:
  !p env ss off sv stk.
    off < dimword(:256) /\ ss.sym_stack = sv :: stk /\
    asm_block_at p ss.sym_base.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ==>
    ?ss'. sym_steps p env 2 ss = SymOK ss' /\
      ss'.sym_stack = stk /\
      ss'.sym_mem_labels = scratch_store_labels ss.sym_mem_labels off sv /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >> metis_tac[sym_pushed_mstore, sym_push_offset_then]
QED

Theorem sym_mload_saved_kinds:
  !ss off sv stk.
    ss.sym_stack = Val off :: stk /\
    mem_sval_at ss.sym_mem_labels (w2n off) sv ==>
    ?out sv'. sym_mload ss = SymOK out /\
      out.sym_stack = sv' :: stk /\
      (!fn ret op. op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') /\
      out.sym_mem_labels = ss.sym_mem_labels /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt gen_tac >> Cases_on `sv` >> strip_tac
  >- (drule_all sym_mload_scratch_word >> strip_tac >> gvs[op_kind_ok_def]) >>
  drule_all sym_mload_mem_sval_label >> disch_then SUBST1_TAC >>
  simp[asmSemTheory.asm_next_def]
QED

Theorem sym_pushed_mload:
  !p env ss off sv pushed.
    off < dimword(:256) /\ mem_sval_at ss.sym_mem_labels off sv /\
    pushed = ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack |> ==>
    ?out sv'. sym_step p env (AsmOp "MLOAD") pushed = SymOK out /\
      out.sym_stack = sv' :: ss.sym_stack /\
      (!fn ret op. op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') /\
      out.sym_mem_labels = ss.sym_mem_labels /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >>
  qspec_then `pushed` mp_tac sym_mload_saved_kinds >>
  gvs[sym_step_def, sym_step_op_def, asmSemTheory.asm_next_def]
QED

Theorem sym_restore_offset_steps:
  !p env ss off sv.
    off < dimword(:256) /\ mem_sval_at ss.sym_mem_labels off sv /\
    asm_block_at p ss.sym_base.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] ==>
    ?out sv'. sym_steps p env 2 ss = SymOK out /\
      out.sym_stack = sv' :: ss.sym_stack /\
      (!fn ret op. op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') /\
      out.sym_mem_labels = ss.sym_mem_labels /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >>
  qspecl_then [`p`, `env`, `ss`, `off`, `sv`] mp_tac sym_pushed_mload >>
  simp[] >> strip_tac >>
  qexistsl_tac [`out`, `sv'`] >> simp[] >>
  qspecl_then [`p`, `env`, `ss`, `off`, `AsmOp "MLOAD"`] mp_tac
    sym_push_offset_then >>
  simp[]
QED

Theorem sym_spill_offsets_cons_result_fold:
  !p env ss mid out off sv xs stk.
    sym_steps p env 2 ss = SymOK mid /\
    mid.sym_mem_labels = scratch_store_labels ss.sym_mem_labels off sv /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    sym_steps p env (2 * LENGTH xs) mid = SymOK out /\
    out.sym_stack = stk /\
    out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) mid.sym_mem_labels xs /\
    out.sym_base.as_pc = mid.sym_base.as_pc + 2 * LENGTH xs ==>
    ?result. sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK result /\
      result.sym_stack = stk /\
      result.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels ((off,sv)::xs) /\
      result.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH ((off,sv)::xs)
Proof
  rpt strip_tac >> drule_all sym_steps_compose >>
  gvs[listTheory.FOLDL, arithmeticTheory.MULT_CLAUSES]
QED

Theorem sym_spill_offsets_cons_step_fold:
  !xs.
    (!p env ss stk initial_fmp.
      EVERY (\p. FST p < dimword(:256)) xs /\
      ss.sym_stack = MAP SND xs ++ stk /\
      asm_block_at p ss.sym_base.as_pc
        (execute_plan initial_fmp (MAP SOSpill (MAP FST xs))) ==>
      ?out. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
        out.sym_stack = stk /\
        out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels xs /\
        out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs) ==>
    !off sv p env ss stk initial_fmp.
    EVERY (\p. FST p < dimword(:256)) ((off,sv)::xs) /\
    ss.sym_stack = MAP SND ((off,sv)::xs) ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SOSpill (MAP FST ((off,sv)::xs)))) ==>
    ?out. sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels ((off,sv)::xs) /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH ((off,sv)::xs)
Proof
  gen_tac >> disch_tac >> rpt gen_tac >>
  pure_rewrite_tac[listTheory.EVERY_DEF, listTheory.MAP,
       pairTheory.FST, pairTheory.SND, listTheory.LENGTH,
       execute_plan_def, listTheory.FLAT, exec_stack_op_def,
       stackOpSimTheory.asm_block_at_append] >>
  pure_rewrite_tac[GSYM execute_plan_def] >> simp[] >> rpt strip_tac >>
  drule_all sym_spill_offset_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  rename1 `sym_steps p env 2 ss = SymOK mid` >>
  `asm_block_at p mid.sym_base.as_pc
    (execute_plan initial_fmp (MAP SOSpill (MAP FST xs)))` by simp[] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  `out.sym_base.as_pc = mid.sym_base.as_pc + 2 * LENGTH xs` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all sym_spill_offsets_cons_result_fold >> simp[]
QED

Theorem sym_spill_offsets_steps_fold:
  !xs p env ss stk initial_fmp.
    EVERY (\p. FST p < dimword(:256)) xs /\
    ss.sym_stack = MAP SND xs ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SOSpill (MAP FST xs))) ==>
    ?out. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels xs /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs
Proof
  Induct >- simp[asmSpliceTheory.sym_steps_def] >>
  Cases >> drule sym_spill_offsets_cons_step_fold >> metis_tac[]
QED

Theorem sym_restore_offsets_cons_result:
  !p env ss mid out off sv sv' xs vals.
    sym_steps p env 2 ss = SymOK mid /\
    mid.sym_stack = sv' :: ss.sym_stack /\
    (!fn ret op. op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') /\
    mid.sym_mem_labels = ss.sym_mem_labels /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    sym_steps p env (2 * LENGTH xs) mid = SymOK out /\
    out.sym_stack = REVERSE vals ++ mid.sym_stack /\
    LIST_REL (\sv sv'. !fn ret op.
      op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') (MAP SND xs) vals /\
    out.sym_mem_labels = mid.sym_mem_labels /\
    out.sym_base.as_pc = mid.sym_base.as_pc + 2 * LENGTH xs ==>
    ?result values.
      sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK result /\
      result.sym_stack = REVERSE values ++ ss.sym_stack /\
      LIST_REL (\sv sv'. !fn ret op.
        op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
        (MAP SND ((off,sv)::xs)) values /\
      result.sym_mem_labels = ss.sym_mem_labels /\
      result.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH ((off,sv)::xs)
Proof
  rpt strip_tac >> drule_all sym_steps_compose >>
  gvs[arithmeticTheory.MULT_CLAUSES] >> strip_tac >>
  qexists_tac `sv' :: vals` >> simp[]
QED

Theorem sym_restore_offsets_cons_step:
  !xs.
    (!p env ss initial_fmp.
      EVERY (\p. FST p < dimword(:256) /\
        mem_sval_at ss.sym_mem_labels (FST p) (SND p)) xs /\
      asm_block_at p ss.sym_base.as_pc
        (execute_plan initial_fmp (MAP SORestore (MAP FST xs))) ==>
      ?out vals. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
        out.sym_stack = REVERSE vals ++ ss.sym_stack /\
        LIST_REL (\sv sv'. !fn ret op.
          op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') (MAP SND xs) vals /\
        out.sym_mem_labels = ss.sym_mem_labels /\
        out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs) ==>
    !off sv p env ss initial_fmp.
    EVERY (\p. FST p < dimword(:256) /\
      mem_sval_at ss.sym_mem_labels (FST p) (SND p)) ((off,sv)::xs) /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SORestore (MAP FST ((off,sv)::xs)))) ==>
    ?out vals. sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK out /\
      out.sym_stack = REVERSE vals ++ ss.sym_stack /\
      LIST_REL (\sv sv'. !fn ret op.
        op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
        (MAP SND ((off,sv)::xs)) vals /\
      out.sym_mem_labels = ss.sym_mem_labels /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH ((off,sv)::xs)
Proof
  gen_tac >> disch_tac >> rpt gen_tac >>
  pure_rewrite_tac[listTheory.EVERY_DEF, listTheory.MAP,
       pairTheory.FST, pairTheory.SND, listTheory.LENGTH,
       execute_plan_def, listTheory.FLAT, exec_stack_op_def,
       stackOpSimTheory.asm_block_at_append] >>
  pure_rewrite_tac[GSYM execute_plan_def] >> simp[] >> rpt strip_tac >>
  drule_all sym_restore_offset_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  rename1 `sym_steps p env 2 ss = SymOK mid` >>
  `asm_block_at p mid.sym_base.as_pc
    (execute_plan initial_fmp (MAP SORestore (MAP FST xs)))` by simp[] >>
  `EVERY (\p. FST p < dimword(:256) /\
     mem_sval_at mid.sym_mem_labels (FST p) (SND p)) xs` by simp[] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all sym_restore_offsets_cons_result >> simp[]
QED

Theorem sym_restore_offsets_steps:
  !xs p env ss initial_fmp.
    EVERY (\p. FST p < dimword(:256) /\
      mem_sval_at ss.sym_mem_labels (FST p) (SND p)) xs /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SORestore (MAP FST xs))) ==>
    ?out vals. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
      out.sym_stack = REVERSE vals ++ ss.sym_stack /\
      LIST_REL (\sv sv'. !fn ret op.
        op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
        (MAP SND xs) vals /\
      out.sym_mem_labels = ss.sym_mem_labels /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs
Proof
  Induct >- simp[asmSpliceTheory.sym_steps_def] >>
  Cases >> drule sym_restore_offsets_cons_step >> metis_tac[]
QED

Theorem scratch_fold_restore_ready:
  EVERY (\p. FST p < dimword(:256)) xs /\
  ALL_DISTINCT (MAP FST xs) /\
  (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
     FST p + 32 <= FST q \/ FST q + 32 <= FST p) /\
  EVERY (\p. MEM p xs) ys ==>
  EVERY (\p. FST p < dimword(:256) /\
    mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) (FST p) (SND p)) ys
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  metis_tac[scratch_fold_saved, pairTheory.PAIR]
QED

Theorem sym_spill_restore_schedule_steps_fold:
  !xs ys p env ss stk initial_fmp.
    EVERY (\p. FST p < dimword(:256)) xs /\
    ALL_DISTINCT (MAP FST xs) /\
    (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
       FST p + 32 <= FST q \/ FST q + 32 <= FST p) /\
    EVERY (\p. MEM p xs) ys /\
    ss.sym_stack = MAP SND xs ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp
        (MAP SOSpill (MAP FST xs) ++ MAP SORestore (MAP FST ys))) ==>
    ?out vals. sym_steps p env (2 * LENGTH xs + 2 * LENGTH ys) ss = SymOK out /\
      out.sym_stack = REVERSE vals ++ stk /\
      LIST_REL (\sv sv'. !fn ret op.
        op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
        (MAP SND ys) vals /\
      out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels xs /\
      out.sym_base.as_pc = ss.sym_base.as_pc + (2 * LENGTH xs + 2 * LENGTH ys)
Proof
  rpt gen_tac >>
  rewrite_tac[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  strip_tac >> drule_all sym_spill_offsets_steps_fold >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  rename1 `sym_steps p env (2 * LENGTH xs) ss = SymOK mid` >>
  `EVERY (\p. FST p < dimword(:256) /\
    mem_sval_at mid.sym_mem_labels (FST p) (SND p)) ys` by
    (gvs[] >> irule scratch_fold_restore_ready >> metis_tac[]) >>
  `asm_block_at p mid.sym_base.as_pc
    (execute_plan initial_fmp (MAP SORestore (MAP FST ys)))` by
    gvs[doSwapSimTheory.execute_plan_map_spill_length] >>
  drule_all sym_restore_offsets_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexistsl_tac [`out`, `vals`] >>
  drule_all sym_steps_compose >> simp[]
QED

Theorem scratch_ranges_outside:
  !xs R b.
    (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==> R b) /\
    ~R b ==>
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[pairTheory.PAIR]
QED

Theorem scratch_fold_separated_saved:
  !xs labs old saved.
    (!off sv. MEM (off,sv) xs ==> old + 32 <= off \/ off + 32 <= old) ==>
    (mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  rpt strip_tac >> irule scratch_fold_preserves_saved >>
  gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> gvs[]
QED

Theorem scratch_fold_context:
  !labs cp xs.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==>
     context_spill_byte cp b) ==>
  !b. b IN FDOM (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) ==> context_spill_byte cp b
Proof
  simp[GSYM finite_mapTheory.FLOOKUP_DEF, finite_mapTheory.TO_FLOOKUP] >>
  metis_tac[scratch_ranges_outside, scratch_fold_outside]
QED

Theorem sym_kinds_scratch_fold:
  !cp fn ret srest ps ss xs out top stack.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op old off sv. FLOOKUP ps.ps_spilled op = SOME old /\ MEM (off,sv) xs ==>
    old + 32 <= off \/ off + 32 <= old) /\
  (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==>
     context_spill_byte cp b) /\
  out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels xs /\
  out.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE stack) top ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := stack) out
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac
  >- metis_tac[scratch_fold_separated_saved] >>
  metis_tac[scratch_fold_context]
QED

Theorem sym_do_swap_shallow:
  !d ps p env cp fn ret srest initial_fmp lo R ss.
    d <= 16 /\ d < LENGTH ps.ps_stack /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (FST (do_swap d ps))) ==>
    ?out. sym_steps p env
        (LENGTH (execute_plan initial_fmp (FST (do_swap d ps)))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest (SND (do_swap d ps)) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp (FST (do_swap d ps))) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >>
  `SND (do_swap d ps) =
     apply_prefix_ops initial_fmp lo (FST (do_swap d ps)) ps` by
    (Cases_on `d = 0` >>
     simp[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
       mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def]) >>
  pop_assum SUBST1_TAC >> irule sym_prefix_ops_sim >>
  Cases_on `d = 0` >>
  simp[stackPlanOpsTheory.do_swap_def, prefixExecTheory.prefix_wf_def,
    prefixExecTheory.stack_op_wf_def, mixedPrefixSimTheory.prefix_spill_wf_def,
    mixedPrefixSimTheory.spill_op_wf_def, prefixSimTheory.is_prefix_op_def]
QED

Theorem sym_selected_kinds_transport:
  !fn ret items saved indices vals.
    LIST_REL (op_kind_ok fn ret) items saved /\
    EVERY (\i. i < LENGTH items) indices /\
    LIST_REL (\sv sv'. !fn ret op.
      op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
      (MAP (\i. EL i saved) indices) vals ==>
    LIST_REL (op_kind_ok fn ret) (MAP (\i. EL i items) indices) vals
Proof
  rpt strip_tac >> drule_all LIST_REL_select_indices >>
  simp[listTheory.LIST_REL_EL_EQN] >>
  gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem MAP_ZIP_indices:
  !xs ys indices.
    LENGTH xs = LENGTH ys /\ EVERY (\i. i < LENGTH xs) indices ==>
    MAP FST (MAP (\i. EL i (ZIP (xs,ys))) indices) = MAP (\i. EL i xs) indices /\
    MAP SND (MAP (\i. EL i (ZIP (xs,ys))) indices) = MAP (\i. EL i ys) indices
Proof
  rpt strip_tac >> simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> gvs[listTheory.EVERY_MEM, listTheory.EL_ZIP]
QED

Theorem sym_spill_restore_indices_steps_fold:
  !offsets saved indices p env ss stk initial_fmp.
    LENGTH offsets = LENGTH saved /\
    EVERY (\i. i < LENGTH offsets) indices /\
    ALL_DISTINCT offsets /\ EVERY (\off. off < dimword(:256)) offsets /\
    (!a b. MEM a offsets /\ MEM b offsets /\ a <> b ==>
      a + 32 <= b \/ b + 32 <= a) /\
    ss.sym_stack = saved ++ stk /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))) ==>
    ?out vals.
      sym_steps p env (LENGTH (execute_plan initial_fmp
        (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))))
        ss = SymOK out /\
      out.sym_stack = REVERSE vals ++ stk /\
      LIST_REL (\sv sv'. !fn ret op.
        op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
        (MAP (\i. EL i saved) indices) vals /\
      out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels (ZIP (offsets,saved)) /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
        (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices)))
Proof
  rpt strip_tac >>
  `?out vals.
    sym_steps p env (2 * LENGTH (ZIP (offsets,saved)) +
      2 * LENGTH (MAP (\i. EL i (ZIP (offsets,saved))) indices)) ss = SymOK out /\
    out.sym_stack = REVERSE vals ++ stk /\
    LIST_REL (\sv sv'. !fn ret op.
      op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
      (MAP SND (MAP (\i. EL i (ZIP (offsets,saved))) indices)) vals /\
    out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_base.as_pc = ss.sym_base.as_pc +
      (2 * LENGTH (ZIP (offsets,saved)) +
      2 * LENGTH (MAP (\i. EL i (ZIP (offsets,saved))) indices))` by
    (irule sym_spill_restore_schedule_steps_fold >>
     simp[listTheory.MAP_ZIP, listTheory.EVERY_MAP, combinTheory.o_DEF] >>
     conj_tac
     >- (rpt strip_tac >>
         imp_res_tac listTheory.MEM_ZIP_MEM_MAP >> gvs[]) >>
     conj_tac
     >- (rw[listTheory.EVERY_MEM] >>
         imp_res_tac listTheory.MEM_ZIP_MEM_MAP >> gvs[listTheory.EVERY_MEM]) >>
     conj_tac
     >- (gvs[listTheory.EVERY_MEM, listTheory.LENGTH_ZIP] >>
         metis_tac[listTheory.EL_ZIP, listTheory.MEM_ZIP]) >>
     qexists_tac `initial_fmp` >> simp[MAP_ZIP_indices]) >>
  qexistsl_tac [`out`, `vals`] >>
  gvs[MAP_ZIP_indices, doSwapSimTheory.execute_plan_spill_restore_length,
      listTheory.LENGTH_ZIP]
QED

Theorem sym_kinds_zip_scratch_fold:
  !cp fn ret srest ps ps' ss out offsets saved top.
    LENGTH offsets = LENGTH saved /\
    sym_kinds_ok cp fn ret srest ps ss /\
    (!op old off. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offsets ==>
      old + 32 <= off \/ off + 32 <= old) /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==> context_spill_byte cp b) /\
    ps'.ps_spilled = ps.ps_spilled /\
    out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_stack = top ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top ==>
    sym_kinds_ok cp fn ret srest ps' out
Proof
  rpt strip_tac >> rename1 `sym_kinds_ok cp0 fn ret srest ps' out` >>
  `sym_kinds_ok cp0 fn ret srest (ps with ps_stack := ps'.ps_stack) out` by
    (irule sym_kinds_scratch_fold >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`ss`, `ZIP (offsets,saved)`] >> simp[] >>
     rpt strip_tac >> imp_res_tac listTheory.MEM_ZIP_MEM_MAP >>
     gvs[] >> metis_tac[]) >>
  gvs[sym_kinds_ok_def]
QED

Theorem scratch_zip_fold_outside:
  !offsets saved labs R b.
    LENGTH offsets = LENGTH saved /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==> R b) /\ ~R b ==>
    FLOOKUP (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs (ZIP (offsets,saved))) b = FLOOKUP labs b
Proof
  rpt strip_tac >> irule scratch_fold_outside >>
  irule scratch_ranges_outside >> qexists_tac `R` >> simp[] >>
  rpt strip_tac >> imp_res_tac listTheory.MEM_ZIP_MEM_MAP >>
  gvs[] >> metis_tac[]
QED

Theorem sym_scratch_indices_numeric:
  !items tail offsets indices ps ps' p env cp fn ret srest initial_fmp R ss.
    REVERSE ps.ps_stack = items ++ tail /\
    LENGTH offsets = LENGTH items /\
    EVERY (\i. i < LENGTH items) indices /\
    ALL_DISTINCT offsets /\ EVERY (\off. off < dimword(:256)) offsets /\
    (!a b. MEM a offsets /\ MEM b offsets /\ a <> b ==>
      a + 32 <= b \/ b + 32 <= a) /\
    (!op old off. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offsets ==>
      old + 32 <= off \/ off + 32 <= old) /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==>
      context_spill_byte cp b /\ R b) /\
    ps'.ps_spilled = ps.ps_spilled /\
    REVERSE ps'.ps_stack = REVERSE (MAP (\i. EL i items) indices) ++ tail /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp
        (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))) ==>
    ?out. sym_steps p env
        (LENGTH (execute_plan initial_fmp
          (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))))
        ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp
          (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >>
  `?saved tailvals.
    ss.sym_stack = saved ++ tailvals ++ srest /\
    LIST_REL (op_kind_ok fn ret) items saved /\
    LIST_REL (op_kind_ok fn ret) tail tailvals` by
    (gvs[sym_kinds_ok_def, listTheory.LIST_REL_SPLIT1] >> metis_tac[]) >>
  `LENGTH offsets = LENGTH saved` by
    metis_tac[listTheory.LIST_REL_LENGTH] >>
  `?out vals.
    sym_steps p env (LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices))))
      ss = SymOK out /\
    out.sym_stack = REVERSE vals ++ (tailvals ++ srest) /\
    LIST_REL (\sv sv'. !fn ret op.
      op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv')
      (MAP (\i. EL i saved) indices) vals /\
    out.sym_mem_labels = FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices)))` by
    (irule sym_spill_restore_indices_steps_fold >> gvs[]) >>
  `LIST_REL (op_kind_ok fn ret) (MAP (\i. EL i items) indices) vals` by
    (irule sym_selected_kinds_transport >> metis_tac[]) >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack)
     (REVERSE vals ++ tailvals)` by
    (simp[] >> irule listTheory.LIST_REL_APPEND_suff >>
     simp[rich_listTheory.LIST_REL_REVERSE_EQ]) >>
  `out.sym_stack = (REVERSE vals ++ tailvals) ++ srest` by simp[] >>
  rename1 `sym_kinds_ok cp0 fn ret srest ps ss` >>
  `!off b. MEM off offsets /\ in_mem_range off 32 b ==>
    context_spill_byte cp0 b` by metis_tac[] >>
  qexists_tac `out` >> simp[] >> conj_tac
  >- (drule_all sym_kinds_zip_scratch_fold >> simp[]) >>
  rpt strip_tac >> simp[] >>
  irule scratch_zip_fold_outside >> metis_tac[]
QED

Theorem sym_temporary_offsets_resources:
  !al sp items offsets al2 cp R.
    spill_alloc_layout_wf al sp /\
    offsets = FST (spill_alloc_n [] al items) /\
    al2 = FOLDL (\a off. free_spill_slot off a)
      (SND (spill_alloc_n [] al items)) offsets /\
    (!b. al2.sa_spill_base <= b /\ b < al2.sa_next_offset ==>
      context_spill_byte cp b /\ R b) ==>
    LENGTH offsets = LENGTH items /\ ALL_DISTINCT offsets /\
    (!a b. MEM a offsets /\ MEM b offsets /\ a <> b ==>
      a + 32 <= b \/ b + 32 <= a) /\
    (!op old off. FLOOKUP sp op = SOME old /\ MEM off offsets ==>
      old + 32 <= off \/ off + 32 <= old) /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==>
      context_spill_byte cp b /\ R b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all doSwapSimTheory.spill_alloc_n_temporary_layout >> strip_tac >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac
  >- (gvs[listTheory.MEM_EL] >> metis_tac[]) >>
  conj_tac
  >- (gvs[listTheory.MEM_EL] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `al2.sa_spill_base <= b /\ b < al2.sa_next_offset` by
    (gvs[listTheory.EVERY_MEM, in_mem_range_def] >> res_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem sym_do_swap_deep_numeric:
  !d ps p env cp fn ret srest initial_fmp R ss.
    d > 16 /\ d < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) (FST (do_swap d ps)) \/
      MEM (SORestore off) (FST (do_swap d ps)) ==> off < dimword(:256)) /\
    (!b. (SND (do_swap d ps)).ps_alloc.sa_spill_base <= b /\
      b < (SND (do_swap d ps)).ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (FST (do_swap d ps))) ==>
    ?out. sym_steps p env
        (LENGTH (execute_plan initial_fmp (FST (do_swap d ps)))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest (SND (do_swap d ps)) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp (FST (do_swap d ps))) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >>
  qabbrev_tac `items = top_n (d + 1) ps.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `alloc2 = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc items)) offsets` >>
  qabbrev_tac `desired = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]` >>
  qabbrev_tac `tail = TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack` >>
  `do_swap d ps =
    (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired)),
     ps with <|ps_stack := tail ++ MAP (\i. EL i items) desired;
               ps_alloc := alloc2|>)` by
    (drule_all doSwapSimTheory.do_swap_big_decompose >>
     pure_rewrite_tac[LET_THM] >>
     simp[Abbr `items`, Abbr `offsets`, Abbr `alloc2`, Abbr `desired`, Abbr `tail`]) >>
  pop_assum SUBST_ALL_TAC >>
  fs[Excl "MAP", Excl "REVERSE_DEF"] >>
  `LENGTH items = d + 1` by
    (simp[Abbr `items`, stackPlanOpsTheory.top_n_def] >> decide_tac) >>
  `REVERSE ps.ps_stack = REVERSE items ++ REVERSE tail` by
    (simp[GSYM listTheory.REVERSE_APPEND] >>
     simp[Abbr `items`, Abbr `tail`, doSwapSimTheory.top_n_suffix]) >>
  `REVERSE (MAP (\i. EL i items) desired) =
    MAP (\i. EL i (REVERSE items)) desired` by
    (qspecl_then [`items`, `d`] mp_tac doSwapSimTheory.reverse_desired_values >>
     simp[Abbr `desired`]) >>
  `LENGTH offsets = LENGTH items /\ ALL_DISTINCT offsets /\
    (!a b. MEM a offsets /\ MEM b offsets /\ a <> b ==>
      a + 32 <= b \/ b + 32 <= a) /\
    (!op old off. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offsets ==>
      old + 32 <= off \/ off + 32 <= old) /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==>
      context_spill_byte cp' b /\ R b)` by
    (irule sym_temporary_offsets_resources >>
     metis_tac[]) >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    (gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >> metis_tac[]) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule sym_scratch_indices_numeric >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`REVERSE items`, `ps`, `REVERSE tail`] >>
  simp[listTheory.MAP_REVERSE] >>
  simp[Abbr `desired`, listTheory.EVERY_GENLIST] >> gvs[]
QED

Theorem sym_do_swap_numeric:
  !d ps p env cp fn ret srest initial_fmp R ss.
    d < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) (FST (do_swap d ps)) \/
      MEM (SORestore off) (FST (do_swap d ps)) ==> off < dimword(:256)) /\
    (!b. (SND (do_swap d ps)).ps_alloc.sa_spill_base <= b /\
      b < (SND (do_swap d ps)).ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (FST (do_swap d ps))) ==>
    ?out. sym_steps p env
        (LENGTH (execute_plan initial_fmp (FST (do_swap d ps)))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest (SND (do_swap d ps)) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp (FST (do_swap d ps))) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >> Cases_on `d <= 16`
  >- (irule sym_do_swap_shallow >> simp[] >> metis_tac[]) >>
  irule sym_do_swap_deep_numeric >> gvs[] >> metis_tac[]
QED

Theorem sym_numeric_seq:
  !p env cp fn ret srest initial_fmp R ops1 ops2 ps ps1 ps2 ss.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) /\
    (!s. sym_kinds_ok cp fn ret srest ps s /\
      asm_block_at p s.sym_base.as_pc (execute_plan initial_fmp ops1) ==>
      ?t. sym_steps p env (LENGTH (execute_plan initial_fmp ops1)) s = SymOK t /\
        sym_kinds_ok cp fn ret srest ps1 t /\
        t.sym_base.as_pc = s.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops1) /\
        (!b. ~R b ==> FLOOKUP t.sym_mem_labels b = FLOOKUP s.sym_mem_labels b)) /\
    (!s. sym_kinds_ok cp fn ret srest ps1 s /\
      asm_block_at p s.sym_base.as_pc (execute_plan initial_fmp ops2) ==>
      ?t. sym_steps p env (LENGTH (execute_plan initial_fmp ops2)) s = SymOK t /\
        sym_kinds_ok cp fn ret srest ps2 t /\
        t.sym_base.as_pc = s.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops2) /\
        (!b. ~R b ==> FLOOKUP t.sym_mem_labels b = FLOOKUP s.sym_mem_labels b)) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps2 out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2)) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  qpat_x_assum `!s. sym_kinds_ok _ _ _ _ ps s /\ _ ==> _`
    (qspec_then `ss` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
  qexists `t'` >> simp[] >> metis_tac[sym_steps_compose, arithmeticTheory.ADD_ASSOC]
QED

Theorem sym_swap_pop_numeric:
  !d n ps p env cp fn ret srest initial_fmp R ss.
    d < LENGTH ps.ps_stack /\ n <= LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) (FST (do_swap d ps)) \/
      MEM (SORestore off) (FST (do_swap d ps)) ==> off < dimword(:256)) /\
    (!b. (SND (do_swap d ps)).ps_alloc.sa_spill_base <= b /\
      b < (SND (do_swap d ps)).ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (FST (do_swap d ps) ++ [SOPop n])) ==>
    ?out. sym_steps p env
        (LENGTH (execute_plan initial_fmp (FST (do_swap d ps) ++ [SOPop n]))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest
        ((SND (do_swap d ps)) with ps_stack := stack_pop n (SND (do_swap d ps)).ps_stack) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp (FST (do_swap d ps) ++ [SOPop n])) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >> irule sym_numeric_seq >> (conj_tac >- asm_rewrite_tac[]) >>
  qexistsl [`ps`, `SND (do_swap d ps)`] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> irule sym_do_swap_numeric >> metis_tac[]) >>
  rpt strip_tac >> irule symShuffleSimTheory.sym_pop_numeric >> simp[planWfTheory.do_swap_length]
QED

Theorem pop_one_some_alloc_mono:
  !item ps d ops ps'.
    stack_get_depth item ps.ps_stack = SOME d /\
    cleanOpsSim$pop_one_step item ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt strip_tac >>
  drule fnFrameBoundaryEntryParamsTheory.entry_pop_one_step_some >> strip_tac >> gvs[] >>
  metis_tac[allocMonoTheory.do_swap_spill_base, allocMonoTheory.do_swap_next_offset,
    pairTheory.PAIR]
QED

Theorem pop_one_step_alloc_mono:
  !item ps ops ps'.
    cleanOpsSim$pop_one_step item ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> Cases_on `stack_get_depth item ps.ps_stack`
  >- simp[cleanOpsSimTheory.pop_one_step_def] >>
  metis_tac[pop_one_some_alloc_mono]
QED

Theorem pop_steps_alloc_mono_cons:
  !items.
    (!ps ops ps'.
      foldlSim$plan_steps cleanOpsSim$pop_one_step items ps = (ops,ps') ==>
      ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
      ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset) ==>
    !item ps ops ps'.
      foldlSim$plan_steps cleanOpsSim$pop_one_step (item::items) ps = (ops,ps') ==>
      ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
      ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  drule reorderPreparationPropsTheory.plan_steps_cons_result >> strip_tac >>
  drule pop_one_step_alloc_mono >> first_x_assum drule >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem pop_steps_alloc_mono:
  !items ps ops ps'.
    foldlSim$plan_steps cleanOpsSim$pop_one_step items ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Induct >- simp[foldlSimTheory.plan_steps_def] >>
  drule pop_steps_alloc_mono_cons >> simp[]
QED

Theorem pop_one_some_layout:
  !item d ps ops ps'.
    stack_get_depth item ps.ps_stack = SOME d /\
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt strip_tac >>
  drule fnFrameBoundaryEntryParamsTheory.entry_pop_one_step_some >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[planWfTheory.stack_get_depth_bound] >>
  drule_all doSwapSimTheory.do_swap_layout_wf >> strip_tac >> gvs[]
QED

Theorem pop_one_step_layout:
  !item ps ops ps'.
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt strip_tac >> Cases_on `stack_get_depth item ps.ps_stack`
  >- gvs[cleanOpsSimTheory.pop_one_step_def] >>
  metis_tac[pop_one_some_layout]
QED

Theorem sym_pop_one_some_numeric:
  !item d ps ops ps' p env cp fn ret srest initial_fmp R ss.
    stack_get_depth item ps.ps_stack = SOME d /\
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule fnFrameBoundaryEntryParamsTheory.entry_pop_one_step_some >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[planWfTheory.stack_get_depth_bound] >>
  gvs[] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule sym_swap_pop_numeric >> gvs[] >> metis_tac[]
QED

Theorem sym_pop_one_numeric:
  !item ps ops ps' p env cp fn ret srest initial_fmp R ss.
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `stack_get_depth item ps.ps_stack`
  >- (gvs[cleanOpsSimTheory.pop_one_step_def] >> qexists `ss` >>
      simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  drule_all sym_pop_one_some_numeric >> simp[]
QED

Theorem sym_pop_steps_cons_numeric:
  !items.
    (!ps ops ps' p env cp fn ret srest initial_fmp R ss.
      foldlSim$plan_steps cleanOpsSim$pop_one_step items ps = (ops,ps') /\
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
      (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
        context_spill_byte cp b /\ R b) /\
      sym_kinds_ok cp fn ret srest ps ss /\
      asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
      ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
        sym_kinds_ok cp fn ret srest ps' out /\
        out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
        (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)) ==>
  !item ps ops ps' p env cp fn ret srest initial_fmp R ss.
    foldlSim$plan_steps cleanOpsSim$pop_one_step (item::items) ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  drule reorderPreparationPropsTheory.plan_steps_cons_result >> strip_tac >> gvs[] >>
  drule_all pop_one_step_layout >> strip_tac >>
  drule pop_steps_alloc_mono >> strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> irule sym_numeric_seq >>
  (conj_tac >- asm_rewrite_tac[]) >>
  qexistsl [`ps`, `ps1`] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> irule sym_pop_one_numeric >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  rw[] >> first_x_assum irule >> metis_tac[]
QED

Theorem sym_pop_steps_numeric:
  !items ps ops ps' p env cp fn ret srest initial_fmp R ss.
    foldlSim$plan_steps cleanOpsSim$pop_one_step items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Induct
  >- (rw[foldlSimTheory.plan_steps_def] >> qexists `ss` >>
      simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  rw[] >> drule_all (SRULE [] sym_pop_steps_cons_numeric) >> simp[]
QED

Theorem sym_popmany_individual_numeric:
  !items ps ops ps' p env cp fn ret srest initial_fmp R ss.
    popmany_individual items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[cleanOpsSimTheory.popmany_individual_eq_foldl,
    cleanOpsSimTheory.pop_foldl_body_eq_foldl_body, GSYM foldlSimTheory.plan_steps_eq_foldl] >>
  strip_tac >> drule_all sym_pop_steps_numeric >> simp[]
QED

Theorem popmany_contiguous_result:
  !items ps.
    items <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items)) ==>
    popmany_plan items ps =
      (FST (do_swap (LENGTH items) ps) ++ [SOPop (LENGTH items)],
       (SND (do_swap (LENGTH items) ps)) with
         ps_stack := stack_pop (LENGTH items) (SND (do_swap (LENGTH items) ps)).ps_stack)
Proof
  Cases_on `items` >> simp[stackPlanOpsTheory.popmany_plan_def, pairTheory.UNCURRY]
QED

Theorem sym_popmany_contiguous_numeric:
  !items ps ops ps' p env cp fn ret srest initial_fmp R ss.
    items <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items)) /\
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH items < LENGTH ps.ps_stack` by
    (irule cleanOpsSimTheory.contiguous_top_stack_bound >> simp[]) >>
  drule_all popmany_contiguous_result >> strip_tac >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule sym_swap_pop_numeric >> gvs[] >> metis_tac[]
QED

Theorem sym_popmany_numeric:
  !items ps ops ps' p env cp fn ret srest initial_fmp R ss.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `items = []`
  >- (gvs[stackPlanOpsTheory.popmany_plan_def] >> qexists `ss` >>
      simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- (irule sym_popmany_contiguous_numeric >> metis_tac[]) >>
  drule_all_then assume_tac cleanOpsSimTheory.popmany_plan_noncontig_new >>
  drule_all sym_popmany_individual_numeric >> simp[]
QED

Theorem sym_poke_popmany_numeric:
  !items ps d op ops next p env cp fn ret srest initial_fmp R ss.
    (\(pop_ops,ps'). (SOPoke d op :: pop_ops,ps'))
      (popmany_plan items (ps with ps_stack := stack_poke d op ps.ps_stack)) = (ops,next) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    d < LENGTH ps.ps_stack /\
    (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==> op_kind_ok fn ret op sv) /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest next out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> pairarg_tac >> gvs[] >>
  drule_all sym_kinds_stack_poke >> strip_tac >>
  `spill_alloc_layout_wf
    (ps with ps_stack := stack_poke d op ps.ps_stack).ps_alloc
    (ps with ps_stack := stack_poke d op ps.ps_stack).ps_spilled` by simp[] >>
  rename1 `popmany_plan items _ = (pops,next)` >>
  `execute_plan initial_fmp (SOPoke d op :: pops) = execute_plan initial_fmp pops`
    by simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
  asm_rewrite_tac[] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule sym_popmany_numeric >> metis_tac[]
QED

Theorem sym_poke_numeric:
  !ps d op p env cp fn ret srest initial_fmp R ss.
    sym_kinds_ok cp fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
    (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==> op_kind_ok fn ret op sv) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPoke d op])) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest (ps with ps_stack := stack_poke d op ps.ps_stack) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOPoke d op]) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_kinds_stack_poke >> strip_tac >>
  qexists `ss` >> simp[planExecTheory.execute_plan_def,
    planExecTheory.exec_stack_op_def, asmSpliceTheory.sym_steps_def]
QED

Theorem sym_phi_plan_hit_no_dup_numeric:
  !inst live halt ps ops next d p env cp fn ret srest initial_fmp R ss.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    ~MEM (operand_to_string (stack_peek d ps.ps_stack)) live /\
    d < LENGTH ps.ps_stack /\
    (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
          op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv) /\
    generate_phi_plan inst live halt ps = (ops,next) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest next out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameStepsPhiTheory.phi_plan_hit_no_dup >> strip_tac >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) live`
  >- (gvs[] >> drule_all sym_poke_popmany_numeric >> simp[]) >>
  gvs[] >> drule_all sym_poke_numeric >> simp[]
QED

Theorem sym_phi_plan_no_dup_numeric:
  !inst live halt ps ops next p env cp fn ret srest initial_fmp R ss.
    generate_phi_plan inst live halt ps = (ops,next) /\
    (!d. stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
      d < LENGTH ps.ps_stack /\
      ~MEM (operand_to_string (stack_peek d ps.ps_stack)) live /\
      (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
            op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest next out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (drule fnFrameStepsPhiTheory.phi_plan_no_hit >> strip_tac >>
      gvs[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  irule sym_phi_plan_hit_no_dup_numeric >> metis_tac[]
QED

Theorem phi_input_not_code_end_own:
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  rw[label_flow_own_ok_def] >>
  first_x_assum drule_all >> simp[] >> metis_tac[]
QED

Theorem phi_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem phi_operand_kind_transport_own:
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  strip_tac >>
  drule_all phi_input_not_code_end_own >> strip_tac >>
  drule_all phi_output_not_code_end >> strip_tac >>
  drule_all frameViewFactsTheory.phi_output_retpc >> strip_tac >>
  gvs[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem phi_run_inst_kind_own:
  phi_run_context fn bb pred entry source final /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  MEM (Var y) inst.inst_operands /\ op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv
Proof
  rewrite_tac[fnFrameStepsPhiTheory.phi_run_context_def] >> strip_tac >>
  drule_all fnPlanPrefixTheory.phi_codegen_inst_shape >> strip_tac >>
  `MEM (HD inst.inst_outputs) inst.inst_outputs` by
    (Cases_on `inst.inst_outputs` >> gvs[]) >>
  irule phi_operand_kind_transport_own >>
  gvs[codegen_ready_fn_def] >>
  metis_tac[livenessProofsTheory.collect_phis_mem,
    unitShapeDefsTheory.MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def]
QED

Theorem phi_run_hit_dead:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  ~MEM (operand_to_string (stack_peek d ps.ps_stack))
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done)))
Proof
  rewrite_tac[fnFrameStepsPhiTheory.phi_run_context_def] >> strip_tac >>
  drule fnFrameStepsPhiTheory.phi_stack_hit_operand >> strip_tac >>
  Cases_on `stack_peek d ps.ps_stack` >>
  gvs[is_var_operand_def, operand_to_string_def] >>
  irule fnFrameStepsPhiTheory.phi_input_dead_at_successor >>
  simp[listTheory.EL_APPEND_EQN]
QED

Theorem phi_run_hit_kind_own:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
    op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)
Proof
  strip_tac >> drule fnFrameStepsPhiTheory.phi_stack_hit_operand >> strip_tac >>
  Cases_on `stack_peek d ps.ps_stack` >> gvs[is_var_operand_def] >>
  metis_tac[phi_run_inst_kind_own, listTheory.MEM_APPEND, listTheory.MEM]
QED

Theorem sym_phi_run_step_own:
  !fn bb pred entry source final done inst todo ps halt ops next
    prog initial_fmp cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  generate_phi_plan inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps =
    (ops,next) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
  (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ R b) /\
  sym_kinds_ok cp fn ret srest ps ss /\
  asm_block_at prog ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?out. sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest next out /\
    out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> irule sym_phi_plan_no_dup_numeric >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[phi_run_hit_dead, phi_run_hit_kind_own,
    genBlockSimTheory.stack_get_phi_depth_var_not_marker]
QED

Theorem paired_phi_run_step_own:
  !base fn bb pred entry source final done inst todo ra lo m ps st halt ops next
    prog initial_fmp o2pc cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  phi_run_config fn ra lo base pred entry source m done (inst::todo) ps st /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  generate_phi_plan inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps =
    (ops,next) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ R b) /\
  sym_kinds_ok cp fn ret srest ps ss /\ ss.sym_base.as_pc = st.as_pc /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st' out.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ [inst]) todo next st' /\
    sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest next out /\ out.sym_base.as_pc = st'.as_pc /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameStepsPhiTheory.phi_run_step >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    gvs[fnFrameStepsPhiTheory.phi_run_config_def] >>
  `!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  drule_all sym_phi_run_step_own >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem block_insts_prefix_alloc_mono:
  !j insts lv dfg cfg fn lbl halt np bl i ps ops qs.
  generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i j insts ps = SOME (ops,qs) ==>
  qs.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
  ps.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset
Proof
  Induct >> simp[fnPlanPrefixTheory.generate_block_insts_prefix_def] >>
  rpt gen_tac >> Cases_on `insts` >> simp[fnPlanPrefixTheory.generate_block_insts_prefix_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule allocMonoTheory.generate_inst_plan_spill_base >> strip_tac >>
  drule allocMonoTheory.generate_inst_plan_next_offset >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem paired_steps_add_preserve:
  !lo o2pc prog env a mid z ss sm sz n k R.
  asm_steps lo o2pc prog n a = AsmOK mid /\
  asm_steps lo o2pc prog k mid = AsmOK z /\
  mid.as_pc = a.as_pc + n /\ z.as_pc = mid.as_pc + k /\
  sym_steps prog env n ss = SymOK sm /\ sym_steps prog env k sm = SymOK sz /\
  (!b. ~R b ==> FLOOKUP sm.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~R b ==> FLOOKUP sz.sym_mem_labels b = FLOOKUP sm.sym_mem_labels b) ==>
  asm_steps lo o2pc prog (n+k) a = AsmOK z /\ z.as_pc = a.as_pc + (n+k) /\
  sym_steps prog env (n+k) ss = SymOK sz /\
  (!b. ~R b ==> FLOOKUP sz.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >> simp[stackOpSimTheory.asm_steps_add_ok, sym_steps_add] >>
  metis_tac[stackOpSimTheory.asm_steps_add_ok, arithmeticTheory.ADD_SYM]
QED

Theorem phi_run_prefix_cons_split:
  !fn bb pred entry source final done inst todo body ps halt block_len dfg cfg
    ops last cp R prog pc initial_fmp.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  block_len = LENGTH done + LENGTH (inst::todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH (inst::todo)) (inst::todo ++ body) ps =
    SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ R b) /\
  asm_block_at prog pc (execute_plan initial_fmp ops) ==>
  ?step_ops next tail_ops.
    ops = step_ops ++ tail_ops /\
    generate_phi_plan inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps =
      (step_ops,next) /\
    generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
      halt 0 block_len (LENGTH (done ++ [inst])) (LENGTH todo) (todo ++ body) next =
      SOME (tail_ops,last) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) step_ops /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) tail_ops /\
    (!b. next.ps_alloc.sa_spill_base <= b /\ b < next.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    asm_block_at prog pc (execute_plan initial_fmp step_ops) /\
    asm_block_at prog (pc + LENGTH (execute_plan initial_fmp step_ops))
      (execute_plan initial_fmp tail_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode = PHI` by
    (irule (cj 1 fnPlanPrefixTheory.phi_codegen_inst_shape) >>
     gvs[fnFrameStepsPhiTheory.phi_run_context_def] >>
     metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[fnFrameStepsPhiTheory.phi_prefix_cons_plan] >>
  Cases_on `generate_phi_plan inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps` >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule block_insts_prefix_alloc_mono >> strip_tac >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
    listTheory.EVERY_APPEND] >>
  gvs[arithmeticTheory.SUC_ONE_ADD] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem paired_phi_run_prefix_cons_own:
  !todo.
  (!done base fn bb pred entry source final ra lo m ps st body block_len
    dfg (cfg:'cfg) halt ops last prog initial_fmp o2pc cp ctx ret srest R env ss.
    phi_run_context fn bb pred entry source final /\
    collect_phis bb.bb_instructions = done ++ todo /\
    phi_run_config fn ra lo base pred entry source m done todo ps st /\
    block_len = LENGTH done + LENGTH (todo ++ body) /\
    generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
      halt 0 block_len (LENGTH done) (LENGTH todo) (todo ++ body) ps = SOME (ops,last) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
    (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\ ss.sym_base.as_pc = st.as_pc /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st' out.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last st' /\
      sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest last out /\ out.sym_base.as_pc = st'.as_pc /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)) ==>
  !inst done base fn bb pred entry source final ra lo m ps st body block_len
    dfg (cfg:'cfg) halt ops last prog initial_fmp o2pc cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  phi_run_config fn ra lo base pred entry source m done (inst::todo) ps st /\
  block_len = LENGTH done + LENGTH (inst::todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH (inst::todo)) (inst::todo ++ body) ps = SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ R b) /\
  sym_kinds_ok cp fn ret srest ps ss /\ ss.sym_base.as_pc = st.as_pc /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st' out.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ inst::todo) [] last st' /\
    sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest last out /\ out.sym_base.as_pc = st'.as_pc /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  drule_all phi_run_prefix_cons_split >> strip_tac >>
  drule_all paired_phi_run_step_own >>
  disch_then (qspecl_then [`o2pc`, `env`] strip_assume_tac) >>
  rename1 `asm_steps lo o2pc prog _ st = AsmOK middle` >>
  `collect_phis bb.bb_instructions = (done ++ [inst]) ++ todo` by simp[] >>
  `asm_block_at prog middle.as_pc (execute_plan initial_fmp tail_ops)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  rename1 `block_len = LENGTH done + LENGTH (inst::todo ++ suffix)` >>
  first_x_assum (qspec_then `done ++ [inst]` mp_tac) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then `suffix` mp_tac) >>
  qpat_x_assum `block_len = _` SUBST_ALL_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss
    [listTheory.LENGTH_APPEND, listTheory.LENGTH, arithmeticTheory.ADD1,
     arithmeticTheory.ADD_CLAUSES,
     AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp_tac bool_ss [listTheory.LENGTH_APPEND, listTheory.LENGTH,
    arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`o2pc`, `env`] strip_assume_tac) >>
  drule_all paired_steps_add_preserve >> strip_tac >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `phi_run_config _ _ _ _ _ _ _ _ (_ ++ [_] ++ _) [] _ _`
    (mp_tac o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  gvs[stackOpSimTheory.execute_plan_append]
QED

Theorem paired_phi_run_prefix_legacy_own:
  !todo done base fn bb pred entry source final ra lo m ps st body block_len
    dfg cfg halt ops last prog initial_fmp o2pc cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ todo /\
  phi_run_config fn ra lo base pred entry source m done todo ps st /\
  block_len = LENGTH done + LENGTH (todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH todo) (todo ++ body) ps = SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ R b) /\
  sym_kinds_ok cp fn ret srest ps ss /\ ss.sym_base.as_pc = st.as_pc /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st' out.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last st' /\
    sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest last out /\ out.sym_base.as_pc = st'.as_pc /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Induct >- (rpt gen_tac >> simp[fnPlanPrefixTheory.generate_block_insts_prefix_def] >>
    strip_tac >> gvs[] >> qexistsl [`st`, `ss`] >>
    simp[execute_plan_def, asm_steps_def, asmSpliceTheory.sym_steps_def]) >>
  drule paired_phi_run_prefix_cons_own >> simp[]
QED

Theorem param_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  ~code_end_var fn x
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> gvs[]
QED

Theorem param_output_retpc_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (retpc_var fn x <=> inst.inst_opcode = RETPC_PARAM)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule (cj 3 (iffLR retpc_shape_ok_def)) >>
      disch_then drule_all >> gvs[]) >>
  strip_tac >> simp[retpc_var_def] >>
  irule (cj 1 copy_phi_var_rules) >> metis_tac[]
QED

Theorem param_output_kind:
  ssa_form fn /\ retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (op_kind_ok fn ret (Var x) sv <=>
   if inst.inst_opcode = RETPC_PARAM then sv = Lab ret 0
   else ?w. sv = Val w)
Proof
  strip_tac >> drule_all param_output_not_code_end >> strip_tac >>
  drule_all param_output_retpc_kind >> strip_tac >>
  simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
QED

Theorem entry_param_kind:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  MEM inst (get_params (HD fn.fn_blocks).bb_instructions) ==>
  (op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv <=>
   if inst.inst_opcode = RETPC_PARAM then sv = Lab ret 0 else ?w. sv = Val w)
Proof
  strip_tac >>
  drule (cj 1 fnFrameBoundaryEntryParamsTheory.canonical_get_params_layout) >>
  disch_then (qspec_then `get_params (HD fn.fn_blocks).bb_instructions` mp_tac) >>
  simp[] >> strip_tac >>
  `?j. j < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
       inst = EL j (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[listTheory.MEM_EL] >>
  drule_all fnFrameBoundaryEntryParamsTheory.param_insts_from_el >> simp[] >> strip_tac >>
  irule param_output_kind >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac
    fnFrameBoundaryEntryParamsTheory.get_params_suffix >>
  Cases_on `fn.fn_blocks` >>
  gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def,
    callLayoutDefsTheory.param_inst_at_def,
    listTheory.LENGTH_EQ_NUM_compute, venomInstTheory.is_param_opcode_iff,
    venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def] >>
  metis_tac[listTheory.MEM_APPEND]
QED

Theorem entry_param_list_kinds:
  !fn params ret ws.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  params = get_params (HD fn.fn_blocks).bb_instructions /\
  LENGTH ws + (if fn_has_retpc fn then 1 else 0) = LENGTH params ==>
  LIST_REL (op_kind_ok fn ret) (MAP (\i. Var (HD i.inst_outputs)) params)
    (MAP Val ws ++ if fn_has_retpc fn then [Lab ret 0] else [])
Proof
  rpt gen_tac >> strip_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >>
  conj_tac >- (Cases_on `fn_has_retpc fn` >> gvs[]) >>
  rpt strip_tac >> simp[listTheory.EL_MAP] >>
  `MEM (EL n params) (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[listTheory.EL_MEM, listTheory.LENGTH_MAP] >>
  drule_all entry_param_kind >> strip_tac >>
  drule_all fnFrameBoundaryEntryParamsTheory.canonical_get_params_layout >> strip_tac >>
  `fn_has_retpc fn <=> EXISTS (\i. i.inst_opcode = RETPC_PARAM) params` by
    gvs[frameRelTheory.fn_has_retpc_def] >>
  `~EXISTS (\i. i.inst_opcode = RETPC_PARAM) ordinary` by
    (gvs[listTheory.EXISTS_MEM, listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `params = get_params _`
    (fn th => full_simp_tac pure_ss [GSYM th]) >>
  gvs[listTheory.EXISTS_APPEND] >>
  Cases_on `n < LENGTH ordinary` >>
  gvs[listTheory.EL_APPEND_EQN, listTheory.EVERY_EL,
      listTheory.EL_MAP] >>
  `n = LENGTH ordinary` by decide_tac >> gvs[]
QED

Theorem entry_installed_sym_kinds:
  !fn params ws pi ch growth spill_base lbl_ctr ss ret srest cp.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  params = get_params (HD fn.fn_blocks).bb_instructions /\
  LENGTH ws + (if fn_has_retpc fn then 1 else 0) = LENGTH params /\
  pi = (init_cleanup_plan_state ch growth spill_base lbl_ctr) with
    ps_stack := MAP (\i. Var (HD i.inst_outputs)) params /\
  ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
    MAP Val (REVERSE ws) ++ srest /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  sym_kinds_ok cp fn ret srest pi ss
Proof
  rpt gen_tac >> strip_tac >> drule_all entry_param_list_kinds >>
  disch_then (qspec_then `ret` mp_tac) >>
  strip_tac >> Cases_on `fn_has_retpc fn` >> gvs[] >>
  drule listTheory.EVERY2_REVERSE >>
  pure_rewrite_tac [listTheory.REVERSE_APPEND, listTheory.REVERSE_DEF] >>
  strip_tac >>
  gvs[sym_kinds_ok_def, init_cleanup_plan_state_def, init_plan_state_def,
      listTheory.MAP_REVERSE]
QED

Theorem op_kinds_forget_map:
  !xs ys f fn ret.
    LIST_REL (op_kind_ok fn ret) xs ys /\
    (!op. MEM op xs ==> f op = dead_stack_marker \/ f op = op) ==>
    LIST_REL (op_kind_ok fn ret) (MAP f xs) ys
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[listTheory.LIST_REL_CONS1] >> rpt strip_tac >> gvs[] >>
  metis_tac[op_kind_ok_def]
QED

Theorem sym_kinds_forget_map:
  !cp fn ret srest ps ss f.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := MAP f ps.ps_stack) ss
Proof
  simp[sym_kinds_ok_def, listTheory.MAP_REVERSE] >> rpt strip_tac >>
  qexists `top` >> simp[] >>
  pure_rewrite_tac[GSYM listTheory.MAP_REVERSE] >>
  irule op_kinds_forget_map >> simp[]
QED

Theorem sym_kinds_forget_promised:
  !cp fn ret srest ps ss f promised.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
  sym_kinds_ok cp fn ret srest
    (ps with <|ps_stack := MAP f ps.ps_stack; ps_cleanup_promised := promised|>) ss
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_kinds_forget_map >>
  simp[sym_kinds_ok_def]
QED

Theorem sym_empty_forget_numeric:
  !ps ps' p env cp fn ret srest initial_fmp R ss f promised.
  ps' = ps with <|ps_stack := MAP f ps.ps_stack; ps_cleanup_promised := promised|> /\
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
  ?out. sym_steps p env (LENGTH (execute_plan initial_fmp [])) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest ps' out /\
    out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp []) /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> qexists `ss` >>
  simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >>
  gvs[] >> irule sym_kinds_forget_promised >> simp[]
QED

Theorem sym_popmany_forget_numeric:
  !items ps ops mid ps' p env cp fn ret srest initial_fmp R ss f promised.
    popmany_plan items ps = (ops,mid) /\
    ps' = mid with <|ps_stack := MAP f mid.ps_stack; ps_cleanup_promised := promised|> /\
    (!op. MEM op mid.ps_stack ==> f op = dead_stack_marker \/ f op = op) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `sym_kinds_ok cplan fn ret srest ps ss` >>
  `!b. mid.ps_alloc.sa_spill_base <= b /\ b < mid.ps_alloc.sa_next_offset ==>
    context_spill_byte cplan b /\ R b` by gvs[] >>
  drule_all sym_popmany_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `out` >> simp[] >> gvs[] >>
  irule sym_kinds_forget_promised >> simp[]
QED

Theorem sym_popmany_mark_numeric:
  !items retained promised ps ops ps' p env cp fn ret srest initial_fmp R ss.
    (\(code,mid). (code, mid with
      <|ps_stack := mark_dead_stack retained mid.ps_stack;
        ps_cleanup_promised := promised|>)) (popmany_plan items ps) = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> pairarg_tac >> gvs[mark_dead_stack_def] >>
  drule_all sym_popmany_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `out` >> simp[] >>
  irule sym_kinds_forget_promised >> simp[] >> metis_tac[]
QED

Theorem sym_clean_stack_plan_numeric:
  !liveness cfg fn bb ps ops ps' p env cp ret srest initial_fmp R ss.
    clean_stack_plan liveness cfg fn bb ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >> metis_tac[]) >>
  rename1 `cfg_preds_of _ _ = pred_label::other_preds` >>
  Cases_on `other_preds`
  >- (simp[] >> IF_CASES_TAC
      >- (simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >> metis_tac[]) >>
      Cases_on `lookup_block pred_label fn.fn_blocks`
      >- (simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >> metis_tac[]) >>
      simp[] >> qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (disch_then (strip_assume_tac o GSYM) >> gvs[execute_plan_def, asmSpliceTheory.sym_steps_def] >>
          metis_tac[sym_kinds_forget_promised, combinTheory.K_THM]) >>
      IF_CASES_TAC
      >- (strip_tac >> drule_all sym_popmany_mark_numeric >>
          disch_then (qspec_then `env` (fn th => metis_tac[th, arithmeticTheory.ADD_COMM]))) >>
      strip_tac >> drule_all sym_popmany_numeric >>
      disch_then (qspec_then `env` (fn th => metis_tac[th, arithmeticTheory.ADD_COMM]))) >>
  simp[execute_plan_def, asmSpliceTheory.sym_steps_def] >> metis_tac[]
QED

Theorem sym_clean_stack_plan_numeric_mode:
  !allow_own own liveness cfg fn bb ps ops ps' p env cp ret srest initial_fmp R ss.
    clean_stack_plan liveness cfg fn bb ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps_mode allow_own p env own
        (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_clean_stack_plan_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `out` >> simp[] >> irule sym_steps_mode_ok >> simp[]
QED

Theorem do_swap_deep_restore_was_spilled:
  !d ps off. d > 16 /\ d < LENGTH ps.ps_stack /\
    MEM (SORestore off) (FST (do_swap d ps)) ==>
    MEM (SOSpill off) (FST (do_swap d ps))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all doSwapSimTheory.do_swap_big_decompose >>
  simp[LET_THM] >> disch_then SUBST_ALL_TAC >>
  gvs[listTheory.MEM_MAP] >>
  rewrite_tac[GSYM (CONJUNCT1 listTheory.EL)] >>
  match_mp_tac listTheory.EL_MEM >>
  simp[doSwapSimTheory.spill_alloc_n_offsets_length, stackPlanOpsTheory.top_n_def] >>
  gvs[listTheory.MEM_GENLIST] >> decide_tac
QED

Theorem do_swap_restore_was_spilled:
  !d ps off. d < LENGTH ps.ps_stack /\
    MEM (SORestore off) (FST (do_swap d ps)) ==>
    MEM (SOSpill off) (FST (do_swap d ps))
Proof
  rpt gen_tac >> Cases_on `d <= 16`
  >- (Cases_on `d = 0` >> simp[stackPlanOpsTheory.do_swap_def]) >>
  simp[do_swap_deep_restore_was_spilled, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem pop_one_restore_was_spilled:
  !item ps ops qs off.
    cleanOpsSim$pop_one_step item ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  rpt gen_tac >> strip_tac >> Cases_on `stack_get_depth item ps.ps_stack`
  >- gvs[cleanOpsSimTheory.pop_one_step_def] >>
  drule fnFrameBoundaryEntryParamsTheory.entry_pop_one_step_some >> strip_tac >>
  gvs[] >> metis_tac[do_swap_restore_was_spilled, planAlignTheory.stack_get_depth_bound]
QED

Theorem pop_steps_restore_was_spilled:
  !items ps ops qs off.
    plan_steps cleanOpsSim$pop_one_step items ps = (ops,qs) /\
    MEM (SORestore off) ops ==> MEM (SOSpill off) ops
Proof
  Induct >- simp[foldlSimTheory.plan_steps_def] >>
  rpt gen_tac >>
  Cases_on `cleanOpsSim$pop_one_step h ps` >>
  rename1 `cleanOpsSim$pop_one_step h ps = (head_ops,mid)` >>
  Cases_on `plan_steps cleanOpsSim$pop_one_step items mid` >>
  simp[foldlSimTheory.plan_steps_def] >>
  metis_tac[pop_one_restore_was_spilled, listTheory.MEM_APPEND]
QED

Theorem popmany_individual_restore_was_spilled:
  !items ps ops qs off.
    popmany_individual items ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  pure_rewrite_tac[cleanOpsSimTheory.popmany_individual_eq_foldl,
    cleanOpsSimTheory.pop_foldl_body_eq_foldl_body, GSYM foldlSimTheory.plan_steps_eq_foldl] >>
  metis_tac[pop_steps_restore_was_spilled]
QED

Theorem popmany_restore_was_spilled:
  !items ps ops qs off.
    popmany_plan items ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  rpt gen_tac >> strip_tac >> Cases_on `items = []`
  >- gvs[stackPlanOpsTheory.popmany_plan_def] >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- (gvs[] >> drule_all popmany_contiguous_result >> strip_tac >> gvs[] >>
      metis_tac[do_swap_restore_was_spilled, cleanOpsSimTheory.contiguous_top_stack_bound]) >>
  drule_all_then assume_tac cleanOpsSimTheory.popmany_plan_noncontig_new >>
  metis_tac[popmany_individual_restore_was_spilled]
QED

Theorem pop_steps_layout:
  !items ps ops qs.
    plan_steps cleanOpsSim$pop_one_step items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  Induct >- simp[foldlSimTheory.plan_steps_def] >>
  rpt gen_tac >> strip_tac >>
  drule reorderPreparationPropsTheory.plan_steps_cons_result >> strip_tac >> gvs[] >>
  metis_tac[pop_one_step_layout]
QED

Theorem popmany_individual_layout:
  !items ps ops qs.
    popmany_individual items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  pure_rewrite_tac[cleanOpsSimTheory.popmany_individual_eq_foldl,
    cleanOpsSimTheory.pop_foldl_body_eq_foldl_body, GSYM foldlSimTheory.plan_steps_eq_foldl] >>
  metis_tac[pop_steps_layout]
QED

Theorem popmany_contiguous_layout:
  !items ps ops qs.
    items <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items)) /\
    popmany_plan items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH items < LENGTH ps.ps_stack` by
    (irule cleanOpsSimTheory.contiguous_top_stack_bound >> simp[]) >>
  drule_all popmany_contiguous_result >> strip_tac >> gvs[] >>
  metis_tac[doSwapSimTheory.do_swap_layout_wf]
QED

Theorem popmany_layout:
  !items ps ops qs.
    popmany_plan items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `items = []`
  >- gvs[stackPlanOpsTheory.popmany_plan_def] >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- (irule popmany_contiguous_layout >> metis_tac[]) >>
  drule_all_then assume_tac cleanOpsSimTheory.popmany_plan_noncontig_new >>
  metis_tac[popmany_individual_layout]
QED

Theorem sym_depth_swap_numeric:
  !item d ps ops ps' p env cp fn ret srest initial_fmp R ss.
    stack_get_depth item ps.ps_stack = SOME d /\ do_swap d ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[planAlignTheory.stack_get_depth_bound] >>
  mp_tac (Q.SPECL [`d`, `ps`] sym_do_swap_numeric) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem optimistic_swap_restore_was_spilled:
  !dfg inst live term ps ops qs off.
    optimistic_swap_plan dfg inst live term ps = (ops,qs) /\
    MEM (SORestore off) ops ==> MEM (SOSpill off) ops
Proof
  rpt gen_tac >> strip_tac >>
  gvs[stackPlanGenTheory.optimistic_swap_plan_def, AllCaseEqs()] >>
  metis_tac[do_swap_restore_was_spilled, planAlignTheory.stack_get_depth_bound,
    pairTheory.FST]
QED

Theorem sym_optimistic_swap_numeric:
  !dfg inst live term ps ops ps' p env cp fn ret srest initial_fmp R ss.
    optimistic_swap_plan dfg inst live term ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!b. ps'.ps_alloc.sa_spill_base <= b /\ b < ps'.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps' out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[stackPlanGenTheory.optimistic_swap_plan_def, AllCaseEqs()]
  >- (qexists `ss` >> simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def])
  >- (qexists `ss` >> simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def])
  >- (qexists `ss` >> simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def])
  >- (qexists `ss` >> simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def])
  >- (qexists `ss` >> simp[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  drule_all sym_depth_swap_numeric >> simp[]
QED

Theorem sym_popmany_optimistic_numeric:
  !items ps pop_ops mid dfg inst live term swap_ops qs p env cp fn ret srest initial_fmp R ss.
    popmany_plan items ps = (pop_ops,mid) /\
    optimistic_swap_plan dfg inst live term mid = (swap_ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!off. MEM (SOSpill off) (pop_ops ++ swap_ops) ==> off < dimword(:256)) /\
    (!b. qs.ps_alloc.sa_spill_base <= b /\ b < qs.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (pop_ops ++ swap_ops)) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp (pop_ops ++ swap_ops))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest qs out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (pop_ops ++ swap_ops)) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac popmany_layout >>
  drule allocMonoTheory.optimistic_swap_plan_spill_base >> disch_tac >>
  drule allocMonoTheory.optimistic_swap_plan_next_offset >> disch_tac >>
  irule sym_numeric_seq >> (conj_tac >- asm_rewrite_tac[]) >>
  qexistsl [`ps`, `mid`] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> irule sym_popmany_numeric >>
      metis_tac[popmany_restore_was_spilled, listTheory.MEM_APPEND,
        arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  rpt strip_tac >> irule sym_optimistic_swap_numeric >>
  metis_tac[optimistic_swap_restore_was_spilled, listTheory.MEM_APPEND]
QED

Theorem prepare_params_nonempty_decompose:
  !liveness fn ps params installed ops qs.
    params = get_params (HD fn.fn_blocks).bb_instructions /\ params <> [] /\
    FOLDL (\s inst. s with ps_stack := stack_push (Var (HD inst.inst_outputs)) s.ps_stack)
      ps params = installed /\
    prepare_params_plan liveness fn ps = (ops,qs) ==>
    ?pop_ops mid swap_ops.
      ops = pop_ops ++ swap_ops /\
      popmany_plan
        (FILTER is_var_operand
          (FILTER (\v. ~MEM (operand_to_string v)
            (live_vars_at liveness (HD fn.fn_blocks).bb_label (LENGTH params)))
            installed.ps_stack)) installed = (pop_ops,mid) /\
      optimistic_swap_plan dfg_empty (LAST params)
        (live_vars_at liveness (HD fn.fn_blocks).bb_label (LENGTH params))
        (case FIND (\inst. ~is_param_opcode inst.inst_opcode)
          (HD fn.fn_blocks).bb_instructions of
          SOME inst => is_terminator inst.inst_opcode | NONE => F)
        mid = (swap_ops,qs)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[stackPlanGenTheory.prepare_params_plan_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem sym_prepare_params_numeric:
  !ch growth spill_base lbl_ctr ps0 params installed liveness fn ops ps1
    p env cp ret srest initial_fmp R ss.
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params /\
    codegen_ready_fn fn /\
    prepare_params_plan liveness fn ps0 = (ops,ps1) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
    (!b. ps1.ps_alloc.sa_spill_base <= b /\ b < ps1.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest installed ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps1 out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryEntryParamsTheory.entry_installed_structural >> strip_tac >>
  Cases_on `params = []`
  >- (gvs[stackPlanGenTheory.prepare_params_plan_def] >> qexists `ss` >>
      gvs[planExecTheory.execute_plan_def, asmSpliceTheory.sym_steps_def,
        stackPlanGenTheory.init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def]) >>
  drule_all prepare_params_nonempty_decompose >> strip_tac >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule sym_popmany_optimistic_numeric >> simp[] >>
  (conj_tac >- gvs[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem sym_label_numeric:
  !lbl ps p env cp fn ret srest initial_fmp R ss.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOLabel lbl]) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp [SOLabel lbl])) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOLabel lbl]) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
    stackOpSimTheory.asm_block_at_cons] >>
  qexists `ss with sym_base := (asm_next ss.sym_base) with as_stack := []` >>
  pure_once_rewrite_tac[arithmeticTheory.ONE] >>
  gvs[asmSpliceTheory.sym_steps_def, asmSymSemTheory.sym_step_def, asmSymSemTheory.sym_lift_def,
    asmSemTheory.asm_step_def, asmSemTheory.asm_next_def, sym_kinds_ok_def,
    asmSymSemTheory.sym_state_component_equality]
QED

Theorem sym_label_prepare_numeric:
  !ch growth spill_base lbl_ctr ps0 params installed liveness fn ops ps1
    p env cp ret srest initial_fmp R ss lbl.
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params /\
    codegen_ready_fn fn /\
    prepare_params_plan liveness fn ps0 = (ops,ps1) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
    (!b. ps1.ps_alloc.sa_spill_base <= b /\ b < ps1.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest installed ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (SOLabel lbl :: ops)) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp (SOLabel lbl :: ops))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps1 out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (SOLabel lbl :: ops)) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `SOLabel lbl :: ops = [SOLabel lbl] ++ ops` by simp[] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  irule sym_numeric_seq >> (conj_tac >- simp[]) >>
  qexistsl [`installed`, `installed`] >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> irule sym_label_numeric >> simp[]) >>
  rpt strip_tac >> irule sym_prepare_params_numeric >> metis_tac[]
QED

Theorem sym_label_prepare_numeric_mode:
  !allow_own own ch growth spill_base lbl_ctr ps0 params installed liveness fn ops ps1
    p env cp ret srest initial_fmp R ss lbl.
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params /\
    codegen_ready_fn fn /\
    prepare_params_plan liveness fn ps0 = (ops,ps1) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
    (!b. ps1.ps_alloc.sa_spill_base <= b /\ b < ps1.ps_alloc.sa_next_offset ==>
      context_spill_byte cp b /\ R b) /\
    sym_kinds_ok cp fn ret srest installed ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (SOLabel lbl :: ops)) ==>
    ?out. sym_steps_mode allow_own p env own
        (LENGTH (execute_plan initial_fmp (SOLabel lbl :: ops))) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest ps1 out /\
      out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (SOLabel lbl :: ops)) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_label_prepare_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `out` >> simp[] >> irule sym_steps_mode_ok >> simp[]
QED
