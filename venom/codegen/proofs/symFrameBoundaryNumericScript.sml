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
