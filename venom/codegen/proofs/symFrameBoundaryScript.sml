(*
 * Block-boundary pieces of the label-discipline proof on the symbolic
 * machine: a block's PHI prefix (after a cleanup when the block has one
 * predecessor) and a function's parameter prologue.  Each
 * is codegen's own lemma with the symbolic premises and conclusions added,
 * over the same n steps.  The prologue starts from the entry symbolic
 * state of sym_fn_sim_at and establishes the symbolic frame invariant,
 * with the memory labels at entry as the frame's labs0.
 *
 * TOP-LEVEL:
 *   sym_phi_prefix_frame_sim          - a join block's PHI prefix
 *   sym_single_pred_prefix_frame_sim  - a one-predecessor block's cleanup
 *                                       and PHI prefix
 *   sym_entry_prefix_frame_sim        - a function's parameter prologue
 *)
Theory symFrameBoundary
Ancestors
  codegenSymRel fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs

(* Symbolic kinds at the boundary depend on the defining instruction,
   not on the concrete word used to represent a label. *)
Theorem phi_input_not_code_end:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  rw[label_flow_ok_def] >>
  first_x_assum drule_all >> simp[] >> metis_tac[]
QED

Theorem phi_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem phi_retpc_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs /\
  MEM (Var y) inst.inst_operands ==>
  (retpc_var fn x <=> retpc_var fn y)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      drule (cj 3 (iffLR retpc_shape_ok_def)) >>
      disch_then drule_all >> simp[] >> metis_tac[]) >>
  simp[retpc_var_def] >> strip_tac >>
  irule (cj 3 copy_phi_var_rules) >> metis_tac[]
QED

Theorem phi_operand_kind_transport:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  strip_tac >>
  drule_all phi_input_not_code_end >> strip_tac >>
  drule_all phi_output_not_code_end >> strip_tac >>
  drule_all phi_retpc_kind >> strip_tac >>
  gvs[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def]
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

Theorem sym_frame_inv_same_count:
  !lo o2pc prog env ctx cp fn ret srest labs0 ps cs ss n cs' ss' ps'.
  lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  asm_steps lo o2pc prog n cs = AsmOK cs' /\
  sym_steps prog env n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
     FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rw[sym_frame_inv_def] >>
  drule_all asm_sym_steps_lockstep >> strip_tac >> gvs[]
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

(* Scratch memory is indexed by byte offset, not by operand identity. *)
Theorem mem_sval_at_store_label:
  !labs off l d.
  mem_sval_at (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, mstore_labels_lookup,
       listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
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

Theorem mem_sval_at_cong:
  !labs labs' off sv.
  (!i. in_mem_range off 32 i ==> FLOOKUP labs' i = FLOOKUP labs i) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  rpt gen_tac >> simp[in_mem_range_def] >> strip_tac >> Cases_on `sv`
  >- (simp[mem_sval_at_def, in_mem_range_def] >>
      metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  simp[mem_sval_at_def, mem_label_at_def,
       listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem mem_sval_at_clear_value:
  !labs off w.
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FDOM_DRESTRICT, pred_setTheory.IN_INTER]
QED

Theorem mem_sval_value_no_label:
  !labs off w. mem_sval_at labs off (Val w) ==>
    mem_label_at labs off = NONE /\
    ~mem_labels_hit labs (in_mem_range off 32)
Proof
  rw[mem_sval_at_def, mem_labels_hit_def] >>
  `FLOOKUP labs off = NONE` by
    (simp[finite_mapTheory.FLOOKUP_DEF] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[mem_label_at_def] >> metis_tac[]
QED

Theorem sym_mload_mem_sval_value:
  !ss off w stk.
  ss.sym_stack = Val off :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) ==>
  ?ss' w'. sym_mload ss = SymOK ss' /\
    ss'.sym_stack = Val w' :: stk /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >> drule mem_sval_value_no_label >> strip_tac >>
  simp[sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, asm_op_mem_reads_def,
       asm_op_mem_writes_def, sym_lift_def,
       asmOpSimTheory.asm_step_op_mload, asmSemTheory.asm_mload_def,
       asmSemTheory.asm_next_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV]
QED

Definition scratch_labels_write_def:
  scratch_labels_write labs off (Val w) =
    mem_labels_clear labs (in_mem_range off 32) /\
  scratch_labels_write labs off (Lab l d) =
    labs |++ GENLIST (\i. (off+i,(l,d,i))) 32
End

Theorem sym_mstore_scratch_write:
  !ss off sv stk.
  ss.sym_stack = Val off :: sv :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    ss'.sym_mem_labels = scratch_labels_write ss.sym_mem_labels (w2n off) sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt gen_tac >> Cases_on `sv` >> strip_tac >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       sval_val_def, asm_op_arity_table_def, asmSemTheory.log_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def,
       mem_labels_hit_def, sym_lift_def, asmOpSimTheory.asm_step_op_mstore,
       asmSemTheory.asm_mstore_def, asmSemTheory.asm_next_def,
       scratch_labels_write_def, Excl "GENLIST_NUMERALS"]
QED

Theorem scratch_labels_write_saved:
  !labs off sv. mem_sval_at (scratch_labels_write labs off sv) off sv
Proof
  Cases_on `sv` >>
  rewrite_tac[scratch_labels_write_def, mem_sval_at_clear_value,
       mem_sval_at_store_label]
QED

Theorem scratch_labels_write_outside:
  !labs off sv i. ~in_mem_range off 32 i ==>
    FLOOKUP (scratch_labels_write labs off sv) i = FLOOKUP labs i
Proof
  Cases_on `sv` >>
  rewrite_tac[scratch_labels_write_def, mem_labels_clear_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, mstore_labels_lookup] >>
  simp[in_mem_range_def]
QED

Theorem scratch_labels_write_preserves_saved:
  !labs off sv old saved.
    old + 32 <= off \/ off + 32 <= old ==>
    (mem_sval_at (scratch_labels_write labs off sv) old saved <=>
     mem_sval_at labs old saved)
Proof
  rpt strip_tac >> irule mem_sval_at_cong >>
  rpt strip_tac >> irule scratch_labels_write_outside >>
  gvs[in_mem_range_def]
QED

Definition scratch_labels_store_def:
  scratch_labels_store labs [] = labs /\
  scratch_labels_store labs ((off,sv)::xs) =
    scratch_labels_store (scratch_labels_write labs off sv) xs
End

Theorem scratch_labels_store_outside:
  !xs labs b.
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs ==>
    FLOOKUP (scratch_labels_store labs xs) b = FLOOKUP labs b
Proof
  Induct >> simp[scratch_labels_store_def] >>
  Cases_on `h` >> simp[scratch_labels_store_def] >>
  metis_tac[scratch_labels_write_outside]
QED

Theorem scratch_labels_store_preserves_saved:
  !xs labs old saved.
    EVERY (\p. old + 32 <= FST p \/ FST p + 32 <= old) xs ==>
    (mem_sval_at (scratch_labels_store labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  Induct >> simp[scratch_labels_store_def] >>
  Cases_on `h` >> simp[scratch_labels_store_def] >>
  metis_tac[scratch_labels_write_preserves_saved]
QED

Theorem scratch_labels_store_saved:
  !xs labs.
    ALL_DISTINCT (MAP FST xs) /\
    (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
       FST p + 32 <= FST q \/ FST q + 32 <= FST p) ==>
    !off sv. MEM (off,sv) xs ==>
      mem_sval_at (scratch_labels_store labs xs) off sv
Proof
  Induct >> simp[scratch_labels_store_def] >>
  gen_tac >> PairCases_on `h` >> rw[scratch_labels_store_def]
  >- (gvs[] >> rename1 `~MEM off (MAP FST xs)` >>
      `EVERY (\p. off + 32 <= FST p \/ FST p + 32 <= off) xs` by
        (simp[listTheory.EVERY_MEM] >>
         metis_tac[listTheory.MEM_MAP, pairTheory.FST]) >>
      metis_tac[scratch_labels_store_preserves_saved, scratch_labels_write_saved]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem sym_mstore_label_scratch:
  !ss off l d stk.
  ss.sym_stack = Val off :: Lab l d :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Lab l d) /\
    (!i. ~in_mem_range (w2n off) 32 i ==>
      FLOOKUP ss'.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i)
Proof
  metis_tac[sym_mstore_scratch_write, scratch_labels_write_saved,
            scratch_labels_write_outside]
QED

Theorem sym_mstore_value_scratch:
  !ss off w stk.
  ss.sym_stack = Val off :: Val w :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Val w) /\
    (!i. ~in_mem_range (w2n off) 32 i ==>
      FLOOKUP ss'.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i)
Proof
  metis_tac[sym_mstore_scratch_write, scratch_labels_write_saved,
            scratch_labels_write_outside]
QED

Theorem sym_step_push_bytes:
  !p env bytes ss.
    sym_step p env (AsmPush bytes) ss = SymOK
      (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
         sym_stack := Val (word_of_bytes F (0w:bytes32) (REVERSE bytes)) ::
                      ss.sym_stack |> )
Proof
  simp[sym_step_def, asmSemTheory.asm_step_def, sym_lift_def,
       asmSemTheory.asm_next_def, asmSymSemTheory.FORALL_sym_state]
QED

Theorem sym_step_push_offset:
  !p env off ss.
    off < dimword(:256) ==>
    sym_step p env (AsmPush (encode_num_bytes off)) ss = SymOK
      (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                  sym_stack := Val (n2w off) :: ss.sym_stack |> )
Proof
  rpt strip_tac >>
  qspec_then `(n2w off:bytes32)` mp_tac (GEN_ALL strongPrefixSimTheory.push_encode_roundtrip) >>
  simp[sym_step_push_bytes]
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
  simp[sym_steps_compute]
QED

Theorem sym_spill_offset_steps:
  !p env ss off sv stk.
    off < dimword(:256) /\ ss.sym_stack = sv :: stk /\
    asm_block_at p ss.sym_base.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ==>
    ?ss'. sym_steps p env 2 ss = SymOK ss' /\
      ss'.sym_stack = stk /\
      ss'.sym_mem_labels = scratch_labels_write ss.sym_mem_labels off sv /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `scratch_labels_write labs off sv` >>
  qabbrev_tac `pushed = ss with <|
    sym_base := asm_next (ss.sym_base with as_stack := []);
    sym_stack := Val (n2w off) :: ss.sym_stack |>` >>
  `?out. sym_mstore pushed = SymOK out /\ out.sym_stack = stk /\
    out.sym_mem_labels = scratch_labels_write labs off sv /\
    out.sym_base.as_pc = ss.sym_base.as_pc + 2` by
    (mp_tac sym_mstore_scratch_write >>
     disch_then (qspec_then `pushed` mp_tac) >>
     simp[Abbr `pushed`, Abbr `labs`, asmSemTheory.asm_next_def]) >>
  `sym_step p env (AsmPush (encode_num_bytes off)) ss = SymOK pushed` by
    simp[Abbr `pushed`, sym_step_push_offset] >>
  `sym_step p env (AsmOp "MSTORE") pushed = SymOK out` by
    simp[sym_step_def, sym_step_op_def] >>
  `pushed.sym_base.as_pc = ss.sym_base.as_pc + 1` by
    simp[Abbr `pushed`, asmSemTheory.asm_next_def] >>
  metis_tac[sym_steps_two]
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
  >- (drule_all sym_mload_mem_sval_value >> strip_tac >> gvs[op_kind_ok_def]) >>
  drule_all sym_mload_mem_sval_label >> disch_then SUBST1_TAC >>
  simp[asmSemTheory.asm_next_def]
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
  qabbrev_tac `pushed = ss with <|
    sym_base := asm_next (ss.sym_base with as_stack := []);
    sym_stack := Val (n2w off) :: ss.sym_stack |>` >>
  `?out sv'. sym_mload pushed = SymOK out /\
    out.sym_stack = sv' :: ss.sym_stack /\
    (!fn ret op. op_kind_ok fn ret op sv ==> op_kind_ok fn ret op sv') /\
    out.sym_mem_labels = ss.sym_mem_labels /\
    out.sym_base.as_pc = ss.sym_base.as_pc + 2` by
    (mp_tac sym_mload_saved_kinds >>
     disch_then (qspec_then `pushed` mp_tac) >>
     simp[Abbr `pushed`, asmSemTheory.asm_next_def]) >>
  `sym_step p env (AsmPush (encode_num_bytes off)) ss = SymOK pushed` by
    simp[Abbr `pushed`, sym_step_push_offset] >>
  `sym_step p env (AsmOp "MLOAD") pushed = SymOK out` by
    simp[sym_step_def, sym_step_op_def] >>
  `pushed.sym_base.as_pc = ss.sym_base.as_pc + 1` by
    simp[Abbr `pushed`, asmSemTheory.asm_next_def] >>
  metis_tac[sym_steps_two]
QED

Theorem sym_spill_offsets_steps:
  !xs p env ss stk initial_fmp.
    EVERY (\p. FST p < dimword(:256)) xs /\
    ss.sym_stack = MAP SND xs ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SOSpill (MAP FST xs))) ==>
    ?out. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels xs /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs
Proof
  Induct >- simp[sym_steps_def, scratch_labels_store_def] >>
  gen_tac >> PairCases_on `h` >>
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
  `sym_steps p env (2 + 2 * LENGTH xs) ss = SymOK out` by
    (qspec_then `2` (qspec_then `2 * LENGTH xs` mp_tac) sym_steps_add >>
     disch_then (qspec_then `ss` mp_tac) >> simp[]) >>
  qexists_tac `out` >> gvs[scratch_labels_store_def, arithmeticTheory.MULT_CLAUSES]
QED

Theorem sym_phi_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_single_pred_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_entry_prefix_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv
   env ret srest ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    (* ----- The symbolic side: the entry symbolic state of sym_fn_sim_at *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    asm_sym_rel prog env as ss /\
    ss.sym_stack =
      (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b)
    ==>
    ?n as' vs_p ss'.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\
      vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest ss.sym_mem_labels ps1 as' ss'
Proof
  cheat
QED
