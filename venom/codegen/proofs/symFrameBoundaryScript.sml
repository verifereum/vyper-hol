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
  dfgDefs symShuffleSim

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
  metis_tac[sym_steps_two, sym_step_push_offset]
QED

Theorem sym_pushed_mstore:
  !p env ss off sv stk pushed.
    off < dimword(:256) /\ ss.sym_stack = sv :: stk /\
    pushed = ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack |> ==>
    ?out. sym_step p env (AsmOp "MSTORE") pushed = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = scratch_labels_write ss.sym_mem_labels off sv /\
      out.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  rpt strip_tac >>
  qspec_then `pushed` mp_tac sym_mstore_scratch_write >>
  gvs[sym_step_def, sym_step_op_def, asmSemTheory.asm_next_def]
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
  >- (drule_all sym_mload_mem_sval_value >> strip_tac >> gvs[op_kind_ok_def]) >>
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
  rpt strip_tac >> metis_tac[sym_pushed_mload, sym_push_offset_then]
QED

Theorem sym_steps_ok_append:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK out ==>
  sym_steps p env (m + n) ss = SymOK out
Proof
  simp[sym_steps_add]
QED

Theorem sym_spill_offsets_cons_result:
  !p env ss mid out off sv xs stk.
    sym_steps p env 2 ss = SymOK mid /\
    mid.sym_mem_labels = scratch_labels_write ss.sym_mem_labels off sv /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    sym_steps p env (2 * LENGTH xs) mid = SymOK out /\
    out.sym_stack = stk /\
    out.sym_mem_labels = scratch_labels_store mid.sym_mem_labels xs /\
    out.sym_base.as_pc = mid.sym_base.as_pc + 2 * LENGTH xs ==>
    ?result. sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK result /\
      result.sym_stack = stk /\
      result.sym_mem_labels = scratch_labels_store ss.sym_mem_labels ((off,sv)::xs) /\
      result.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH ((off,sv)::xs)
Proof
  rpt strip_tac >> drule_all sym_steps_ok_append >>
  gvs[scratch_labels_store_def, arithmeticTheory.MULT_CLAUSES]
QED

Theorem sym_spill_offsets_cons_step:
  !xs.
    (!p env ss stk initial_fmp.
      EVERY (\p. FST p < dimword(:256)) xs /\
      ss.sym_stack = MAP SND xs ++ stk /\
      asm_block_at p ss.sym_base.as_pc
        (execute_plan initial_fmp (MAP SOSpill (MAP FST xs))) ==>
      ?out. sym_steps p env (2 * LENGTH xs) ss = SymOK out /\
        out.sym_stack = stk /\
        out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels xs /\
        out.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH xs) ==>
    !off sv p env ss stk initial_fmp.
    EVERY (\p. FST p < dimword(:256)) ((off,sv)::xs) /\
    ss.sym_stack = MAP SND ((off,sv)::xs) ++ stk /\
    asm_block_at p ss.sym_base.as_pc
      (execute_plan initial_fmp (MAP SOSpill (MAP FST ((off,sv)::xs)))) ==>
    ?out. sym_steps p env (2 * LENGTH ((off,sv)::xs)) ss = SymOK out /\
      out.sym_stack = stk /\
      out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels ((off,sv)::xs) /\
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
  drule_all sym_spill_offsets_cons_result >> simp[]
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
  Cases >> drule sym_spill_offsets_cons_step >> metis_tac[]
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
  rpt strip_tac >> drule_all sym_steps_ok_append >>
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
  Induct >- simp[sym_steps_def] >>
  Cases >> drule sym_restore_offsets_cons_step >> metis_tac[]
QED

Theorem scratch_labels_store_restore_ready:
  EVERY (\p. FST p < dimword(:256)) xs /\
  ALL_DISTINCT (MAP FST xs) /\
  (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
     FST p + 32 <= FST q \/ FST q + 32 <= FST p) /\
  EVERY (\p. MEM p xs) ys ==>
  EVERY (\p. FST p < dimword(:256) /\
    mem_sval_at (scratch_labels_store labs xs) (FST p) (SND p)) ys
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  metis_tac[scratch_labels_store_saved, pairTheory.PAIR]
QED

Theorem sym_spill_restore_schedule_steps:
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
      out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels xs /\
      out.sym_base.as_pc = ss.sym_base.as_pc + (2 * LENGTH xs + 2 * LENGTH ys)
Proof
  rpt gen_tac >>
  rewrite_tac[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  strip_tac >> drule_all sym_spill_offsets_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  rename1 `sym_steps p env (2 * LENGTH xs) ss = SymOK mid` >>
  `EVERY (\p. FST p < dimword(:256) /\
    mem_sval_at mid.sym_mem_labels (FST p) (SND p)) ys` by
    (gvs[] >> irule scratch_labels_store_restore_ready >> metis_tac[]) >>
  `asm_block_at p mid.sym_base.as_pc
    (execute_plan initial_fmp (MAP SORestore (MAP FST ys)))` by
    gvs[doSwapSimTheory.execute_plan_map_spill_length] >>
  drule_all sym_restore_offsets_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexistsl_tac [`out`, `vals`] >>
  drule_all sym_steps_ok_append >> simp[]
QED

Theorem scratch_ranges_outside:
  !xs R b.
    (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==> R b) /\
    ~R b ==>
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[pairTheory.PAIR]
QED

Theorem scratch_labels_store_separated_saved:
  !xs labs old saved.
    (!off sv. MEM (off,sv) xs ==> old + 32 <= off \/ off + 32 <= old) ==>
    (mem_sval_at (scratch_labels_store labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  rpt strip_tac >> irule scratch_labels_store_preserves_saved >>
  gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> gvs[]
QED

Theorem scratch_labels_store_context:
  !labs cp xs.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==>
     context_spill_byte cp b) ==>
  !b. b IN FDOM (scratch_labels_store labs xs) ==> context_spill_byte cp b
Proof
  simp[GSYM finite_mapTheory.FLOOKUP_DEF, finite_mapTheory.TO_FLOOKUP] >>
  metis_tac[scratch_ranges_outside, scratch_labels_store_outside]
QED

Theorem sym_kinds_scratch_store:
  !cp fn ret srest ps ss xs out top stack.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op old off sv. FLOOKUP ps.ps_spilled op = SOME old /\ MEM (off,sv) xs ==>
    old + 32 <= off \/ off + 32 <= old) /\
  (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==>
     context_spill_byte cp b) /\
  out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels xs /\
  out.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE stack) top ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := stack) out
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac
  >- metis_tac[scratch_labels_store_separated_saved] >>
  metis_tac[scratch_labels_store_context]
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

Theorem sym_pop_numeric:
  !n ps p env cp fn ret srest initial_fmp lo R ss.
    n <= LENGTH ps.ps_stack /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOPop n]) ==>
    ?out. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPop n])) ss = SymOK out /\
      sym_kinds_ok cp fn ret srest
        (ps with ps_stack := stack_pop n ps.ps_stack) out /\
      out.sym_base.as_pc = ss.sym_base.as_pc +
        LENGTH (execute_plan initial_fmp [SOPop n]) /\
      (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >>
  `ps with ps_stack := stack_pop n ps.ps_stack =
     apply_prefix_ops initial_fmp lo [SOPop n] ps` by
    simp[mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      stackModelTheory.stack_pop_def] >>
  pop_assum SUBST1_TAC >> irule sym_prefix_ops_sim >>
  simp[prefixExecTheory.prefix_wf_def, prefixExecTheory.stack_op_wf_def,
    mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def,
    prefixSimTheory.is_prefix_op_def]
QED

Theorem LIST_REL_select_indices:
  !R xs ys indices.
    LIST_REL R xs ys /\ EVERY (\i. i < LENGTH xs) indices ==>
    LIST_REL R (MAP (\i. EL i xs) indices) (MAP (\i. EL i ys) indices)
Proof
  simp[listTheory.LIST_REL_EL_EQN, listTheory.EVERY_EL,
       listTheory.EL_MAP]
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

Theorem sym_spill_restore_indices_steps:
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
      out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels (ZIP (offsets,saved)) /\
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
    out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_base.as_pc = ss.sym_base.as_pc +
      (2 * LENGTH (ZIP (offsets,saved)) +
      2 * LENGTH (MAP (\i. EL i (ZIP (offsets,saved))) indices))` by
    (irule sym_spill_restore_schedule_steps >>
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

Theorem sym_kinds_zip_scratch_store:
  !cp fn ret srest ps ps' ss out offsets saved top.
    LENGTH offsets = LENGTH saved /\
    sym_kinds_ok cp fn ret srest ps ss /\
    (!op old off. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offsets ==>
      old + 32 <= off \/ off + 32 <= old) /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==> context_spill_byte cp b) /\
    ps'.ps_spilled = ps.ps_spilled /\
    out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_stack = top ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top ==>
    sym_kinds_ok cp fn ret srest ps' out
Proof
  rpt strip_tac >> rename1 `sym_kinds_ok cp0 fn ret srest ps' out` >>
  `sym_kinds_ok cp0 fn ret srest (ps with ps_stack := ps'.ps_stack) out` by
    (irule sym_kinds_scratch_store >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`ss`, `ZIP (offsets,saved)`] >> simp[] >>
     rpt strip_tac >> imp_res_tac listTheory.MEM_ZIP_MEM_MAP >>
     gvs[] >> metis_tac[]) >>
  gvs[sym_kinds_ok_def]
QED

Theorem scratch_labels_zip_store_outside:
  !offsets saved labs R b.
    LENGTH offsets = LENGTH saved /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==> R b) /\ ~R b ==>
    FLOOKUP (scratch_labels_store labs (ZIP (offsets,saved))) b = FLOOKUP labs b
Proof
  rpt strip_tac >> irule scratch_labels_store_outside >>
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
    out.sym_mem_labels = scratch_labels_store ss.sym_mem_labels (ZIP (offsets,saved)) /\
    out.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp
      (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) indices)))` by
    (irule sym_spill_restore_indices_steps >> gvs[]) >>
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
  >- (drule_all sym_kinds_zip_scratch_store >> simp[]) >>
  rpt strip_tac >> simp[] >>
  irule scratch_labels_zip_store_outside >> metis_tac[]
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
  qexists `t'` >> simp[] >> metis_tac[sym_steps_ok_append, arithmeticTheory.ADD_ASSOC]
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
  rpt strip_tac >> irule sym_pop_numeric >> simp[planWfTheory.do_swap_length]
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
  drule reorderSimTheory.plan_steps_cons_result >> strip_tac >>
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
      simp[planExecTheory.execute_plan_def, sym_steps_def]) >>
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
  drule reorderSimTheory.plan_steps_cons_result >> strip_tac >> gvs[] >>
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
      simp[planExecTheory.execute_plan_def, sym_steps_def]) >>
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
      simp[planExecTheory.execute_plan_def, sym_steps_def]) >>
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
    planExecTheory.exec_stack_op_def, sym_steps_def]
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
      gvs[planExecTheory.execute_plan_def, sym_steps_def]) >>
  irule sym_phi_plan_hit_no_dup_numeric >> metis_tac[]
QED

Theorem phi_run_inst_kind:
  phi_run_context fn bb pred entry source final /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM (Var y) inst.inst_operands /\ op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv
Proof
  rewrite_tac[fnFrameStepsPhiTheory.phi_run_context_def] >> strip_tac >>
  drule_all fnPlanPrefixTheory.phi_codegen_inst_shape >> strip_tac >>
  `MEM (HD inst.inst_outputs) inst.inst_outputs` by
    (Cases_on `inst.inst_outputs` >> gvs[]) >>
  irule phi_operand_kind_transport >>
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

Theorem phi_run_hit_kind:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
    op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)
Proof
  strip_tac >> drule fnFrameStepsPhiTheory.phi_stack_hit_operand >> strip_tac >>
  Cases_on `stack_peek d ps.ps_stack` >> gvs[is_var_operand_def] >>
  metis_tac[phi_run_inst_kind, listTheory.MEM_APPEND, listTheory.MEM]
QED

Theorem sym_phi_run_step:
  !fn bb pred entry source final done inst todo ps halt ops next
    prog initial_fmp cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
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
  metis_tac[phi_run_hit_dead, phi_run_hit_kind,
    genBlockSimTheory.stack_get_phi_depth_var_not_marker]
QED

Theorem paired_phi_run_step:
  !base fn bb pred entry source final done inst todo ra lo m ps st halt ops next
    prog initial_fmp o2pc cp ctx ret srest R env ss.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  phi_run_config fn ra lo base pred entry source m done (inst::todo) ps st /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
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
  drule_all sym_phi_run_step >>
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

Theorem paired_phi_run_prefix_cons:
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
    MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
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
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
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
  drule_all paired_phi_run_step >>
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

Theorem paired_phi_run_prefix:
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
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
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
    simp[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  drule paired_phi_run_prefix_cons >> simp[]
QED

Theorem sym_frame_inv_local_same_count:
  !lo o2pc prog env ctx cp fn ret srest labs0 ps cs ss top rest n endpoint out last.
  lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  cs.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (cs with as_stack := top) = AsmOK endpoint /\
  sym_steps prog env n ss = SymOK out /\
  sym_kinds_ok cp fn ret srest last out /\
  (!b. ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  asm_steps lo o2pc prog n cs =
    AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 last
    (endpoint with as_stack := endpoint.as_stack ++ rest) out
Proof
  rpt gen_tac >> strip_tac >> drule asmFrameTheory.asm_steps_frame >>
  disch_then (qspec_then `rest` mp_tac) >>
  `cs with as_stack := top ++ rest = cs` by
    simp[asmSemTheory.asm_state_component_equality] >>
  simp[] >> strip_tac >> metis_tac[sym_frame_inv_same_count]
QED

Theorem sym_phi_run_prefix_frame:
  !todo done base fn bb pred entry source final ra lo m ps cs top rest body
    block_len dfg cfg halt ops last prog o2pc cp ctx ret srest env ss labs0.
  lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ todo /\
  phi_run_config fn ra lo base pred entry source m done todo ps
    (cs with as_stack := top) /\
  cs.as_stack = top ++ rest /\
  block_len = LENGTH done + LENGTH (todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH todo) (todo ++ body) ps = SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ closure_spill_byte ctx cp fn.fn_name b) /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
  ?endpoint out.
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs =
      AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
    endpoint.as_pc = cs.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last endpoint /\
    sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK out /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 last
      (endpoint with as_stack := endpoint.as_stack ++ rest) out
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = cs.as_pc` by
    gvs[sym_frame_inv_def, asmSymBridgeTheory.asm_sym_rel_def] >>
  `asm_block_at prog (cs with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp ops)` by simp[] >>
  `ss.sym_base.as_pc = (cs with as_stack := top).as_pc` by simp[] >>
  drule_all paired_phi_run_prefix >>
  disch_then (qspecl_then [`o2pc`, `env`] strip_assume_tac) >>
  drule_all sym_frame_inv_local_same_count >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
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
