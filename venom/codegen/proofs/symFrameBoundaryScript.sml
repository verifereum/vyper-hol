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
  dfgDefs symShuffleSim reorderStages codegenSymOwnRel symFrameBoundaryPairing symFrameBoundaryNumeric
  symFrameBoundaryOwn fnPlanPlaceRevertPostamble asmSymOwnStep

(* Symbolic kinds at the boundary depend on the defining instruction,
   not on the concrete word used to represent a label. *)
Theorem phi_input_not_code_end_own:
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_input_not_code_end_own
QED

Theorem phi_input_not_code_end:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  metis_tac[phi_input_not_code_end_own, label_flow_ok_imp_label_flow_own_ok]
QED

Theorem phi_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_output_not_code_end
QED

Theorem phi_operand_kind_transport_own:
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_operand_kind_transport_own
QED

Theorem phi_operand_kind_transport:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  metis_tac[phi_operand_kind_transport_own, label_flow_ok_imp_label_flow_own_ok]
QED

Theorem param_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  ~code_end_var fn x
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.param_output_not_code_end
QED

Theorem param_output_retpc_kind:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (retpc_var fn x <=> inst.inst_opcode = RETPC_PARAM)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.param_output_retpc_kind
QED

Theorem param_output_kind:
  ssa_form fn /\ retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] ==>
  (op_kind_ok fn ret (Var x) sv <=>
   if inst.inst_opcode = RETPC_PARAM then sv = Lab ret 0
   else ?w. sv = Val w)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.param_output_kind
QED

Theorem sym_run_same_endpoint:
  !R lo prog env cs ss n cs' out.
  (!n cs ss out.
    R cs ss /\ sym_steps prog env n ss = SymOK out ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      R cs' out) /\
  R cs ss /\
  asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
  sym_steps prog env n ss = SymOK out ==>
  R cs' out
Proof
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
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
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_frame_inv_own lo prog env cs.as_code ctx cplan fn ret srest labs0 ps cs ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all sym_frame_inv_same_count_own >> simp[sym_frame_inv_canonical_own]
QED

Theorem sym_kinds_stack_poke:
  !cp fn ret srest ps ss d op.
  sym_kinds_ok cp fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
        op_kind_ok fn ret op sv) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  metis_tac[symFrameBoundaryNumericTheory.sym_kinds_stack_poke]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_mload_mem_sval_label]
QED

Definition scratch_labels_store_def:
  scratch_labels_store labs [] = labs /\
  scratch_labels_store labs ((off,sv)::xs) =
    scratch_labels_store (scratch_store_labels labs off sv) xs
End

Theorem scratch_labels_store_fold[local]:
  !xs labs. scratch_labels_store labs xs =
    FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs
Proof
  Induct >> simp[scratch_labels_store_def] >>
  Cases_on `h` >> simp[scratch_labels_store_def]
QED

Theorem scratch_labels_store_outside:
  !xs labs b.
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs ==>
    FLOOKUP (scratch_labels_store labs xs) b = FLOOKUP labs b
Proof
  simp[scratch_labels_store_fold, scratch_fold_outside]
QED

Theorem scratch_labels_store_preserves_saved:
  !xs labs old saved.
    EVERY (\p. old + 32 <= FST p \/ FST p + 32 <= old) xs ==>
    (mem_sval_at (scratch_labels_store labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  simp[scratch_labels_store_fold, scratch_fold_preserves_saved]
QED

Theorem scratch_labels_store_saved:
  !xs labs.
    ALL_DISTINCT (MAP FST xs) /\
    (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
       FST p + 32 <= FST q \/ FST q + 32 <= FST p) ==>
    !off sv. MEM (off,sv) xs ==>
      mem_sval_at (scratch_labels_store labs xs) off sv
Proof
  simp[scratch_labels_store_fold, scratch_fold_saved]
QED

Theorem sym_steps_two:
  !p env ss i j s1 s2.
    asm_block_at p ss.sym_base.as_pc [i;j] /\
    sym_step p env i ss = SymOK s1 /\
    s1.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    sym_step p env j s1 = SymOK s2 ==>
    sym_steps p env 2 ss = SymOK s2
Proof
  metis_tac[symFrameBoundaryNumericTheory.sym_steps_two]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_push_offset_then]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_pushed_mstore]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_spill_offset_steps]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_mload_saved_kinds]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_pushed_mload]
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
  metis_tac[symFrameBoundaryNumericTheory.sym_restore_offset_steps]
QED

Theorem sym_spill_offsets_cons_result:
  !p env ss mid out off sv xs stk.
    sym_steps p env 2 ss = SymOK mid /\
    mid.sym_mem_labels = scratch_store_labels ss.sym_mem_labels off sv /\
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
  rewrite_tac[scratch_labels_store_fold] >>
  metis_tac[symFrameBoundaryNumericTheory.sym_spill_offsets_cons_result_fold]
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_spill_offsets_cons_step_fold
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
  rewrite_tac[scratch_labels_store_fold] >>
  metis_tac[symFrameBoundaryNumericTheory.sym_spill_offsets_steps_fold]
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_restore_offsets_cons_step
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_restore_offsets_steps
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.scratch_fold_restore_ready
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_spill_restore_schedule_steps_fold
QED

Theorem scratch_ranges_outside:
  !xs R b.
    (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==> R b) /\
    ~R b ==>
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.scratch_ranges_outside
QED

Theorem scratch_labels_store_separated_saved:
  !xs labs old saved.
    (!off sv. MEM (off,sv) xs ==> old + 32 <= off \/ off + 32 <= old) ==>
    (mem_sval_at (scratch_labels_store labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.scratch_fold_separated_saved
QED

Theorem scratch_labels_store_context:
  !labs cp xs.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  (!off sv b. MEM (off,sv) xs /\ in_mem_range off 32 b ==>
     context_spill_byte cp b) ==>
  !b. b IN FDOM (scratch_labels_store labs xs) ==> context_spill_byte cp b
Proof
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.scratch_fold_context
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_kinds_scratch_fold
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_do_swap_shallow
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_selected_kinds_transport
QED

Theorem MAP_ZIP_indices:
  !xs ys indices.
    LENGTH xs = LENGTH ys /\ EVERY (\i. i < LENGTH xs) indices ==>
    MAP FST (MAP (\i. EL i (ZIP (xs,ys))) indices) = MAP (\i. EL i xs) indices /\
    MAP SND (MAP (\i. EL i (ZIP (xs,ys))) indices) = MAP (\i. EL i ys) indices
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.MAP_ZIP_indices
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_spill_restore_indices_steps_fold
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
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_kinds_zip_scratch_fold
QED

Theorem scratch_labels_zip_store_outside:
  !offsets saved labs R b.
    LENGTH offsets = LENGTH saved /\
    (!off b. MEM off offsets /\ in_mem_range off 32 b ==> R b) /\ ~R b ==>
    FLOOKUP (scratch_labels_store labs (ZIP (offsets,saved))) b = FLOOKUP labs b
Proof
  rewrite_tac[scratch_labels_store_fold] >>
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.scratch_zip_fold_outside
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_scratch_indices_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_temporary_offsets_resources
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_do_swap_deep_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_do_swap_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_numeric_seq
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_swap_pop_numeric
QED

Theorem pop_one_some_alloc_mono:
  !item ps d ops ps'.
    stack_get_depth item ps.ps_stack = SOME d /\
    cleanOpsSim$pop_one_step item ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_one_some_alloc_mono
QED

Theorem pop_one_step_alloc_mono:
  !item ps ops ps'.
    cleanOpsSim$pop_one_step item ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_one_step_alloc_mono
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_steps_alloc_mono_cons
QED

Theorem pop_steps_alloc_mono:
  !items ps ops ps'.
    foldlSim$plan_steps cleanOpsSim$pop_one_step items ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_steps_alloc_mono
QED

Theorem pop_one_some_layout:
  !item d ps ops ps'.
    stack_get_depth item ps.ps_stack = SOME d /\
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_one_some_layout
QED

Theorem pop_one_step_layout:
  !item ps ops ps'.
    cleanOpsSim$pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_one_step_layout
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_pop_one_some_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_pop_one_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_pop_steps_cons_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_pop_steps_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_individual_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_contiguous_result
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_contiguous_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_poke_popmany_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_poke_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_phi_plan_hit_no_dup_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_phi_plan_no_dup_numeric
QED

Theorem phi_run_inst_kind_own:
  phi_run_context fn bb pred entry source final /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  MEM (Var y) inst.inst_operands /\ op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_run_inst_kind_own
QED

Theorem phi_run_inst_kind:
  phi_run_context fn bb pred entry source final /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM (Var y) inst.inst_operands /\ op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv
Proof
  metis_tac[phi_run_inst_kind_own, label_flow_ok_imp_label_flow_own_ok]
QED

Theorem phi_run_hit_dead:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  ~MEM (operand_to_string (stack_peek d ps.ps_stack))
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done)))
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_run_hit_dead
QED

Theorem phi_run_hit_kind_own:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
    op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_run_hit_kind_own
QED

Theorem phi_run_hit_kind:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
    op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)
Proof
  metis_tac[phi_run_hit_kind_own, label_flow_ok_imp_label_flow_own_ok]
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_phi_run_step_own
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
  rpt gen_tac >> strip_tac >>
  drule label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all sym_phi_run_step_own >> simp[]
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.paired_phi_run_step_own
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
  drule label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all paired_phi_run_step_own >> simp[]
QED

Theorem block_insts_prefix_alloc_mono:
  !j insts lv dfg cfg fn lbl halt np bl i ps ops qs.
  generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i j insts ps = SOME (ops,qs) ==>
  qs.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
  ps.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.block_insts_prefix_alloc_mono
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.paired_steps_add_preserve
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.phi_run_prefix_cons_split
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.paired_phi_run_prefix_cons_own
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.paired_phi_run_prefix_legacy_own
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
  rpt gen_tac >> strip_tac >>
  drule label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all paired_phi_run_prefix_legacy_own >> simp[]
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
  gen_tac >> disch_then kall_tac >> rpt gen_tac >> strip_tac >>
  drule_all paired_phi_run_prefix >> simp[]
QED

Theorem paired_phi_run_prefix_own:
  !allow_own own todo done base fn bb pred entry source final ra lo m ps st body block_len
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
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK out /\
    sym_kinds_ok cp fn ret srest last out /\ out.sym_base.as_pc = st'.as_pc /\
    (!b. ~R b ==> FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all paired_phi_run_prefix_legacy_own >>
  disch_then (qspecl_then [`o2pc`, `env`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> irule sym_steps_mode_ok >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_frame_inv_own lo prog env cs.as_code ctx cplan fn ret srest labs0 ps cs ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all symFrameBoundaryPhiPackagingTheory.sym_frame_inv_local_same_count_own >>
  simp[sym_frame_inv_canonical_own]
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
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `label_flow_own_ok ctx` by metis_tac[label_flow_ok_imp_label_flow_own_ok] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_frame_inv_own lo prog env cs.as_code ctx cplan fn ret srest labs0 ps cs ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_phi_run_prefix_frame_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
QED

Theorem entry_param_kind:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  MEM inst (get_params (HD fn.fn_blocks).bb_instructions) ==>
  (op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv <=>
   if inst.inst_opcode = RETPC_PARAM then sv = Lab ret 0 else ?w. sv = Val w)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.entry_param_kind
QED

Theorem entry_param_list_kinds:
  !fn params ret ws.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  params = get_params (HD fn.fn_blocks).bb_instructions /\
  LENGTH ws + (if fn_has_retpc fn then 1 else 0) = LENGTH params ==>
  LIST_REL (op_kind_ok fn ret) (MAP (\i. Var (HD i.inst_outputs)) params)
    (MAP Val ws ++ if fn_has_retpc fn then [Lab ret 0] else [])
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.entry_param_list_kinds
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.entry_installed_sym_kinds
QED

Theorem sym_kinds_relevant_fields:
  !ps' ps cp fn ret srest ss.
  ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled /\
  sym_kinds_ok cp fn ret srest ps ss ==>
  sym_kinds_ok cp fn ret srest ps' ss
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_kinds_relevant_fields
QED

Theorem op_kinds_forget_map:
  !xs ys f fn ret.
    LIST_REL (op_kind_ok fn ret) xs ys /\
    (!op. MEM op xs ==> f op = dead_stack_marker \/ f op = op) ==>
    LIST_REL (op_kind_ok fn ret) (MAP f xs) ys
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.op_kinds_forget_map
QED

Theorem sym_kinds_forget_map:
  !cp fn ret srest ps ss f.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := MAP f ps.ps_stack) ss
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_kinds_forget_map
QED

Theorem sym_kinds_forget_promised:
  !cp fn ret srest ps ss f promised.
  sym_kinds_ok cp fn ret srest ps ss /\
  (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
  sym_kinds_ok cp fn ret srest
    (ps with <|ps_stack := MAP f ps.ps_stack; ps_cleanup_promised := promised|>) ss
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_kinds_forget_promised
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_empty_forget_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_forget_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_mark_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_clean_stack_plan_numeric
QED

(* Boundary plans already have successful legacy runs.  Transport just the
   execution component, retaining their kinds, pc and memory-label facts. *)
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_clean_stack_plan_numeric_mode
QED

Theorem clean_stack_plan_frame_sim_exact:
  !ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops)
    ==>
    ?as2.
      asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameCleanStackTheory.clean_stack_plan_frame_sim_reloc >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem allocator_interval_own_spill:
  !ctx cp fn r ps b.
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    ps.ps_alloc.sa_spill_base <= b /\ b < ps.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ closure_spill_byte ctx cp fn.fn_name b
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryOwnTheory.allocator_interval_own_spill
QED

Theorem sym_clean_stack_plan_frame_sim:
  !ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0 env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops) /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?as2 ss2.
      asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled) /\
      sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) ss = SymOK ss2 /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps2 as2 ss2
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss` >>
  `sym_frame_inv_own lo prog env as.as_code ctx cplan fn ret srest labs0 ps as ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_clean_stack_plan_frame_sim_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
QED

Theorem do_swap_deep_restore_was_spilled:
  !d ps off. d > 16 /\ d < LENGTH ps.ps_stack /\
    MEM (SORestore off) (FST (do_swap d ps)) ==>
    MEM (SOSpill off) (FST (do_swap d ps))
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.do_swap_deep_restore_was_spilled
QED

Theorem do_swap_restore_was_spilled:
  !d ps off. d < LENGTH ps.ps_stack /\
    MEM (SORestore off) (FST (do_swap d ps)) ==>
    MEM (SOSpill off) (FST (do_swap d ps))
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.do_swap_restore_was_spilled
QED

Theorem pop_one_restore_was_spilled:
  !item ps ops qs off.
    cleanOpsSim$pop_one_step item ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_one_restore_was_spilled
QED

Theorem pop_steps_restore_was_spilled:
  !items ps ops qs off.
    plan_steps cleanOpsSim$pop_one_step items ps = (ops,qs) /\
    MEM (SORestore off) ops ==> MEM (SOSpill off) ops
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_steps_restore_was_spilled
QED

Theorem popmany_individual_restore_was_spilled:
  !items ps ops qs off.
    popmany_individual items ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_individual_restore_was_spilled
QED

Theorem popmany_restore_was_spilled:
  !items ps ops qs off.
    popmany_plan items ps = (ops,qs) /\ MEM (SORestore off) ops ==>
    MEM (SOSpill off) ops
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_restore_was_spilled
QED

Theorem pop_steps_layout:
  !items ps ops qs.
    plan_steps cleanOpsSim$pop_one_step items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.pop_steps_layout
QED

Theorem popmany_individual_layout:
  !items ps ops qs.
    popmany_individual items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_individual_layout
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_contiguous_layout
QED

Theorem popmany_layout:
  !items ps ops qs.
    popmany_plan items ps = (ops,qs) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.popmany_layout
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_depth_swap_numeric
QED

Theorem optimistic_swap_restore_was_spilled:
  !dfg inst live term ps ops qs off.
    optimistic_swap_plan dfg inst live term ps = (ops,qs) /\
    MEM (SORestore off) ops ==> MEM (SOSpill off) ops
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.optimistic_swap_restore_was_spilled
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_optimistic_swap_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_popmany_optimistic_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.prepare_params_nonempty_decompose
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_prepare_params_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_label_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_label_prepare_numeric
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
  MATCH_ACCEPT_TAC symFrameBoundaryNumericTheory.sym_label_prepare_numeric_mode
QED

Theorem sym_entry_prefix_asm:
  !ctx cp lo o2pc prog liveness fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs a ra rest vp env ret srest ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ liveness = liveness_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs a ra rest /\
    vp = (entry_bind_pairs
      (entry_param_pairs vs (get_params (HD fn.fn_blocks).bb_instructions)) vs
      with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) /\
    asm_block_at prog a.as_pc (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    asm_static_wf prog /\ asm_sym_rel prog env a ss /\
    ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
    ?a' ss'.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan cp.cp_initial_fmp
          (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) a = AsmOK a' /\
      a'.as_pc = a.as_pc + LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest a.as_memory ps1 vp a' /\
      sym_steps prog env
        (LENGTH (execute_plan cp.cp_initial_fmp
          (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest ss.sym_mem_labels ps1 a' ss'
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `asm_sym_rel_own lo prog env a.as_code a ss` by
    gvs[asm_sym_rel_own_canonical] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_entry_prefix_asm_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
QED

Theorem block_phi_plan_split:
  !liveness dfg cfg fn lbl halt np bl phis body ps ops last prog pc fmp r.
  generate_block_insts_plan liveness dfg cfg fn lbl halt np bl 0
    (phis ++ body) ps = SOME (ops,last) /\
  r.sr_spill_base <= last.ps_alloc.sa_spill_base /\
  last.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
    off < dimword(:256)) /\
  asm_block_at prog pc (execute_plan fmp ops) ==>
  ?pre mid post.
    ops = pre ++ post /\
    generate_block_insts_prefix liveness dfg cfg fn lbl halt np bl 0
      (LENGTH phis) (phis ++ body) ps = SOME (pre,mid) /\
    generate_block_insts_plan liveness dfg cfg fn lbl halt np bl
      (LENGTH phis) body mid = SOME (post,last) /\
    r.sr_spill_base <= mid.ps_alloc.sa_spill_base /\
    mid.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) pre /\
    asm_block_at prog pc (execute_plan fmp pre)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryOwnTheory.block_phi_plan_split
QED

Theorem phi_hits_run_context:
  !fn bb pred ps vs final dfg.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
  bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
  eval_phis vs bb.bb_instructions = OK final /\
  (!inst op. MEM inst (collect_phis bb.bb_instructions) /\
     is_var_operand op /\ MEM op inst.inst_operands /\ MEM op ps.ps_stack ==>
     resolve_phi pred inst.inst_operands = SOME op) /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
     ~(MEM op ps.ps_stack /\ ?inst.
       MEM inst (collect_phis bb.bb_instructions) /\
       resolve_phi pred inst.inst_operands = SOME op) /\
     (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
     ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) ==>
  phi_run_context fn bb pred ps vs final
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryOwnTheory.phi_hits_run_context
QED

Theorem phi_run_final_frame:
  !ctx cp lo fn ra rest mem0 ps vs st last final endpoint bb base pred k r.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  phi_run_context fn bb pred ps vs final /\
  phi_run_config fn ra lo base pred ps vs st.as_memory
    (collect_phis bb.bb_instructions) [] last endpoint /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= last.ps_alloc.sa_spill_base /\
  last.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  fn_frame_inv ctx cp lo fn ra rest mem0 last (final with vs_inst_idx := k)
    (endpoint with as_stack := endpoint.as_stack ++ rest)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryOwnTheory.phi_run_final_frame
QED

Theorem phi_frame_run_init:
  !ctx cp lo fn ra rest mem0 ps vs st base pred phis.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generated_plan_state_wf_marked base ps ==>
  ?top. st.as_stack = top ++ rest /\
    phi_run_config fn ra lo base pred ps vs st.as_memory [] phis ps
      (st with as_stack := top)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryOwnTheory.phi_frame_run_init
QED

Theorem sym_phi_prefix_hits_frame_sim_exact:
  !ctx cp lo o2pc prog liveness dfg cfg fn bb pred base ps vs as s_phi phis
   body ops ps3 r ra rest mem0 env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    (!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
      MEM op ps.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op) /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
        resolve_phi pred inst.inst_operands = SOME op) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
      (phis ++ body) ps = SOME (ops,ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (LENGTH phis) (phis ++ body) ps = SOME (phi_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (LENGTH phis) body ps1 = SOME (body_ops,ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        operand_val (frame_view fn ra s_phi) lo at =
        operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp phi_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `label_flow_own_ok ctx` by metis_tac[label_flow_ok_imp_label_flow_own_ok] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss` >>
  `sym_frame_inv_own lo prog env as.as_code ctx cplan fn ret srest labs0 ps as ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_phi_prefix_hits_frame_sim_exact_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
QED

Theorem sym_phi_prefix_hits_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg fn bb pred base ps vs as s_phi phis
   body ops ps3 r ra rest mem0 env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    (!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
      MEM op ps.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op) /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
        resolve_phi pred inst.inst_operands = SOME op) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
      (phis ++ body) ps = SOME (ops,ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (LENGTH phis) (phis ++ body) ps = SOME (phi_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (LENGTH phis) body ps1 = SOME (body_ops,ps3) /\
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
  rpt gen_tac >> strip_tac >>
  drule_all sym_phi_prefix_hits_frame_sim_exact >>
  strip_tac >> qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_phi_prefix_frame_sim_exact:
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
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp phi_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `label_flow_own_ok ctx` by metis_tac[label_flow_ok_imp_label_flow_own_ok] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss` >>
  `sym_frame_inv_own lo prog env as.as_code ctx cplan fn ret srest labs0 ps as ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_phi_prefix_frame_sim_exact_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  drule_all sym_phi_prefix_frame_sim_exact >>
  strip_tac >> qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_single_pred_prefix_frame_sim_exact:
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
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops))
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `label_flow_own_ok ctx` by metis_tac[label_flow_ok_imp_label_flow_own_ok] >>
  rename1 `sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss` >>
  `sym_frame_inv_own lo prog env as.as_code ctx cplan fn ret srest labs0 ps as ss` by
    gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_single_pred_prefix_frame_sim_exact_own) >>
  strip_tac >> gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  drule_all sym_single_pred_prefix_frame_sim_exact >>
  strip_tac >> qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
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
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by gvs[code_labels_agree_refl] >>
  `label_flow_own_ok ctx` by metis_tac[label_flow_ok_imp_label_flow_own_ok] >>
  `asm_sym_rel_own lo prog env as.as_code as ss` by
    gvs[asm_sym_rel_own_canonical] >>
  drule_all (Q.SPEC `F` symFrameBoundaryOwnTheory.sym_entry_prefix_frame_sim_own) >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qexistsl [`n`, `as'`, `vs_p`, `ss'`] >>
  gvs[sym_steps_mode_def, sym_frame_inv_canonical_own] >> metis_tac[]
QED
