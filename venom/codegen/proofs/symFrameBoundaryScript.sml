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
Theorem phi_input_not_code_end:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands ==>
  ~code_end_var fn x
Proof
  metis_tac[symFrameBoundaryNumericTheory.phi_input_not_code_end_own, label_flow_ok_imp_label_flow_own_ok]
QED

Theorem phi_operand_kind_transport:
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  ssa_form fn /\ retpc_shape_ok fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM x inst.inst_outputs /\ MEM (Var y) inst.inst_operands /\
  op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var x) sv
Proof
  metis_tac[symFrameBoundaryNumericTheory.phi_operand_kind_transport_own, label_flow_ok_imp_label_flow_own_ok]
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

Theorem phi_run_inst_kind:
  phi_run_context fn bb pred entry source final /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  MEM (Var y) inst.inst_operands /\ op_kind_ok fn ret (Var y) sv ==>
  op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv
Proof
  metis_tac[symFrameBoundaryNumericTheory.phi_run_inst_kind_own, label_flow_ok_imp_label_flow_own_ok]
QED

Theorem phi_run_hit_kind:
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  MEM fn ctx.ctx_functions /\ label_flow_ok ctx /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
    op_kind_ok fn ret (Var (HD inst.inst_outputs)) sv)
Proof
  metis_tac[symFrameBoundaryNumericTheory.phi_run_hit_kind_own, label_flow_ok_imp_label_flow_own_ok]
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
  drule_all symFrameBoundaryNumericTheory.sym_phi_run_step_own >> simp[]
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
  drule_all symFrameBoundaryNumericTheory.paired_phi_run_step_own >> simp[]
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
  drule_all symFrameBoundaryNumericTheory.paired_phi_run_prefix_legacy_own >> simp[]
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
  drule_all symFrameBoundaryNumericTheory.paired_phi_run_prefix_legacy_own >>
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

(* Boundary plans already have successful legacy runs.  Transport just the
   execution component, retaining their kinds, pc and memory-label facts. *)
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
