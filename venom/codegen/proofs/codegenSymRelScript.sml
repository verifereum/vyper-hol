(*
 * The symbolic twin of the codegen frame invariant: what codegen's assembly
 * holds, read in asmSymSem's symbolic semantics, where code and data
 * addresses are labels (Lab l d) rather than words.
 *
 * Every stack slot and spill slot of a frame holds a concrete word, except
 * the return-PC slots (Lab ret 0, ret the return label the caller pushed)
 * and the code_end-derived pointers (Lab "code_end" d).  Which operands are
 * which is fixed by the function: retpc_var for the first kind, and
 * code_end_var, the ADD [op; Label "code_end"] outputs and their ASSIGN
 * copies, for the second.
 *
 * TOP-LEVEL:
 *   code_end_var           - the code_end-derived variables of a function
 *   label_flow_ok          - no CODESIZE; code_end variables only copied or
 *                            CODECOPY's source, and CODECOPY reads only
 *                            runtime_begin or a code_end variable
 *   code_end_offset_ok     - a code_end ADD's offset is below 2^255
 *   sym_unit_static_ok     - the data segment holds bytes only, has
 *                            runtime_begin when the code uses it, and every
 *                            INVOKE names a function of the context
 *   op_kind_ok             - the kind of symbolic value an operand's slot
 *                            holds in a frame
 *   sym_kinds_ok           - the kinds part of the frame invariant
 *   sym_frame_inv          - fn_frame_inv's symbolic twin
 *   asm_sym_steps_lockstep - an OK symbolic run is shadowed by a related
 *                            OK concrete run
 *)

Theory codegenSymRel
Ancestors
  asmDataEnv asmSymBridge asmSplice asmSymSem asmSem frameRel contextCodegenRel codegenRel
  unitShapeDefs stackPlanTypes venomWf venomExecSemantics venomState
  venomInst allocaRemapSSA dfgAnalysisProps dfgDefs list finite_map arithmetic

(* ===== Label-flow facts of the Venom unit ===== *)

(* The variables holding a code_end-derived pointer: an ADD's output whose
   second operand is Label "code_end", and the ASSIGN copies of one.  Unlike
   retpc_var, there is no PHI case: label_flow_ok lets no PHI read one. *)
Inductive code_end_var:
[~seed:]
  (!fn inst op x.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ADD /\
    inst.inst_operands = [op; Label "code_end"] /\
    MEM x inst.inst_outputs ==> code_end_var fn x)
[~assign:]
  (!fn inst x y.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var y] /\ MEM x inst.inst_outputs /\
    code_end_var fn y ==> code_end_var fn x)
End

(* P1 and P2 of the step-5 plan.  CODESIZE is a label misuse (the symbolic
   semantics has no code size); a code_end pointer is only copied or read
   by CODECOPY as its source; and CODECOPY's source is runtime_begin or such
   a pointer. *)
Definition label_flow_ok_def:
  label_flow_ok ctx <=>
    !fn inst.
      MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> CODESIZE /\
      (!x. MEM (Var x) inst.inst_operands /\ code_end_var fn x ==>
           (inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var x]) \/
           (inst.inst_opcode = CODECOPY /\
            ?dst sz. inst.inst_operands = [dst; Var x; sz] /\
                     dst <> Var x /\ sz <> Var x)) /\
      (inst.inst_opcode = CODECOPY ==>
       ?dst src sz.
         inst.inst_operands = [dst; src; sz] /\
         (src = Label "runtime_begin" \/
          ?x. src = Var x /\ code_end_var fn x))
End

(* P3: at every invariant point of a code_end ADD, its offset is below
   2^255, so the pointer's delta is one the symbolic semantics keeps
   (sym_delta_ok). *)
Definition code_end_offset_ok_def:
  code_end_offset_ok Inv ctx <=>
    !fn inst vs op w.
      Inv ctx fn inst vs /\ inst.inst_opcode = ADD /\
      inst.inst_operands = [op; Label "code_end"] /\
      eval_operand op vs = SOME w ==>
      w2n w < dimword (:256) DIV 2
End

(* The static clauses: the data segment holds bytes only (a DataLabel would
   be a code address in the data, AsmDataLabel, which asm_static_wf rules
   out); runtime_begin is a data header when the code reads it; and INVOKE
   jumps to a function's label. *)
Definition sym_unit_static_ok_def:
  sym_unit_static_ok unit <=>
    EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                      ds.ds_items) unit.cu_data_segment /\
    ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                MEM inst (fn_insts fn) /\
                MEM (Label "runtime_begin") inst.inst_operands) ==>
     EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
    wf_invoke_targets unit.cu_context
End

(* In SSA form, a code_end variable's one definition is its seed ADD or a
   copy of another code_end variable. *)
Theorem code_end_var_def_inst:
  !fn x inst.
    ssa_form fn /\ code_end_var fn x /\ MEM inst (fn_insts fn) /\
    MEM x inst.inst_outputs ==>
    (inst.inst_opcode = ADD /\ ?op. inst.inst_operands = [op; Label "code_end"]) \/
    (inst.inst_opcode = ASSIGN /\
     ?y. inst.inst_operands = [Var y] /\ code_end_var fn y)
Proof
  rpt strip_tac >>
  qpat_x_assum `code_end_var _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [code_end_var_cases]) >>
  rename1 `MEM def (fn_insts fn)` >>
  `def = inst` by metis_tac[allocaRemapSSATheory.ssa_unique_output] >>
  gvs[]
QED

(* retpc_shape_ok's clause on what defines a return-PC variable. *)
val retpc_def_tac =
  qpat_assum `!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
                       retpc_var fn x ==> _` (fn th => drule_all th);

(* No variable is both a return-PC variable and a code_end variable. *)
Theorem code_end_var_not_retpc_var:
  !fn x. code_end_var fn x ==> retpc_shape_ok fn ==> ~retpc_var fn x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  qpat_assum `retpc_shape_ok _`
    (strip_assume_tac o REWRITE_RULE [retpc_shape_ok_def]) >>
  retpc_def_tac >> gvs[]
QED

(* ===== Symbolic kinds of operands ===== *)

(* The symbolic value sv may sit in the slot of operand op in fn's frame,
   ret being the return label the caller pushed: a word for a literal or an
   ordinary variable, Lab ret 0 for a return-PC variable, a code_end
   pointer for a code_end variable, and the label for a label.  Only the
   kind is fixed: which word, and which code_end delta, is the concrete
   state's business (asm_sym_rel).  Dead slots hold anything. *)
Definition op_kind_ok_def:
  op_kind_ok fn ret op sv <=>
    op = dead_stack_marker \/
    case op of
      Lit _ => (?w. sv = Val w)
    | Label l => sv = Lab l 0
    | Var x =>
        if retpc_var fn x then sv = Lab ret 0
        else if code_end_var fn x then (?d. sv = Lab "code_end" d)
        else (?w. sv = Val w)
End

(* The ASSIGN-chain root of an operand has the operand's kind. *)
Theorem op_kind_ok_normalize_operand:
  !dfg visited op.
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn ==>
    (op_kind_ok fn ret (normalize_operand dfg visited op) sv <=>
     op_kind_ok fn ret op sv)
Proof
  recInduct normalize_operand_ind >> rpt strip_tac >>
  simp[Once normalize_operand_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP (dfg_build_function fn).dfg_defs v` >> simp[] >>
  rename1 `FLOOKUP _ v = SOME inst` >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = op1 :: ops` >>
  Cases_on `ops` >> simp[] >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    (irule dfg_build_function_correct >> simp[dfg_get_def_def]) >>
  first_x_assum (qspecl_then [`inst`, `op1`] mp_tac) >> simp[] >>
  disch_then kall_tac >>
  `retpc_shape_ok fn /\ label_positions_ok inst` by
    gvs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  `~(code_end_var fn v /\ retpc_var fn v)` by
    metis_tac[code_end_var_not_retpc_var] >>
  qpat_x_assum `retpc_shape_ok _`
    (strip_assume_tac o REWRITE_RULE [retpc_shape_ok_def]) >>
  Cases_on `op1`
  >~ [`Label l`]
  >- gvs[label_positions_ok_def, is_label_operand_def]
  >~ [`Lit w`]
  >- (`~retpc_var fn v` by (strip_tac >> retpc_def_tac >> simp[]) >>
      `~code_end_var fn v` by
        (strip_tac >> drule_all code_end_var_def_inst >> simp[]) >>
      simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def])
  >~ [`Var y`]
  >- (`retpc_var fn v <=> retpc_var fn y` by
        (eq_tac >> strip_tac
         >- (retpc_def_tac >> simp[])
         >> simp[retpc_var_def] >>
         irule (cj 2 copy_phi_var_rules) >> gvs[retpc_var_def] >>
         metis_tac[]) >>
      `code_end_var fn v <=> code_end_var fn y` by
        (eq_tac >> strip_tac
         >- (drule_all code_end_var_def_inst >> simp[])
         >> irule (cj 2 code_end_var_rules) >> metis_tac[]) >>
      simp[op_kind_ok_def, stackPlanGenTheory.dead_stack_marker_def])
QED

(* The 32 memory bytes from off hold the symbolic value sv: a label's
   intact bytes, or no label bytes at all. *)
Definition mem_sval_at_def:
  mem_sval_at labs off (Lab l d) = (mem_label_at labs off = SOME (l, d)) /\
  mem_sval_at labs off (Val _) =
    (!i. in_mem_range off 32 i ==> i NOTIN FDOM labs)
End

(* ===== The frame invariant ===== *)

(* The kinds part of the frame invariant, which stack shuffles, spills and
   restores keep without looking at the concrete state: in fn's frame with
   planner state ps, ret the return label the caller pushed and srest the
   caller's symbolic stack below the frame, the frame stack holds values of
   its operands' kinds, each live spill slot holds a value of its operand's
   kind, and label bytes lie in spill regions only. *)
Definition sym_kinds_ok_def:
  sym_kinds_ok cp fn ret srest ps ss <=>
    (?top. ss.sym_stack = top ++ srest /\
           LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top) /\
    (!op off. FLOOKUP ps.ps_spilled op = SOME off ==>
       ?sv. op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels off sv) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b)
End

(* The symbolic state ss of program p against the concrete state cs: related
   (asm_sym_rel), of the right kinds, with the memory labels outside the
   frame's closure those at the frame's entry, labs0, and the return label
   a code label. *)
Definition sym_frame_inv_def:
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss <=>
    asm_sym_rel p env cs ss /\
    sym_kinds_ok cp fn ret srest ps ss /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p)
End

(* ===== Runs ===== *)



Theorem sym_steps_add:
  !m n ss. sym_steps p env (m + n) ss =
           case sym_steps p env m ss of
             SymOK ss' => sym_steps p env n ss'
           | r => r
Proof
  Induct >> simp[sym_steps_def, ADD_CLAUSES] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[]
QED

Theorem sym_steps_compose:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK out ==>
  sym_steps p env (m + n) ss = SymOK out
Proof
  simp[sym_steps_add]
QED

Theorem mem_sval_at_store_label:
  mem_sval_at (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, mstore_labels_lookup,
       EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem store_label_lookup_outside:
  ~in_mem_range off 32 i ==>
  FLOOKUP (labs |++ GENLIST (\j. (off+j,(l,d,j))) 32) i = FLOOKUP labs i
Proof
  simp[mstore_labels_lookup, in_mem_range_def]
QED

Theorem mem_sval_at_clear:
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FDOM_DRESTRICT, pred_setTheory.IN_APP]
QED

Theorem mem_sval_at_cong:
  !labs labs' off sv.
  (!i. in_mem_range off 32 i ==> FLOOKUP labs' i = FLOOKUP labs i) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  rpt gen_tac >> strip_tac >>
  `!i. in_mem_range off 32 i ==> (i IN FDOM labs' <=> i IN FDOM labs)` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `FLOOKUP labs' off = FLOOKUP labs off` by
    (first_x_assum irule >> simp[in_mem_range_def]) >>
  Cases_on `sv` >>
  simp[mem_sval_at_def, mem_label_at_def, listTheory.EVERY_MEM,
       rich_listTheory.MEM_COUNT_LIST] >>
  gvs[in_mem_range_def]
QED

Theorem sym_steps_single:
  asm_block_at p ss.sym_base.as_pc [inst] ==>
  sym_steps p env 1 ss = sym_step p env inst ss
Proof
  simp[asm_block_at_def, sym_steps_compute] >>
  Cases_on `sym_step p env inst ss` >>
  simp[sym_steps_compute]
QED

Theorem sym_step_dup_name:
  0 < n /\ n <= 16 ==>
  sym_step p env (AsmOp (dup_name n)) ss = sym_dup (n-1) ss
Proof
  strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  pure_rewrite_tac[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[] >> simp[planExecTheory.dup_name_def] >>
  simp[sym_step_def, sym_step_op_def, dup_table_def]
QED

Theorem sym_step_swap_name:
  0 < n /\ n <= 16 ==>
  sym_step p env (AsmOp (swap_name n)) ss = sym_swap n ss
Proof
  strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  pure_rewrite_tac[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[] >> simp[planExecTheory.swap_name_def] >>
  simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def]
QED

Theorem sym_scratch_push:
  off < dimword (:256) ==>
  sym_step p env (AsmPush (encode_num_bytes off)) ss =
  SymOK (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                   sym_stack := Val (n2w off) :: ss.sym_stack |>)
Proof
  strip_tac >>
  `word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes off)) = n2w off` by
    (mp_tac (Q.SPEC `n2w off` (GEN_ALL strongPrefixSimTheory.push_encode_roundtrip)) >> simp[]) >>
  simp[sym_step_def, stackOpAsmSimTheory.asm_step_push_ok, sym_lift_def,
       asm_next_def, sym_state_component_equality]
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

(* The memory labels after a 32-byte store of sv at off. *)
Definition scratch_store_labels_def:
  scratch_store_labels labs off (Val w) =
    mem_labels_clear labs (in_mem_range off 32) /\
  scratch_store_labels labs off (Lab l d) =
    labs |++ GENLIST (\i. (off + i, (l,d,i))) 32
End

Theorem scratch_store_labels_outside:
  ~in_mem_range off 32 b ==>
  FLOOKUP (scratch_store_labels labs off sv) b = FLOOKUP labs b
Proof
  Cases_on `sv` >> pure_rewrite_tac[scratch_store_labels_def,
    mstore_labels_lookup] >>
  simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       in_mem_range_def]
QED

Theorem scratch_store_labels_at:
  mem_sval_at (scratch_store_labels labs off sv) off sv
Proof
  Cases_on `sv` >>
  rewrite_tac[scratch_store_labels_def, mem_sval_at_clear,
              mem_sval_at_store_label]
QED

Theorem scratch_store_labels_preserves_saved:
  old + 32 <= off \/ off + 32 <= old ==>
  (mem_sval_at (scratch_store_labels labs off sv) old saved <=>
   mem_sval_at labs old saved)
Proof
  strip_tac >> irule mem_sval_at_cong >>
  rpt strip_tac >> irule scratch_store_labels_outside >>
  gvs[in_mem_range_def]
QED

Theorem mem_sval_val_no_label:
  mem_sval_at labs off (Val w) ==>
  mem_label_at labs off = NONE /\ ~mem_labels_hit labs (in_mem_range off 32)
Proof
  simp[mem_sval_at_def, mem_labels_hit_def] >> strip_tac >>
  `FLOOKUP labs off = NONE` by
    (simp[finite_mapTheory.FLOOKUP_DEF] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[mem_label_at_def] >> metis_tac[]
QED

Theorem sym_mload_scratch_word:
  !ss off w stk.
  ss.sym_stack = Val off :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) ==>
  ?ss' w'. sym_mload ss = SymOK ss' /\
    ss'.sym_stack = Val w' :: stk /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >> drule mem_sval_val_no_label >> strip_tac >>
  simp[sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, asm_op_mem_reads_def,
       asm_op_mem_writes_def, sym_lift_def,
       asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_arith_def,
       asmSemTheory.asm_step_compare_def, asmSemTheory.asm_step_bitwise_def,
       asmSemTheory.asm_step_memory_def, asmSemTheory.asm_mload_def,
       asmSemTheory.asm_next_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem sym_mstore_scratch_step:
  !ss off sv stk.
  ss.sym_stack = Val off :: sv :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    ss'.sym_mem_labels = scratch_store_labels ss.sym_mem_labels (w2n off) sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt gen_tac >> Cases_on `sv` >> strip_tac >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       sval_val_def, asm_op_arity_table_def, asmSemTheory.log_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def,
       mem_labels_hit_def, sym_lift_def, asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_arith_def,
       asmSemTheory.asm_step_compare_def, asmSemTheory.asm_step_bitwise_def,
       asmSemTheory.asm_step_memory_def,
       asmSemTheory.asm_mstore_def, asmSemTheory.asm_next_def,
       scratch_store_labels_def, Excl "GENLIST_NUMERALS"]
QED

(* A run of n steps that ends ends the run with more fuel. *)
Theorem sym_steps_terminal_run:
  !n ss fuel.
    sym_terminal (sym_steps p env n ss) ==>
    sym_run p env (n + fuel) ss = sym_steps p env n ss
Proof
  Induct >> simp[sym_steps_def, sym_terminal_def, ADD_CLAUSES] >>
  rpt gen_tac >> simp[sym_run_SUC] >>
  IF_CASES_TAC >> simp[sym_terminal_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >>
  simp[sym_terminal_def] >>
  ONCE_REWRITE_TAC [ADD_COMM] >> simp[]
QED

(* A symbolic run that stays OK is shadowed by the concrete run, step for
   step (asm_sym_step): the concrete run is OK too, and the two end related. *)
Theorem asm_sym_steps_lockstep:
  !n cs ss ss'.
    asm_static_wf p /\ asm_sym_rel p env cs ss /\
    sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
            p n cs = AsmOK cs' /\
          asm_sym_rel p env cs' ss'
Proof
  Induct >> simp[sym_steps_def, asm_steps_def] >> rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by gvs[asm_sym_rel_def] >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p` >> gvs[] >>
  `cs.as_pc < LENGTH p` by simp[] >>
  drule_all asm_sym_step >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[asm_sym_step_rel_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem LIST_REL_select_indices:
  !R xs ys indices.
    LIST_REL R xs ys /\ EVERY (\i. i < LENGTH xs) indices ==>
    LIST_REL R (MAP (\i. EL i xs) indices) (MAP (\i. EL i ys) indices)
Proof
  simp[listTheory.LIST_REL_EL_EQN, listTheory.EVERY_EL,
       listTheory.EL_MAP]
QED

Theorem sym_frame_inv_region_transfer:
  !p env ctx cp fn ret srest labs0 ps cs ss r cs' ss' ps'.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_sym_rel p env cs' ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rw[sym_frame_inv_def] >>
  `~(r.sr_spill_base <= b /\ b < r.sr_spill_end)` by
    (strip_tac >> fs[closure_spill_byte_def] >>
     metis_tac[fcgDefsTheory.fcg_path_def, relationTheory.RTC_REFL]) >>
  metis_tac[]
QED
