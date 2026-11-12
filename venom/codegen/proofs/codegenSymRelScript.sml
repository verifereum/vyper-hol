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
 *   sym_steps              - n symbolic steps, as asm_steps
 *   sym_run_terminal_never_bad - a symbolic run that ends never misuses a
 *                            label, at any fuel
 *   asm_sym_steps_lockstep - an OK symbolic run is shadowed by a related
 *                            OK concrete run
 *)

Theory codegenSymRel
Ancestors
  asmDataEnv asmSymBridge asmSymSem asmSem frameRel contextCodegenRel codegenRel
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

(* n symbolic steps, as asm_steps: the state they reach, or the result
   that stopped them. *)
Definition sym_steps_def:
  sym_steps p env 0 ss = SymOK ss /\
  sym_steps p env (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else
      case sym_step p env (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_steps p env n ss'
      | r => r
End


Theorem sym_run_zero[local]:
  sym_run p env 0 ss = SymError "out of fuel"
Proof
  simp[Once sym_run_def]
QED

Theorem sym_run_SUC_step[local]:
  sym_run p env (SUC fuel) ss =
  if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
  else
    case sym_step p env (EL ss.sym_base.as_pc p) ss of
      SymOK ss' => sym_run p env fuel ss'
    | r => r
Proof
  simp[Once sym_run_def]
QED

(* The symbolic run is deterministic, and fuel only cuts it short with an
   error: so one that ends never misuses a label, at any fuel. *)
Theorem sym_run_terminal_never_bad:
  !fuel0 ss. sym_terminal (sym_run p env fuel0 ss) ==>
             !fuel msg. sym_run p env fuel ss <> SymBad msg
Proof
  Induct
  >- simp[sym_run_zero, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >> Cases
  >- simp[sym_run_zero] >>
  gvs[sym_run_SUC_step] >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p` >> gvs[sym_terminal_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >>
  gvs[sym_terminal_def] >> first_x_assum drule >> simp[]
QED

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

(* A run of n steps to ss' continues as the run from ss'. *)
Theorem sym_steps_run:
  !n ss ss' fuel.
    sym_steps p env n ss = SymOK ss' ==>
    sym_run p env (n + fuel) ss = sym_run p env fuel ss'
Proof
  Induct >> simp[sym_steps_def, ADD_CLAUSES] >> rpt gen_tac >>
  simp[sym_run_SUC_step] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[] >>
  ONCE_REWRITE_TAC [ADD_COMM] >> simp[]
QED

(* A run of n steps that ends ends the run with more fuel. *)
Theorem sym_steps_terminal_run:
  !n ss fuel.
    sym_terminal (sym_steps p env n ss) ==>
    sym_run p env (n + fuel) ss = sym_steps p env n ss
Proof
  Induct >> simp[sym_steps_def, sym_terminal_def, ADD_CLAUSES] >>
  rpt gen_tac >> simp[sym_run_SUC_step] >>
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
