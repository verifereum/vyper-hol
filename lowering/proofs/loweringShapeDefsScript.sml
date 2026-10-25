(*
 * Shape invariant of the raw lowering (S2 of #626).
 *
 * The compile monad only appends code.  These definitions say what the code
 * a compile action appends looks like, so that o1_source_unit_ok of a lowered
 * unit follows from one fact per generator.
 *
 * TOP-LEVEL:
 *   all_blocks, state_insts      — the blocks and instructions of a state
 *   added_insts, added_labels    — what a compile action appended
 *   opaque_out, opaque_insts_ok  — GAS / RETPC_PARAM outputs used only where
 *                                  gas_use_ok / retpc_use_ok allow, and never
 *                                  copied
 *   plain_operand                — an operand the lowering may pass anywhere
 *   label_or_plain               — a plain operand or a label
 *   compiler_label, jump_label_ok, inst_jump_labels_ok
 *                                — labels a terminator may jump to: compiler
 *                                  labels or "fn_" function entries
 *   lowered_inst_ok              — the per-instruction shape; `internal`
 *                                  selects internal-function or entry code
 *   shape_state, shape_extends   — the state invariant and the append step
 *   shape_step                   — Hoare-style judgment on compile actions
 *   shape_stable                 — a state predicate kept by every append
 *   gas_operand, retpc_operand   — a variable holding a GAS / RETPC_PARAM
 *                                  output
 *
 * The rules for shape_step are in loweringShapeRules.
 *)
Theory loweringShapeDefs
Ancestors
  list rich_list compileEnv emitHelper emitHelperProps fragExec venomInst
  unitShapeDefs

(* ===== Code held by a compile state ===== *)

(* Finished blocks oldest first, then the open block: the block stream that
   extract_context_with_internals packages. *)
Definition all_blocks_def:
  all_blocks (st : compile_state) =
    REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb;
        bb_instructions := st.cs_current_insts |>]
End

Definition state_insts_def:
  state_insts (st : compile_state) =
    FLAT (MAP (\bb. bb.bb_instructions) (all_blocks st))
End

(* Under cs_extends st st', state_insts st is a prefix of state_insts st'
   (state_insts_cs_extends), so these are exactly the appended parts. *)
Definition added_insts_def:
  added_insts (st : compile_state) (st' : compile_state) =
    DROP (LENGTH (state_insts st)) (state_insts st')
End

Definition added_labels_def:
  added_labels (st : compile_state) (st' : compile_state) =
    DROP (LENGTH (all_blocks st)) (MAP (\bb. bb.bb_label) (all_blocks st'))
End

(* ===== Opaque values ===== *)

Definition opaque_out_def:
  opaque_out opc insts x <=>
    ?inst. MEM inst insts /\ inst.inst_opcode = opc /\ MEM x inst.inst_outputs
End

(* Stricter than opaque_use_ok: no ASSIGN/PHI copies at all, so the
   copy/PHI closure is just the seeds. *)
Definition opaque_insts_ok_def:
  opaque_insts_ok insts <=>
    !inst x. MEM inst insts /\ MEM (Var x) inst.inst_operands ==>
      (opaque_out GAS insts x ==>
         (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
         ?rest. inst.inst_operands = Var x :: rest /\ ~MEM (Var x) rest) /\
      (opaque_out RETPC_PARAM insts x ==>
         inst.inst_opcode = RET /\
         ?front. inst.inst_operands = front ++ [Var x] /\ ~MEM (Var x) front)
End

(* An operand that may appear in any position: no label, no compiler
   variable still to be allocated, and no GAS or return-PC value. *)
Definition plain_operand_def:
  plain_operand (st : compile_state) op <=>
    ~is_label_operand op /\
    !x. op = Var x ==>
        not_fresh_at st x /\
        ~opaque_out GAS (state_insts st) x /\
        ~opaque_out RETPC_PARAM (state_insts st) x
End

(* An operand of an ordinary instruction: a label (jump target, INVOKE
   callee) or a plain operand. *)
Definition label_or_plain_def:
  label_or_plain st op <=> is_label_operand op \/ plain_operand st op
End

(* ===== Per-instruction shape ===== *)

(* Labels made by fresh_label. *)
Definition compiler_label_def:
  compiler_label l <=> l IN compiler_labels_future 0
End

(* Compiler-generated labels and external entry labels ("fn_" ++ name). *)
Definition jump_label_ok_def:
  jump_label_ok l <=> compiler_label l \/ isPREFIX "fn_" l
End

(* Every label a terminator names: the block's successors. *)
Definition inst_jump_labels_ok_def:
  inst_jump_labels_ok inst <=>
    is_terminator inst.inst_opcode ==>
    !l. MEM (Label l) inst.inst_operands ==> jump_label_ok l
End

(* Entry code (internal = F) never returns through RET and declares no
   parameters; internal-function code (internal = T) never halts the
   transaction with STOP or RETURN. *)
Definition lowered_inst_ok_def:
  lowered_inst_ok internal inst <=>
    raw_opcode_ok inst.inst_opcode /\ inst_shape_ok inst /\
    inst_jump_labels_ok inst /\
    (internal ==> ~MEM inst.inst_opcode [STOP; RETURN]) /\
    (~internal ==> inst.inst_opcode <> RET /\
                   ~is_param_opcode inst.inst_opcode)
End

(* ===== State invariant and the append step ===== *)

Definition shape_state_def:
  shape_state (st : compile_state) <=>
    opaque_insts_ok (state_insts st) /\
    (!inst x. MEM inst (state_insts st) /\ MEM (Var x) inst.inst_operands ==>
              not_fresh_at st x) /\
    (!inst x. MEM inst (state_insts st) /\
              MEM inst.inst_opcode [GAS; RETPC_PARAM] /\
              MEM x inst.inst_outputs ==> not_fresh_at st x)
End

(* LP constrains the labels of the blocks started on the way. *)
Definition shape_extends_def:
  shape_extends internal (LP : string -> bool) st st' <=>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    EVERY (lowered_inst_ok internal) (added_insts st st') /\
    EVERY LP (added_labels st st') /\
    !inst x. MEM inst (added_insts st st') /\
             MEM inst.inst_opcode [GAS; RETPC_PARAM] /\
             MEM x inst.inst_outputs ==> ~not_fresh_at st x
End

Definition shape_step_def:
  shape_step internal LP (P : compile_state -> bool) (m : 'a compiler)
             (Q : 'a -> compile_state -> bool) <=>
    !st x st'. m st = (x, st') /\ P st /\ shape_state st ==>
      shape_extends internal LP st st' /\ shape_state st' /\ Q x st'
End

(* A precondition that survives appending code. *)
Definition shape_stable_def:
  shape_stable (R : compile_state -> bool) <=>
    !internal LP st st'. R st /\ shape_extends internal LP st st' ==> R st'
End

(* Opaque values that may only go where opaque_insts_ok allows. *)
Definition gas_operand_def:
  gas_operand (st : compile_state) op <=>
    ?g. op = Var g /\ not_fresh_at st g /\
        opaque_out GAS (state_insts st) g /\
        ~opaque_out RETPC_PARAM (state_insts st) g
End

Definition retpc_operand_def:
  retpc_operand (st : compile_state) op <=>
    ?r. op = Var r /\ not_fresh_at st r /\
        opaque_out RETPC_PARAM (state_insts st) r /\
        ~opaque_out GAS (state_insts st) r
End

(* ===== The compile monad only appends ===== *)

Theorem state_insts_cs_extends:
  !st st'. cs_extends st st' ==>
           state_insts st' = state_insts st ++ added_insts st st'
Proof
  rpt strip_tac >>
  `?ext. state_insts st' = state_insts st ++ ext`
    suffices_by (strip_tac >> simp[added_insts_def, DROP_LENGTH_APPEND]) >>
  gvs[cs_extends_def, state_insts_def, all_blocks_def] >>
  Cases_on `new = []` >> gvs[IS_PREFIX_APPEND] >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  pop_assum SUBST1_TAC >>
  simp[REVERSE_APPEND, FLAT_APPEND, MAP_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem block_labels_cs_extends:
  !st st'. cs_extends st st' ==>
    MAP (\bb. bb.bb_label) (all_blocks st') =
    MAP (\bb. bb.bb_label) (all_blocks st) ++ added_labels st st'
Proof
  rpt strip_tac >>
  `?ext. MAP (\bb. bb.bb_label) (all_blocks st') =
         MAP (\bb. bb.bb_label) (all_blocks st) ++ ext`
    suffices_by (strip_tac >>
                 simp[added_labels_def, DROP_LENGTH_APPEND, LENGTH_MAP] >>
                 metis_tac[LENGTH_MAP, DROP_LENGTH_APPEND]) >>
  gvs[cs_extends_def, all_blocks_def] >>
  Cases_on `new = []` >> gvs[] >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  pop_assum SUBST1_TAC >>
  simp[REVERSE_APPEND, MAP_APPEND]
QED

Theorem not_fresh_at_mono:
  !st st' x. st.cs_next_var <= st'.cs_next_var /\ not_fresh_at st x ==>
             not_fresh_at st' x
Proof
  rw[not_fresh_at_def]
QED

Theorem shape_extends_refl:
  !internal LP st. shape_extends internal LP st st
Proof
  simp[shape_extends_def, cs_extends_refl, added_insts_def,
       added_labels_def, DROP_LENGTH_NIL, DROP_LENGTH_TOO_LONG]
QED

Theorem shape_extends_trans:
  !internal LP st1 st2 st3.
    shape_extends internal LP st1 st2 /\ shape_extends internal LP st2 st3 ==>
    shape_extends internal LP st1 st3
Proof
  rpt gen_tac >> simp[shape_extends_def] >> strip_tac >>
  `cs_extends st1 st3` by metis_tac[cs_extends_trans] >>
  `added_insts st1 st3 = added_insts st1 st2 ++ added_insts st2 st3`
    by (`state_insts st3 = state_insts st1 ++ added_insts st1 st3`
          by simp[state_insts_cs_extends] >>
        `state_insts st3 = state_insts st2 ++ added_insts st2 st3`
          by simp[state_insts_cs_extends] >>
        `state_insts st2 = state_insts st1 ++ added_insts st1 st2`
          by simp[state_insts_cs_extends] >>
        gvs[]) >>
  `added_labels st1 st3 = added_labels st1 st2 ++ added_labels st2 st3`
    by (imp_res_tac block_labels_cs_extends >> gvs[]) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem plain_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ plain_operand st op ==>
    plain_operand st' op
Proof
  rw[plain_operand_def, shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem label_or_plain_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ label_or_plain st op ==>
    label_or_plain st' op
Proof
  rw[label_or_plain_def] >> metis_tac[plain_operand_mono]
QED

Theorem gas_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ gas_operand st op ==>
    gas_operand st' op
Proof
  rw[gas_operand_def, shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem retpc_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ retpc_operand st op ==>
    retpc_operand st' op
Proof
  rw[retpc_operand_def, shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED
