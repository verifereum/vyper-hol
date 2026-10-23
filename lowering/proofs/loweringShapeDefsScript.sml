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
 *   lowered_inst_ok              — the per-instruction shape; `internal`
 *                                  selects internal-function or entry code
 *   shape_state, shape_extends   — the state invariant and the append step
 *   shape_step                   — Hoare-style judgment on compile actions
 *   shape_step_* rules           — composition and monad primitives
 *   opaque_insts_ok_opaque_use_ok — the invariant gives opaque_use_ok
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
Definition jump_labels_ok_def:
  jump_labels_ok inst <=>
    is_terminator inst.inst_opcode ==>
    !l. MEM (Label l) inst.inst_operands ==> jump_label_ok l
End

(* Entry code (internal = F) never returns through RET and declares no
   parameters; internal-function code (internal = T) never halts the
   transaction with STOP or RETURN. *)
Definition lowered_inst_ok_def:
  lowered_inst_ok internal inst <=>
    raw_opcode_ok inst.inst_opcode /\ inst_shape_ok inst /\
    jump_labels_ok inst /\
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

(* ===== Composition rules ===== *)

Theorem shape_step_bind:
  !internal LP P m f Q R.
    shape_step internal LP P m Q /\
    (!x. shape_step internal LP (Q x) (f x) R) ==>
    shape_step internal LP P (comp_bind m f) R
Proof
  rw[shape_step_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[shape_extends_trans]
QED

Theorem shape_step_ignore_bind:
  !internal LP P m f Q R.
    shape_step internal LP P m Q /\
    (!x. shape_step internal LP (Q x) f R) ==>
    shape_step internal LP P (comp_ignore_bind m f) R
Proof
  rw[comp_ignore_bind_def] >> irule shape_step_bind >> metis_tac[]
QED

Theorem shape_step_return:
  !internal LP P Q x.
    (!st. P st ==> Q x st) ==>
    shape_step internal LP P (comp_return x) Q
Proof
  rw[shape_step_def, comp_return_def, shape_extends_refl]
QED

Theorem shape_extends_LP_mono:
  !internal LP LP' st st'.
    shape_extends internal LP st st' /\ (!l. LP l ==> LP' l) ==>
    shape_extends internal LP' st st'
Proof
  rw[shape_extends_def, EVERY_MEM]
QED

Theorem shape_step_conseq:
  !internal LP LP' P P' m Q Q'.
    shape_step internal LP P m Q /\ (!st. P' st ==> P st) /\
    (!x st. Q x st ==> Q' x st) /\ (!l. LP l ==> LP' l) ==>
    shape_step internal LP' P' m Q'
Proof
  rw[shape_step_def] >> `P st` by res_tac >>
  qpat_x_assum `!st x st'. _` drule_all >> strip_tac >>
  metis_tac[shape_extends_LP_mono]
QED

Theorem shape_step_comp_get:
  !internal LP P.
    shape_step internal LP P comp_get (\x st'. x = st' /\ P st')
Proof
  rw[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem shape_step_frame:
  !internal LP P m Q R.
    shape_step internal LP P m Q /\ shape_stable R ==>
    shape_step internal LP (\st. R st /\ P st) m (\x st. R st /\ Q x st)
Proof
  rw[shape_step_def, shape_stable_def] >> metis_tac[]
QED

(* ===== Monad primitives ===== *)

Theorem shape_extends_same_code:
  !internal LP st st'.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts /\
    st.cs_next_var <= st'.cs_next_var ==>
    shape_extends internal LP st st'
Proof
  rpt strip_tac >>
  `state_insts st' = state_insts st /\ all_blocks st' = all_blocks st`
    by gs[state_insts_def, all_blocks_def] >>
  `cs_extends st st'` by (irule cs_extends_same_block >> gs[]) >>
  gs[shape_extends_def, added_insts_def, added_labels_def, DROP_LENGTH_NIL,
     DROP_LENGTH_TOO_LONG]
QED

Theorem shape_state_same_code:
  !st st'.
    shape_state st /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts /\
    st.cs_next_var <= st'.cs_next_var ==>
    shape_state st'
Proof
  rpt strip_tac >>
  `state_insts st' = state_insts st`
    by gs[state_insts_def, all_blocks_def] >>
  gs[shape_state_def] >> metis_tac[not_fresh_at_mono]
QED

(* The output of emit_op / fresh_var is a new compiler variable. *)
Theorem fresh_output_props:
  !st st'. st'.cs_next_var = st.cs_next_var + 1 ==>
    ~not_fresh_at st (STRING #"%" (toString st.cs_next_var)) /\
    not_fresh_at st' (STRING #"%" (toString st.cs_next_var))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL])
  >> rw[not_fresh_at_def] >> irule fresh_var_distinct >> gs[]
QED

Theorem shape_step_fresh_var:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R fresh_var
      (\x st'. R st' /\ plain_operand st' (Var x))
Proof
  simp[shape_step_def, fresh_var_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  `st1.cs_next_var = st.cs_next_var + 1` by simp[Abbr `st1`] >>
  drule fresh_output_props >> strip_tac >>
  `state_insts st1 = state_insts st`
    by simp[Abbr `st1`, state_insts_def, all_blocks_def] >>
  `R st1` by metis_tac[shape_stable_def] >>
  gs[plain_operand_def, stackPlanTypesTheory.is_label_operand_def, shape_state_def,
     opaque_out_def] >>
  metis_tac[]
QED

Theorem shape_step_fresh_id:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R fresh_id (\x st'. R st')
Proof
  simp[shape_step_def, fresh_id_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_step_fresh_label:
  !internal LP R sfx.
    shape_stable R ==>
    shape_step internal LP R (fresh_label sfx)
      (\l st'. R st' /\ compiler_label l)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >> gvs[fresh_label_def] >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `shape_extends internal LP st st1`
    by (irule shape_extends_same_code >> simp[Abbr `st1`]) >>
  `shape_state st1`
    by (irule shape_state_same_code >> qexists_tac `st` >>
        simp[Abbr `st1`]) >>
  simp[compiler_label_def, fresh_label_output_in_future] >>
  metis_tac[shape_stable_def]
QED

Theorem DROP_LENGTH_MAP_APPEND[local]:
  !f l m. DROP (LENGTH l) (MAP f l ++ m) = m
Proof
  rpt gen_tac >>
  `LENGTH l = LENGTH (MAP f l)` by simp[] >>
  pop_assum SUBST1_TAC >> simp[DROP_LENGTH_APPEND]
QED

Theorem shape_step_new_block:
  !internal LP R lbl.
    shape_stable R /\ LP lbl ==>
    shape_step internal LP R (new_block lbl) (\x st'. R st')
Proof
  simp[shape_step_def, new_block_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `new_block lbl st = (st.cs_current_bb, st1)`
    by simp[new_block_def, Abbr `st1`] >>
  drule cs_extends_new_block >> strip_tac >>
  `all_blocks st1 =
     all_blocks st ++ [<| bb_label := lbl; bb_instructions := [] |>]`
    by simp[Abbr `st1`, all_blocks_def] >>
  `st1.cs_next_var = st.cs_next_var` by simp[Abbr `st1`] >>
  `state_insts st1 = state_insts st` by gs[state_insts_def] >>
  `added_labels st st1 = [lbl]`
    by gs[added_labels_def, DROP_LENGTH_MAP_APPEND] >>
  `added_insts st st1 = []` by gs[added_insts_def, DROP_LENGTH_NIL] >>
  `shape_extends internal LP st st1` by gs[shape_extends_def] >>
  `shape_state st1`
    by (gs[shape_state_def] >>
        metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_REFL]) >>
  metis_tac[shape_stable_def]
QED

Theorem opaque_out_snoc:
  !opc insts inst x.
    opaque_out opc (insts ++ [inst]) x <=>
    opaque_out opc insts x \/ (inst.inst_opcode = opc /\ MEM x inst.inst_outputs)
Proof
  rw[opaque_out_def] >> metis_tac[]
QED

Theorem opaque_insts_ok_snoc:
  !st st' insts inst.
    opaque_insts_ok insts /\
    (!i x. MEM i insts /\ MEM (Var x) i.inst_operands ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out GAS (insts ++ [inst]) x ==>
          (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
          ?rest. inst.inst_operands = Var x :: rest /\ ~MEM (Var x) rest) /\
       (opaque_out RETPC_PARAM (insts ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front. inst.inst_operands = front ++ [Var x] /\
                  ~MEM (Var x) front)) ==>
    opaque_insts_ok (insts ++ [inst])
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once opaque_insts_ok_def] >> qx_genl_tac [`i`, `y`] >> strip_tac
  >- (`not_fresh_at st y` by metis_tac[] >>
      `MEM y inst.inst_outputs ==>
       inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM`
        by (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      qpat_x_assum `opaque_insts_ok _`
        (qspecl_then [`i`, `y`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
      Cases_on `MEM y inst.inst_outputs` >> gvs[opaque_out_snoc])
  >> gvs[] >>
  qpat_x_assum `!x. MEM (Var x) inst.inst_operands ==> _ /\ _`
    (qspec_then `y` mp_tac) >>
  simp[]
QED

Theorem operands_not_fresh_snoc[local]:
  !st st' insts inst.
    st.cs_next_var <= st'.cs_next_var /\
    (!i x. MEM i insts /\ MEM (Var x) i.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) ==>
    !i x. MEM i (insts ++ [inst]) /\ MEM (Var x) i.inst_operands ==>
          not_fresh_at st' x
Proof
  rw[] >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[] >>
  metis_tac[]
QED

Theorem opaque_outputs_not_fresh_snoc[local]:
  !st st' insts inst.
    st.cs_next_var <= st'.cs_next_var /\
    (!i x. MEM i insts /\ MEM i.inst_opcode [GAS; RETPC_PARAM] /\
           MEM x i.inst_outputs ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) ==>
    !i x. MEM i (insts ++ [inst]) /\ MEM i.inst_opcode [GAS; RETPC_PARAM] /\
          MEM x i.inst_outputs ==> not_fresh_at st' x
Proof
  rpt gen_tac >> strip_tac >> qx_genl_tac [`i`, `y`] >> strip_tac >>
  `MEM i insts \/ i = inst` by gvs[] >> pop_assum strip_assume_tac
  >- (`not_fresh_at st y` by metis_tac[] >> metis_tac[not_fresh_at_mono])
  >> gvs[]
QED

(* Appending one instruction to the open block. *)
Theorem shape_append_inst:
  !internal LP st st' inst.
    shape_state st /\ lowered_inst_ok internal inst /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    st.cs_next_var <= st'.cs_next_var /\
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
       !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x /\ not_fresh_at st' x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out GAS (state_insts st ++ [inst]) x ==>
          (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
          ?rest. inst.inst_operands = Var x :: rest /\ ~MEM (Var x) rest) /\
       (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front. inst.inst_operands = front ++ [Var x] /\
                  ~MEM (Var x) front)) ==>
    shape_extends internal LP st st' /\ shape_state st'
Proof
  rpt gen_tac >> strip_tac >>
  `state_insts st' = state_insts st ++ [inst]`
    by gs[state_insts_def, all_blocks_def] >>
  `added_insts st st' = [inst]`
    by gs[added_insts_def, DROP_LENGTH_APPEND] >>
  `added_labels st st' = []`
    by gs[added_labels_def, all_blocks_def, DROP_LENGTH_TOO_LONG] >>
  `cs_extends st st'` by (irule cs_extends_same_block >> gs[]) >>
  qpat_x_assum `shape_state st`
    (strip_assume_tac o REWRITE_RULE [shape_state_def]) >>
  conj_tac
  >- (simp[shape_extends_def] >>
      qpat_assum `added_insts _ _ = _` (fn th => simp[th]) >>
      qpat_assum `added_labels _ _ = _` (fn th => simp[th]) >>
      rpt strip_tac >> gs[]) >>
  REWRITE_TAC [shape_state_def] >>
  qpat_assum `state_insts st' = _` (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac
  >- (match_mp_tac (Q.SPECL [`st`, `st'`] opaque_insts_ok_snoc) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (match_mp_tac (Q.SPECL [`st`, `st'`] operands_not_fresh_snoc) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >> match_mp_tac (Q.SPECL [`st`, `st'`] opaque_outputs_not_fresh_snoc) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem plain_operand_not_opaque:
  !st op x. plain_operand st op /\ op = Var x ==>
    not_fresh_at st x /\ ~opaque_out GAS (state_insts st) x /\
    ~opaque_out RETPC_PARAM (state_insts st) x
Proof
  rw[plain_operand_def]
QED

(* Operands that are all plain, appended by a non-opaque opcode. *)
Theorem plain_append_ok:
  !st inst.
    EVERY (plain_operand st) inst.inst_operands /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
         ~opaque_out GAS (state_insts st ++ [inst]) x /\
         ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)
Proof
  rpt gen_tac >> strip_tac >> simp[opaque_out_snoc] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[plain_operand_def]
QED

(* A call whose head operand may be a GAS value. *)
Theorem call_append_ok:
  !st g rest inst.
    MEM inst.inst_opcode [CALL; STATICCALL] /\
    inst.inst_operands = g :: rest /\
    (gas_operand st g \/ plain_operand st g) /\
    EVERY (plain_operand st) rest ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       (opaque_out GAS (state_insts st ++ [inst]) x ==>
          (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
          ?rest'. inst.inst_operands = Var x :: rest' /\ ~MEM (Var x) rest') /\
       ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `!x. MEM (Var x) rest ==>
       not_fresh_at st x /\ ~opaque_out GAS (state_insts st) x /\
       ~opaque_out RETPC_PARAM (state_insts st) x`
    by (gvs[EVERY_MEM] >> metis_tac[plain_operand_not_opaque]) >>
  `!x. g = Var x ==>
       not_fresh_at st x /\ ~opaque_out RETPC_PARAM (state_insts st) x`
    by (rw[] >> gvs[gas_operand_def, plain_operand_def] >> metis_tac[]) >>
  simp[opaque_out_snoc] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A RET whose last operand may be the return PC. *)
Theorem ret_append_ok:
  !st front r inst.
    inst.inst_opcode = RET /\ inst.inst_operands = front ++ [r] /\
    (retpc_operand st r \/ plain_operand st r) /\
    EVERY (plain_operand st) front ==>
    (!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
    (!x. MEM (Var x) inst.inst_operands ==>
       ~opaque_out GAS (state_insts st ++ [inst]) x /\
       (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
          inst.inst_opcode = RET /\
          ?front'. inst.inst_operands = front' ++ [Var x] /\
                   ~MEM (Var x) front'))
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM (Var x) front ==>
       not_fresh_at st x /\ ~opaque_out GAS (state_insts st) x /\
       ~opaque_out RETPC_PARAM (state_insts st) x`
    by (gvs[EVERY_MEM] >> metis_tac[plain_operand_not_opaque]) >>
  `!x. r = Var x ==>
       not_fresh_at st x /\ ~opaque_out GAS (state_insts st) x`
    by (rw[] >> gvs[retpc_operand_def, plain_operand_def] >> metis_tac[]) >>
  simp[opaque_out_snoc] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* A fresh output of a non-opaque instruction is plain. *)
Theorem fresh_out_plain:
  !st st1 inst out.
    shape_state st /\ ~not_fresh_at st out /\ not_fresh_at st1 out /\
    state_insts st1 = state_insts st ++ [inst] /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM ==>
    plain_operand st1 (Var out)
Proof
  rpt gen_tac >> strip_tac >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       opaque_out_snoc] >>
  gvs[shape_state_def, opaque_out_def] >> metis_tac[]
QED

(* A fresh output of GAS or RETPC_PARAM is opaque of exactly that kind. *)
Theorem fresh_out_opaque:
  !st st1 inst out.
    shape_state st /\ ~not_fresh_at st out /\
    state_insts st1 = state_insts st ++ [inst] /\
    MEM out inst.inst_outputs ==>
    opaque_out inst.inst_opcode (state_insts st1) out /\
    (!opc. MEM opc [GAS; RETPC_PARAM] /\ opc <> inst.inst_opcode ==>
           ~opaque_out opc (state_insts st1) out)
Proof
  rpt gen_tac >> strip_tac >> simp[opaque_out_snoc] >>
  rpt strip_tac >> gvs[shape_state_def, opaque_out_def] >> metis_tac[]
QED

Theorem shape_step_emit:
  !internal LP R inst.
    shape_stable R /\ lowered_inst_ok internal inst /\
    ~MEM inst.inst_opcode [GAS; RETPC_PARAM] ==>
    shape_step internal LP
      (\st. R st /\ EVERY (plain_operand st) inst.inst_operands)
      (emit inst) (\x st'. R st')
Proof
  simp[shape_step_def, emit_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem emit_op_eq:
  !opc ops st.
    emit_op opc ops st =
      (Var (STRING #"%" (toString st.cs_next_var)),
       st with <| cs_next_id := st.cs_next_id + 1;
                  cs_next_var := st.cs_next_var + 1;
                  cs_current_insts := st.cs_current_insts ++
                    [mk_inst st.cs_next_id opc ops
                       [STRING #"%" (toString st.cs_next_var)]] |>)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def]
QED

Theorem emit_inst_eq:
  !opc ops outs st.
    emit_inst opc ops outs st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                      cs_current_insts := st.cs_current_insts ++
                        [mk_inst st.cs_next_id opc ops outs] |>)
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem emit_void_eq:
  !opc ops st.
    emit_void opc ops st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                      cs_current_insts := st.cs_current_insts ++
                        [mk_inst st.cs_next_id opc ops []] |>)
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def]
QED

(* The state after emit_op, its new instruction and its output. *)
Theorem emit_op_facts:
  !opc ops st x st1.
    emit_op opc ops st = (x, st1) ==>
    ?out. x = Var out /\ st1.cs_next_var = st.cs_next_var + 1 /\
          ~not_fresh_at st out /\ not_fresh_at st1 out /\
          st1.cs_blocks = st.cs_blocks /\
          st1.cs_current_bb = st.cs_current_bb /\
          st1.cs_current_insts = st.cs_current_insts ++
            [mk_inst st.cs_next_id opc ops [out]] /\
          state_insts st1 =
            state_insts st ++ [mk_inst st.cs_next_id opc ops [out]]
Proof
  rw[emit_op_eq] >> simp[state_insts_def, all_blocks_def] >>
  irule fresh_output_props >> simp[]
QED

Theorem shape_step_emit_op:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal LP (\st. R st /\ EVERY (plain_operand st) ops)
      (emit_op opc ops) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> simp[shape_step_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops [out]` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   inst.inst_outputs = [out] /\ lowered_inst_ok internal inst`
    by fs[Abbr `inst`, mk_inst_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (plain_operand st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  gvs[] >> match_mp_tac (Q.SPECL [`st`, `st'`, `inst`] fresh_out_plain) >> gs[]
QED

Theorem shape_step_emit_inst:
  !internal LP R opc ops outs.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
    shape_step internal LP (\st. R st /\ EVERY (plain_operand st) ops)
      (emit_inst opc ops outs) (\x st'. R st')
Proof
  rpt strip_tac >> simp[shape_step_def, emit_inst_eq] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc ops outs` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = ops /\
   lowered_inst_ok internal inst`
    by fs[Abbr `inst`, mk_inst_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM` by gvs[] >>
  `EVERY (plain_operand st) inst.inst_operands` by gvs[] >>
  drule_all plain_append_ok >> strip_tac >>
  `shape_extends internal LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`]) >>
  metis_tac[shape_stable_def]
QED

Theorem shape_step_emit_void:
  !internal LP R opc ops.
    shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM] /\
    (!id. lowered_inst_ok internal (mk_inst id opc ops [])) ==>
    shape_step internal LP (\st. R st /\ EVERY (plain_operand st) ops)
      (emit_void opc ops) (\x st'. R st')
Proof
  rpt strip_tac >>
  `emit_void opc ops = emit_inst opc ops []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  simp[shape_step_emit_inst]
QED

(* GAS feeds only the gas slot of a call. *)
Theorem shape_step_emit_op_gas:
  !internal LP R.
    shape_stable R ==>
    shape_step internal LP R (emit_op GAS [])
      (\x st'. R st' /\ gas_operand st' x)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id GAS [] [out]` >>
  `inst.inst_opcode = GAS /\ inst.inst_operands = [] /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok internal inst` by (simp[Abbr `inst`] >> EVAL_TAC) >>
  `shape_extends internal LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  qspecl_then [`st`, `st'`, `inst`, `out`] mp_tac fresh_out_opaque >>
  gs[gas_operand_def]
QED

Theorem shape_step_emit_op_call:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) ==>
    shape_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (emit_op opc (g :: rest)) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt strip_tac >> simp[shape_step_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id opc (g :: rest) [out]` >>
  `inst.inst_opcode = opc /\ inst.inst_operands = g :: rest /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok internal inst`
    by (simp[Abbr `inst`] >> qpat_x_assum `!id outs. lowered_inst_ok _ _` MATCH_ACCEPT_TAC) >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> RETPC_PARAM`
    by (Cases_on `opc = CALL` >> gvs[]) >>
  `(!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
   (!x. MEM (Var x) inst.inst_operands ==>
      (opaque_out GAS (state_insts st ++ [inst]) x ==>
         (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
         ?rest'. inst.inst_operands = Var x :: rest' /\ ~MEM (Var x) rest') /\
      ~opaque_out RETPC_PARAM (state_insts st ++ [inst]) x)`
    by (match_mp_tac (Q.SPECL [`st`, `g`, `rest`, `inst`] call_append_ok) >>
        ASM_REWRITE_TAC[]) >>
  `shape_extends internal LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`internal`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[] >> rpt strip_tac >> res_tac >> gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  gvs[] >> match_mp_tac (Q.SPECL [`st`, `st'`, `inst`] fresh_out_plain) >> gs[]
QED

(* The return PC exists only in internal-function code. *)
Theorem shape_step_emit_op_retpc:
  !LP R w.
    shape_stable R ==>
    shape_step T LP R (emit_op RETPC_PARAM [Lit w])
      (\x st'. R st' /\ retpc_operand st' x)
Proof
  simp[shape_step_def, PULL_FORALL, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id RETPC_PARAM [Lit w] [out]` >>
  `inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit w] /\
   inst.inst_outputs = [out]`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok T inst` by (simp[Abbr `inst`] >> EVAL_TAC) >>
  `shape_extends T LP st st' /\ shape_state st'`
    by (match_mp_tac (Q.SPECL [`T`, `LP`, `st`, `st'`, `inst`] shape_append_inst) >>
        gs[]) >>
  `R st'` by metis_tac[shape_stable_def] >>
  qspecl_then [`st`, `st'`, `inst`, `out`] mp_tac fresh_out_opaque >>
  gs[retpc_operand_def]
QED

Theorem shape_step_emit_inst_ret:
  !LP R front r.
    shape_stable R /\
    (!id. lowered_inst_ok T (mk_inst id RET (front ++ [r]) [])) ==>
    shape_step T LP
      (\st. R st /\ EVERY (plain_operand st) front /\
            (retpc_operand st r \/ plain_operand st r))
      (emit_inst RET (front ++ [r]) []) (\x st'. R st')
Proof
  rpt strip_tac >> simp[shape_step_def, emit_inst_eq] >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `shape_extends _ _ st st1` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id RET (front ++ [r]) []` >>
  `inst.inst_opcode = RET /\ inst.inst_operands = front ++ [r] /\
   inst.inst_outputs = []`
    by simp[Abbr `inst`, mk_inst_def] >>
  `lowered_inst_ok T inst`
    by (simp[Abbr `inst`] >> qpat_x_assum `!id. lowered_inst_ok _ _` MATCH_ACCEPT_TAC) >>
  `(!x. MEM (Var x) inst.inst_operands ==> not_fresh_at st x) /\
   (!x. MEM (Var x) inst.inst_operands ==>
      ~opaque_out GAS (state_insts st ++ [inst]) x /\
      (opaque_out RETPC_PARAM (state_insts st ++ [inst]) x ==>
         inst.inst_opcode = RET /\
         ?front'. inst.inst_operands = front' ++ [Var x] /\
                  ~MEM (Var x) front'))`
    by (match_mp_tac (Q.SPECL [`st`, `front`, `r`, `inst`] ret_append_ok) >>
        ASM_REWRITE_TAC[]) >>
  `shape_extends T LP st st1 /\ shape_state st1`
    by (match_mp_tac (Q.SPECL [`T`, `LP`, `st`, `st1`, `inst`] shape_append_inst) >>
        gs[Abbr `st1`] >> rpt strip_tac >> res_tac >> gs[]) >>
  metis_tac[shape_stable_def]
QED

(* ===== From the invariant to opaque_use_ok ===== *)

Theorem copy_phi_var_opaque_out:
  !origin fn x.
    copy_phi_var origin fn x ==>
    !insts. opaque_insts_ok insts /\ MEM origin [GAS; RETPC_PARAM] /\
            (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
            opaque_out origin insts x
Proof
  Induct_on `copy_phi_var` >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- (simp[opaque_out_def] >> metis_tac[])
  >> rename1 `copy_phi_var origin fn y` >>
  `opaque_out origin insts y` by (first_x_assum irule >> gs[]) >>
  `MEM inst insts` by res_tac >>
  qpat_x_assum `MEM origin _` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `opaque_insts_ok _`
    (qspecl_then [`inst`, `y`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
  gvs[]
QED

Theorem opaque_insts_ok_opaque_use_ok:
  !insts fn.
    opaque_insts_ok insts /\
    (!inst. MEM inst (fn_insts fn) ==> MEM inst insts) ==>
    opaque_use_ok fn
Proof
  rpt strip_tac >> simp[opaque_use_ok_def, gas_var_def, retpc_var_def] >>
  rpt gen_tac >> strip_tac >>
  `MEM inst insts` by res_tac >>
  rpt conj_tac >> strip_tac >>
  drule copy_phi_var_opaque_out >>
  disch_then (qspec_then `insts` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  qpat_x_assum `opaque_insts_ok _`
    (qspecl_then [`inst`, `x`] mp_tac o REWRITE_RULE [opaque_insts_ok_def]) >>
  simp[gas_use_ok_def, retpc_use_ok_def] >> metis_tac[]
QED
