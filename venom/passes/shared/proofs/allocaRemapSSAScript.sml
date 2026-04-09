(*
 * SSA + pointer_derived_vars helpers for alloca remap proofs.
 * Extracted to a separate file for faster incremental builds.
 *)

Theory allocaRemapSSA
Ancestors
  pointerConfinedDefs venomWf venomInst
Libs
  listTheory rich_listTheory arithmeticTheory pred_setTheory

(* MEM inst (fn_insts fn) from block membership *)
Theorem mem_fn_insts_blocks:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem mem_fn_insts_intro:
  !fn bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  simp[fn_insts_def] >> metis_tac[mem_fn_insts_blocks]
QED

(* SSA uniqueness: if ALL_DISTINCT (FLAT (MAP f l)) and v appears in
   f a and f b for a,b in l, then a = b. *)
Theorem all_distinct_flat_map_unique:
  !(l:'a list) (f:'a -> 'b list) a b v.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM a l /\ MEM b l /\
    MEM v (f a) /\ MEM v (f b) ==> a = b
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

(* SSA uniqueness: two instructions sharing an output variable must be equal. *)
Theorem ssa_unique_output:
  !fn inst1 inst2 v.
    ssa_form fn /\ MEM inst1 (fn_insts fn) /\ MEM inst2 (fn_insts fn) /\
    MEM v inst1.inst_outputs /\ MEM v inst2.inst_outputs ==>
    inst1 = inst2
Proof
  rpt strip_tac >>
  irule (INST_TYPE [alpha |-> ``:instruction``, beta |-> ``:string``]
           all_distinct_flat_map_unique) >>
  qexistsl_tac [`\i:instruction. i.inst_outputs`, `fn_insts fn`, `v`] >>
  gvs[ssa_form_def]
QED

(* Every member of pointer_use_step is an output of a pointer-preserving
   instruction with a Var operand in the given list. *)
Theorem pointer_use_step_mem:
  !fn vars v. MEM v (pointer_use_step fn vars) ==>
    ?bb inst u. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              is_pointer_preserving_op inst.inst_opcode /\
              MEM v inst.inst_outputs /\
              MEM (Var u) inst.inst_operands /\ MEM u vars
Proof
  rpt gen_tac >> simp[pointer_use_step_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  rename [`MEM bb fn.fn_blocks`] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename [`MEM inst' bb.bb_instructions`] >>
  pop_assum mp_tac >> rw[] >> gvs[AllCaseEqs()] >>
  gvs[EXISTS_MEM] >>
  rename [`MEM op inst'.inst_operands`] >>
  Cases_on `op` >> gvs[] >>
  metis_tac[]
QED

(* Invariant for the OWHILE in pointer_use_vars: every element of the
   current list is either initial or was added by a pointer-preserving
   instruction that has an operand in the current list.
   Proved as a separate helper to avoid nested tactic chain issues. *)
Theorem pointer_use_owhile_inv_step[local]:
  !fn x.
    (!(v:string). MEM v (case x of INL l => l | INR l => l) ==>
       MEM v vars \/
       ?bb inst u. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         is_pointer_preserving_op inst.inst_opcode /\
         MEM v inst.inst_outputs /\
         MEM (Var u) inst.inst_operands /\
         MEM u (case x of INL l => l | INR l => l)) /\
    ISL x ==>
    (!(v:string). MEM v (case
        (case pointer_use_step_step fn (OUTL x) of
           NONE => INR (OUTL x) | SOME vs => INL vs)
       of INL l => l | INR l => l) ==>
       MEM v vars \/
       ?bb inst u. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         is_pointer_preserving_op inst.inst_opcode /\
         MEM v inst.inst_outputs /\
         MEM (Var u) inst.inst_operands /\
         MEM u (case
            (case pointer_use_step_step fn (OUTL x) of
               NONE => INR (OUTL x) | SOME vs => INL vs)
           of INL l => l | INR l => l))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `x` >> gvs[] >>
  Cases_on `pointer_use_step_step fn x'`
  (* NONE: g(INL x') = INR x', list unchanged. IH applies directly. *)
  >- gvs[]
  (* SOME: g(INL x') = INL (x' ++ new_vars) *)
  >- (simp[] >>
      gvs[pointer_use_step_step_def, LET_DEF, AllCaseEqs()] >>
      rpt strip_tac >> gvs[MEM_APPEND, MEM_FILTER] >>
      TRY (imp_res_tac pointer_use_step_mem >>
           DISJ2_TAC >> metis_tac[] >> NO_TAC) >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      DISJ2_TAC >> metis_tac[])
QED

(* OWHILE invariant: the property is preserved through all iterations.
   Built via ML-level instantiation of OWHILE_INV_IND since the tactic
   level can't do the higher-order matching for P. *)
local
  val owhile_ind = DB.fetch "While" "OWHILE_INV_IND"
    |> INST_TYPE [alpha |-> ``:string list + string list``]
  val P = ``\(s:string list + string list). !v:string.
    MEM v (case s of INL l => l | INR l => l) ==>
    MEM v vars \/ ?bb inst u.
      MEM bb fn_val.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\
      MEM v inst.inst_outputs /\
      MEM (Var u) inst.inst_operands /\
      MEM u (case s of INL l => l | INR l => l)``
  val f = ``\(w:string list + string list).
    case pointer_use_step_step fn_val (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs``
  val s0 = ``INL vars : string list + string list``
  val spec = ISPECL [``ISL : (string list + string list) -> bool``, f, s0]
    (INST [``P:(string list + string list) -> bool`` |-> P] owhile_ind)
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
  (* Discharge base case: trivial by simp *)
  val base = prove(fst (dest_conj (fst (dest_imp (concl spec)))), simp[])
  (* Discharge step case using pointer_use_owhile_inv_step *)
  val step = prove(snd (dest_conj (fst (dest_imp (concl spec)))),
    rpt strip_tac >>
    mp_tac (SPECL [``fn_val:ir_function``, ``x:string list + string list``]
              pointer_use_owhile_inv_step) >>
    simp[])
  val result = MP spec (CONJ base step)
in
  val owhile_pv_inv = save_thm("owhile_pv_inv", GEN_ALL result)
end

(* Members of pointer_use_vars are either in the initial set or are
   outputs of pointer-preserving instructions that have an operand
   in the final pv set. *)
Theorem pointer_use_vars_mem_char:
  !fn vars v. MEM v (pointer_use_vars fn vars) ==>
    MEM v vars \/
    ?bb inst u. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              is_pointer_preserving_op inst.inst_opcode /\
              MEM v inst.inst_outputs /\
              MEM (Var u) inst.inst_operands /\
              MEM u (pointer_use_vars fn vars)
Proof
  rpt gen_tac >>
  simp[pointer_use_vars_def] >>
  Cases_on `OWHILE ISL (\w. case pointer_use_step_step fn (OUTL w) of
              NONE => INR (OUTL w) | SOME vs => INL vs) (INL vars)` >>
  simp[] >>
  Cases_on `x` >> simp[] >> strip_tac >>
  mp_tac owhile_pv_inv >>
  disch_then (qspecl_then [`vars`, `fn`] mp_tac) >>
  disch_then drule >> strip_tac >>
  res_tac >> gvs[] >>
  DISJ2_TAC >> qexistsl_tac [`bb`, `inst`, `u`] >> simp[]
QED

(* Under SSA + roots ⊆ alloca_roots, an instruction with no pv operands
   and not ALLOCA cannot produce pv output vars. *)
Theorem no_pv_outputs_from_no_pv_inputs:
  !fn roots inst bb.
    ssa_form fn /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    ~is_alloca_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    !v. MEM v inst.inst_outputs ==> v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  gvs[pointer_derived_vars_def] >>
  imp_res_tac pointer_use_vars_mem_char >> gvs[]
  (* Case 1: v in SET_TO_LIST roots => v IN roots => ALLOCA output => SSA *)
  >- (`v IN roots` by gvs[MEM_SET_TO_LIST] >>
      `v IN alloca_roots fn` by gvs[SUBSET_DEF] >>
      gvs[alloca_roots_def, inst_output_def, AllCaseEqs()] >>
      rename [`MEM inst' (fn_insts fn)`] >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
      `inst = inst'` by
        (irule ssa_unique_output >> simp[] >> metis_tac[]) >>
      gvs[is_alloca_op_def])
  (* Case 2: pointer-preserving inst' with pv operand. SSA: inst = inst'. *)
  >- (rename [`MEM inst' bb'.bb_instructions`,
              `MEM (Var u) inst'.inst_operands`] >>
      `MEM inst (fn_insts fn) /\ MEM inst' (fn_insts fn)` by
        metis_tac[mem_fn_insts_intro] >>
      `inst = inst'` by
        (irule ssa_unique_output >> simp[] >> metis_tac[]) >>
      gvs[] >>
      first_x_assum (qspecl_then [`Var u`, `u`] mp_tac) >> simp[] >>
      simp[pointer_derived_vars_def])
QED
