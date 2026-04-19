(*
 * Instruction Simulation Helpers
 *
 * Foundational lemmas for gen_inst_simulation:
 *   - operand_val stability under update_var
 *   - venom_asm_rel stability under variable-only updates
 *   - plan_stack_rel properties for operand evaluation
 *   - asm_steps for empty plans
 *
 * These are the building blocks for proving per-instruction simulation.
 *)


Theory instSimHelpers
Ancestors
  asmSem planExec stackModel codegenRel stackPlanTypes stackPlanGen venomExecSemantics venomState list rich_list finite_map stackOpSim asmOpSim
Libs
  BasicProvers

(* ===== operand_val stability ===== *)

(* operand_val for Lit is independent of state *)
Theorem operand_val_lit:
  !vs lo w. operand_val vs lo (Lit w) = SOME w
Proof
  simp[operand_val_def]
QED

(* operand_val for Label is independent of state *)
Theorem operand_val_label:
  !vs lo l. operand_val vs lo (Label l) = OPTION_MAP n2w (FLOOKUP lo l)
Proof
  simp[operand_val_def]
QED

(* operand_val for Var x under update_var y: unchanged if x <> y *)
Theorem operand_val_update_var_neq:
  !vs lo x v y.
    x <> y ==>
    operand_val (update_var y v vs) lo (Var x) =
    operand_val vs lo (Var x)
Proof
  rw[operand_val_def, update_var_def, FLOOKUP_UPDATE]
QED

(* operand_val for Var x under update_var x: gets the new value *)
Theorem operand_val_update_var_eq:
  !vs lo x v.
    operand_val (update_var x v vs) lo (Var x) = SOME v
Proof
  rw[operand_val_def, update_var_def, FLOOKUP_UPDATE]
QED

(* operand_val for non-Var operands is independent of vs_vars *)
Theorem operand_val_non_var:
  !vs lo op.
    (~is_var_operand op) ==>
    operand_val (update_var y v vs) lo op = operand_val vs lo op
Proof
  Cases_on `op` >> simp[operand_val_def, update_var_def, is_var_operand_def]
QED

(* General: operand_val stable under update_var for any operand not
   referencing the updated variable *)
Theorem operand_val_update_var:
  !vs lo op y v.
    (case op of Var x => x <> y | _ => T) ==>
    operand_val (update_var y v vs) lo op =
    operand_val vs lo op
Proof
  Cases_on `op` >>
  simp[operand_val_def, update_var_def, FLOOKUP_UPDATE]
QED

(* ===== plan_stack_rel stability under update_var ===== *)

(* If no stack operand references variable y, plan_stack_rel is
   preserved under update_var y. This is the key SSA property:
   under SSA, the output variable is fresh, so no existing stack
   entry references it. *)
Theorem plan_stack_rel_update_var:
  !lo vs ps_stack asm_stack y v.
    plan_stack_rel lo vs ps_stack asm_stack /\
    EVERY (\op. case op of Var x => x <> y | _ => T) ps_stack ==>
    plan_stack_rel lo (update_var y v vs) ps_stack asm_stack
Proof
  rw[plan_stack_rel_def] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\op. case op of Var x => x <> y | _ => T) (REVERSE ps_stack)`
    by simp[EVERY_REVERSE] >>
  `i < LENGTH (REVERSE ps_stack)` by simp[] >>
  `(case EL i (REVERSE ps_stack) of Var x => x <> y | _ => T)` by
    (imp_res_tac EVERY_EL >> fs[]) >>
  metis_tac[operand_val_update_var]
QED

(* ===== plan_spill_rel stability under update_var ===== *)

Theorem plan_spill_rel_update_var:
  !lo vs ps_spilled asm_mem y v.
    plan_spill_rel lo vs ps_spilled asm_mem /\
    (!op. op IN FDOM ps_spilled ==>
       case op of Var x => x <> y | _ => T) ==>
    plan_spill_rel lo (update_var y v vs) ps_spilled asm_mem
Proof
  rw[plan_spill_rel_def] >>
  `op IN FDOM ps_spilled` by fs[flookup_thm] >>
  `case op of Var x => x <> y | _ => T` by res_tac >>
  (* Get: operand_val vs lo op = SOME (word_of_bytes ...) *)
  first_x_assum (qspecl_then [`op`, `off`] mp_tac) >> simp[] >>
  strip_tac >>
  (* Now show operand_val is unchanged under update_var *)
  Cases_on `op` >>
  fs[operand_val_def, update_var_def, FLOOKUP_UPDATE]
QED

(* ===== memory_rel stability under update_var ===== *)

(* memory_rel is about byte memories, not vs_vars, so unaffected *)
Theorem memory_rel_update_var:
  !alloc vs y v.
    memory_rel alloc vs.vs_memory (update_var y v vs).vs_memory
    = memory_rel alloc vs.vs_memory vs.vs_memory
Proof
  rw[update_var_def]
QED

(* memory_rel is reflexive (when there's no spill region to worry about) *)
Theorem memory_rel_refl:
  !alloc mem. memory_rel alloc mem mem
Proof
  rw[memory_rel_def, read_byte_def]
QED

(* ===== venom_asm_rel stability under update_var ===== *)

(* The master stability lemma: update_var with a fresh variable
   preserves venom_asm_rel, given the SSA condition that the
   variable doesn't appear in the plan stack or spills. *)
Theorem venom_asm_rel_update_var:
  !lo ps vs as y v.
    venom_asm_rel lo ps vs as /\
    EVERY (\op. case op of Var x => x <> y | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> y | _ => T) ==>
    venom_asm_rel lo ps (update_var y v vs) as
Proof
  rw[venom_asm_rel_def]
  >- (irule plan_stack_rel_update_var >> simp[])
  >- (irule plan_spill_rel_update_var >> simp[])
  >> fs[update_var_def]
QED

(* ===== venom_asm_rel when operand_val already matches ===== *)

(* plan_stack_rel under update_var when the variable already has the
   right value. Unlike plan_stack_rel_update_var which requires y NOT
   on the stack, this lemma allows Var y on the stack — because
   update_var y v is a no-op on operand_val when FLOOKUP vs.vs_vars y
   was already SOME v.

   Key use case: PARAM instruction at function entry. The asm stack
   already has the param value, and step_inst PARAM does update_var
   with that same value. *)
Theorem plan_stack_rel_update_var_same:
  !lo vs ps_stack asm_stack y v.
    plan_stack_rel lo vs ps_stack asm_stack /\
    operand_val vs lo (Var y) = SOME v ==>
    plan_stack_rel lo (update_var y v vs) ps_stack asm_stack
Proof
  rw[plan_stack_rel_def] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `EL i (REVERSE ps_stack)` >>
  gvs[operand_val_def, update_var_def, FLOOKUP_UPDATE] >>
  rename1 `Var varname` >>
  Cases_on `varname = y` >> gvs[]
QED

(* plan_spill_rel under update_var when the variable already has the
   right value. Same reasoning as plan_stack_rel_update_var_same. *)
Theorem plan_spill_rel_update_var_same:
  !lo vs ps_spilled asm_mem y v.
    plan_spill_rel lo vs ps_spilled asm_mem /\
    operand_val vs lo (Var y) = SOME v ==>
    plan_spill_rel lo (update_var y v vs) ps_spilled asm_mem
Proof
  rw[plan_spill_rel_def] >>
  first_x_assum (qspecl_then [`op`, `off`] mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `op` >>
  gvs[operand_val_def, update_var_def, FLOOKUP_UPDATE] >>
  (* Only Var case remains — either varname = y or not *)
  rename1 `FLOOKUP _ varname` >>
  Cases_on `varname = y` >> gvs[]
QED

(* The master lemma: update_var y v preserves venom_asm_rel when
   operand_val already maps Var y to v.
   This is STRICTLY STRONGER than venom_asm_rel_update_var (which
   requires y not on stack/spills). Here, y MAY be on the stack. *)
Theorem venom_asm_rel_update_var_on_stack:
  !lo ps vs as y v.
    venom_asm_rel lo ps vs as /\
    operand_val vs lo (Var y) = SOME v ==>
    venom_asm_rel lo ps (update_var y v vs) as
Proof
  rw[venom_asm_rel_def]
  >- (irule plan_stack_rel_update_var_same >> metis_tac[])
  >- (irule plan_spill_rel_update_var_same >> metis_tac[])
  >> fs[update_var_def]
QED

(* ===== venom_asm_rel with simultaneous poke + update_var ===== *)

(* ===== plan_stack_rel poke ===== *)

(* Poking an operand that evaluates to the existing asm value preserves
   plan_stack_rel. *)
Theorem plan_stack_rel_poke:
  !lo vs stk as_stk dist op.
    plan_stack_rel lo vs stk as_stk /\
    dist < LENGTH stk /\
    operand_val vs lo op = SOME (EL dist as_stk) ==>
    plan_stack_rel lo vs (stack_poke dist op stk) as_stk
Proof
  rpt gen_tac >> strip_tac >>
  fs[plan_stack_rel_def, stack_poke_def] >>
  rpt strip_tac >>
  simp[EL_REVERSE, LENGTH_LUPDATE, EL_LUPDATE] >>
  IF_CASES_TAC
  >- (
    SUBGOAL_THEN ``i:num = dist`` SUBST_ALL_TAC THENL [decide_tac, gvs[]]
  ) >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_REVERSE]
QED

Theorem plan_stack_rel_poke_swap:
  !lo vs stk as_stk d1 d2 op1 op2.
    plan_stack_rel lo vs stk as_stk /\
    d1 < LENGTH stk /\ d2 < LENGTH stk /\
    operand_val vs lo op1 = SOME (EL d1 as_stk) /\
    operand_val vs lo op2 = SOME (EL d2 as_stk) ==>
    plan_stack_rel lo vs
      (stack_poke d1 op1 (stack_poke d2 op2 stk)) as_stk
Proof
  rpt strip_tac >>
  irule plan_stack_rel_poke >>
  rpt conj_tac
  THENL [
    simp[stack_poke_def, LENGTH_LUPDATE],
    ASM_REWRITE_TAC[],
    irule plan_stack_rel_poke >> ASM_REWRITE_TAC[]
  ]
QED

(* Poke preserves venom_asm_rel when new operand evaluates to existing value *)
Theorem venom_asm_rel_poke:
  !lo ps vs as dist op.
    venom_asm_rel lo ps vs as /\
    dist < LENGTH ps.ps_stack /\
    operand_val vs lo op = SOME (EL dist as.as_stack) ==>
    venom_asm_rel lo
      (ps with ps_stack := stack_poke dist op ps.ps_stack) vs as
Proof
  rpt strip_tac >> gvs[venom_asm_rel_def] >>
  irule plan_stack_rel_poke >> simp[]
QED

(* PHI poke: poke Var out + update_var. Composes update_var then poke. *)
Theorem pre_sub_eq[local]:
  !n m. m < n ==> PRE (n - m) = n - (m + 1)
Proof
  simp[]
QED

Theorem stack_peek_el_reverse[local]:
  !dist stk. dist < LENGTH stk ==>
    stack_peek dist stk = EL dist (REVERSE stk)
Proof
  simp[stack_peek_def, EL_REVERSE, pre_sub_eq]
QED

Theorem venom_asm_rel_poke_update_var:
  !lo ps vs as out v dist.
    venom_asm_rel lo ps vs as /\
    dist < LENGTH ps.ps_stack /\
    operand_val vs lo (stack_peek dist ps.ps_stack) = SOME v /\
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) ==>
    venom_asm_rel lo
      (ps with ps_stack := stack_poke dist (Var out) ps.ps_stack)
      (update_var out v vs) as
Proof
  rpt strip_tac
  >> qpat_x_assum `venom_asm_rel _ _ _ _` mp_tac
  >> simp[venom_asm_rel_def] >> strip_tac
  >> simp[venom_asm_rel_def, update_var_def]
  >> conj_tac
  >- (
    irule plan_stack_rel_poke
    >> simp[operand_val_def, update_var_def, FLOOKUP_UPDATE]
    >> conj_tac
    >- suspend "v_eq"
    >> suspend "psr_uv"
  )
  >> suspend "spill"
QED

Resume venom_asm_rel_poke_update_var[v_eq]:
  qpat_x_assum `operand_val _ _ _ = SOME v` mp_tac
  >> simp[stack_peek_el_reverse]
  >> qpat_x_assum `plan_stack_rel _ _ _ _` mp_tac
  >> simp[plan_stack_rel_def, LET_THM]
  >> strip_tac >> first_x_assum (qspec_then `dist` mp_tac)
  >> simp[]
QED

Resume venom_asm_rel_poke_update_var[psr_uv]:
  once_rewrite_tac[GSYM update_var_def]
  >> irule plan_stack_rel_update_var >> simp[]
QED

Resume venom_asm_rel_poke_update_var[spill]:
  once_rewrite_tac[GSYM update_var_def]
  >> irule plan_spill_rel_update_var >> simp[]
QED

Finalise venom_asm_rel_poke_update_var

(* ===== asm_steps for empty plans ===== *)

(* Empty plan: zero asm instructions, zero steps *)
Theorem asm_steps_empty_plan:
  !lo otp prog as.
    asm_steps lo otp prog 0 as = AsmOK as
Proof
  simp[asm_steps_def]
QED

(* asm_block_at for empty list is always true *)
(* Already in stackOpSimTheory as asm_block_at_nil *)

(* ===== NOP simulation ===== *)

(* NOP: empty plan, identity on Venom state *)
Theorem gen_nop_simulation:
  !fuel ctx lo otp prog inst ps vs as.
    inst.inst_opcode = NOP /\
    venom_asm_rel lo ps vs as ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo otp prog n as = AsmOK as' /\
        venom_asm_rel lo ps vs' as'
Proof
  rw[] >>
  qexistsl_tac [`0`, `as`] >>
  simp[asm_steps_def] >>
  (* step_inst for NOP: dispatches through step_inst_base, returns OK vs *)
  gvs[Once step_inst_def, step_inst_base_def]
QED
