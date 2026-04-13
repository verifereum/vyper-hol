(*
 * Emit Step Simulation
 *
 * Proves that the SOEmit step (the actual opcode execution) preserves
 * venom_asm_rel. The plan's pop-operands/push-outputs (steps 5-6 of
 * generate_regular_inst_plan) model what the asm instruction does.
 *
 * Key results:
 *   emit_popn_push1_sim — generic: any 1-step that pops n, pushes 1 result
 *   emit_pure2_sim      — binary pure ops (ADD, SUB, MUL, ...)
 *   emit_pure1_sim      — unary pure ops (ISZERO, NOT)
 *   emit_pure3_sim      — ternary pure ops (ADDMOD, MULMOD)
 *
 * Strategy: compose plan_stack_rel_pop + plan_stack_rel_update_var +
 *   plan_stack_rel_push. The tricky index arithmetic is handled by
 *   existing stackOpSim lemmas.
 *)

Theory emitSim
Ancestors
  codegenRel asmSem planExec stackPlanGen stackPlanTypes stackModel
  venomExecSemantics venomState venomInst
  instSimHelpers stackOpSim blockSimHelpers
  list rich_list finite_map
Libs
  BasicProvers

(* =========================================================================
   Connection: eval_operand vs operand_val
   ========================================================================= *)

Theorem eval_operand_var_eq:
  !x vs lo.
    operand_val vs lo (Var x) = eval_operand (Var x) vs
Proof
  simp[operand_val_def, eval_operand_def, lookup_var_def]
QED

Theorem eval_operand_lit_eq:
  !w vs lo.
    operand_val vs lo (Lit w) = eval_operand (Lit w) vs
Proof
  simp[operand_val_def, eval_operand_def]
QED

(* For non-Label operands, operand_val and eval_operand agree *)
Theorem operand_val_eq_eval:
  !vs lo op.
    ~is_label_operand op ==>
    operand_val vs lo op = eval_operand op vs
Proof
  Cases_on `op` >>
  simp[operand_val_def, eval_operand_def, lookup_var_def,
       is_label_operand_def]
QED

(* If both are SOME, values must agree (for non-Label operands) *)
Theorem operand_eval_agree:
  !vs lo op a v.
    ~is_label_operand op /\
    operand_val vs lo op = SOME a /\
    eval_operand op vs = SOME v ==>
    a = v
Proof
  rpt strip_tac >>
  imp_res_tac operand_val_eq_eval >> gvs[]
QED

(* =========================================================================
   Core helper: plan_stack_rel after pop-n / push-1-output
   ========================================================================= *)

Theorem plan_stack_rel_emit_step:
  !lo vs ps_stack asm_stack n out result.
    plan_stack_rel lo vs ps_stack asm_stack /\
    n <= LENGTH ps_stack /\
    EVERY (\op. case op of Var x => x <> out | _ => T)
      (TAKE (LENGTH ps_stack - n) ps_stack) ==>
    plan_stack_rel lo (update_var out result vs)
      (SNOC (Var out) (TAKE (LENGTH ps_stack - n) ps_stack))
      (result :: DROP n asm_stack)
Proof
  rpt strip_tac >>
  `plan_stack_rel lo vs
     (TAKE (LENGTH ps_stack - n) ps_stack)
     (DROP n asm_stack)` by
    (irule plan_stack_rel_pop >> simp[]) >>
  `plan_stack_rel lo (update_var out result vs)
     (TAKE (LENGTH ps_stack - n) ps_stack)
     (DROP n asm_stack)` by
    (irule plan_stack_rel_update_var >> simp[]) >>
  irule plan_stack_rel_push >> simp[] >>
  simp[operand_val_update_var_eq]
QED

(* =========================================================================
   exec_pure decomposition lemmas (extract update_var from exec_pureN)
   ========================================================================= *)

Theorem exec_pure2_update_var:
  !f inst vs vs' op1 op2 out.
    exec_pure2 f inst vs = OK vs' /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] ==>
    ?v1 v2.
      eval_operand op1 vs = SOME v1 /\
      eval_operand op2 vs = SOME v2 /\
      vs' = update_var out (f v1 v2) vs
Proof
  rw[exec_pure2_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[] >>
  Cases_on `eval_operand op2 vs` >> gvs[]
QED

Theorem exec_pure1_update_var:
  !f inst vs vs' op1 out.
    exec_pure1 f inst vs = OK vs' /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] ==>
    ?v1.
      eval_operand op1 vs = SOME v1 /\
      vs' = update_var out (f v1) vs
Proof
  rw[exec_pure1_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[]
QED

Theorem exec_pure3_update_var:
  !f inst vs vs' op1 op2 op3 out.
    exec_pure3 f inst vs = OK vs' /\
    inst.inst_operands = [op1; op2; op3] /\
    inst.inst_outputs = [out] ==>
    ?v1 v2 v3.
      eval_operand op1 vs = SOME v1 /\
      eval_operand op2 vs = SOME v2 /\
      eval_operand op3 vs = SOME v3 /\
      vs' = update_var out (f v1 v2 v3) vs
Proof
  rw[exec_pure3_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[] >>
  Cases_on `eval_operand op2 vs` >> gvs[] >>
  Cases_on `eval_operand op3 vs` >> gvs[]
QED

(* =========================================================================
   Generic emit: 1 asm step that pops n and pushes 1 result

   This is the shared core for all pure emit lemmas.
   The caller provides:
   - The asm result of the step (must be AsmOK with stack = result :: DROP n)
   - The Venom result (must be update_var out result vs)
   ========================================================================= *)

Theorem emit_popn_push1_sim:
  !lo o2pc prog ps vs as n out result.
    venom_asm_rel lo ps vs as /\
    n <= LENGTH ps.ps_stack /\
    (* SSA freshness *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    (* Asm instruction executes: pops n, pushes result *)
    as.as_pc < LENGTH prog /\
    asm_step lo o2pc (EL as.as_pc prog) as =
      AsmOK (asm_next (as with as_stack := result :: DROP n as.as_stack))
    ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop n ps.ps_stack))
        (update_var out result vs) as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `asm_next (as with as_stack :=
    result :: DROP n as.as_stack)` >>
  rpt conj_tac
  >- (
    (* asm_steps 1 = AsmOK *)
    PURE_REWRITE_TAC[GSYM (EVAL ``SUC 0``)] >>
    simp[Once asm_steps_def] >>
    simp[asm_steps_def]
  )
  >- (
    simp[asm_next_def] >>
    qpat_x_assum `venom_asm_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE[venom_asm_rel_def]) >>
    simp[venom_asm_rel_def, update_var_def] >>
    rpt conj_tac
    >- (
      simp[stack_push_def, stack_pop_def, GSYM update_var_def] >>
      irule plan_stack_rel_emit_step >> simp[] >>
      irule EVERY_TAKE >> simp[]
    )
    >- (
      simp[GSYM update_var_def] >>
      irule plan_spill_rel_update_var >> simp[]
    )
  )
  >- simp[asm_next_def]
QED

(* =========================================================================
   Stack top extraction from plan_stack_rel

   When plan stack ends with [opN; ...; op1], asm stack starts with
   v1 :: ... :: vN :: rest where vi = operand_val vs lo opi.
   ========================================================================= *)

Theorem asm_stack_top1_from_plan:
  !lo vs ps_stack as_stack op1 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op1] ==>
    ?v1 rest.
      as_stack = v1 :: rest /\
      operand_val vs lo op1 = SOME v1
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  simp[REVERSE_APPEND]
QED

Theorem asm_stack_top2_from_plan:
  !lo vs ps_stack as_stack op1 op2 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op2; op1] ==>
    ?v1 v2 rest.
      as_stack = v1 :: v2 :: rest /\
      operand_val vs lo op1 = SOME v1 /\
      operand_val vs lo op2 = SOME v2
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  conj_tac
  >- (
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND]
  )
  >- (
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
QED

Theorem asm_stack_top3_from_plan:
  !lo vs ps_stack as_stack op1 op2 op3 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op3; op2; op1] ==>
    ?v1 v2 v3 rest.
      as_stack = v1 :: v2 :: v3 :: rest /\
      operand_val vs lo op1 = SOME v1 /\
      operand_val vs lo op2 = SOME v2 /\
      operand_val vs lo op3 = SOME v3
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  rpt conj_tac
  >- (
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND]
  )
  >- (
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
  >- (
    first_x_assum (qspec_then `2` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
QED

(* =========================================================================
   Pure binary emit simulation (exec_pure2 / asm_binop)

   Covers: ADD, SUB, MUL, DIV, SDIV, MOD, SMOD, EXP, LT, GT, SLT, SGT,
           EQ, AND, OR, XOR, SHL, SHR, SAR, SIGNEXTEND, BYTE
   ========================================================================= *)

Theorem emit_pure2_sim:
  !lo o2pc prog ps vs as f name inst op1 op2 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\ ~is_label_operand op2 /\
    (* Plan stack has operands at top *)
    ps.ps_stack = base ++ [op2; op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    (* Asm instruction *)
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_binop f as /\
    (* Venom execution *)
    exec_pure2 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 2 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure2_update_var >> strip_tac >>
  (* Get asm stack top 2 = operand values *)
  `?a b rest. as.as_stack = a :: b :: rest /\
    operand_val vs lo op1 = SOME a /\
    operand_val vs lo op2 = SOME b` by (
    irule asm_stack_top2_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  (* Bridge operand_val to eval_operand *)
  `a = v1` by metis_tac[operand_eval_agree] >>
  `b = v2` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Now apply the generic emit sim *)
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_binop_def]
QED

(* =========================================================================
   Pure unary emit simulation (exec_pure1 / asm_unop)
   ========================================================================= *)

Theorem emit_pure1_sim:
  !lo o2pc prog ps vs as f name inst op1 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\
    (* Plan stack has operand at top *)
    ps.ps_stack = base ++ [op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_unop f as /\
    exec_pure1 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 1 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure1_update_var >> strip_tac >>
  `?a rest. as.as_stack = a :: rest /\
    operand_val vs lo op1 = SOME a` by (
    irule asm_stack_top1_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  `a = v1` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_unop_def]
QED

(* =========================================================================
   Pure ternary emit simulation (exec_pure3 / asm_ternop)
   ========================================================================= *)

Theorem emit_pure3_sim:
  !lo o2pc prog ps vs as f name inst op1 op2 op3 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1; op2; op3] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\ ~is_label_operand op2 /\ ~is_label_operand op3 /\
    (* Plan stack has operands at top *)
    ps.ps_stack = base ++ [op3; op2; op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_ternop f as /\
    exec_pure3 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 3 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure3_update_var >> strip_tac >>
  `?a b c rest. as.as_stack = a :: b :: c :: rest /\
    operand_val vs lo op1 = SOME a /\
    operand_val vs lo op2 = SOME b /\
    operand_val vs lo op3 = SOME c` by (
    irule asm_stack_top3_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  `a = v1` by metis_tac[operand_eval_agree] >>
  `b = v2` by metis_tac[operand_eval_agree] >>
  `c = v3` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_ternop_def]
QED

