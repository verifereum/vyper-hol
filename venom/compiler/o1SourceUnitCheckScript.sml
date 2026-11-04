(*
 * Computable sufficient check for o1_source_unit_ok on concrete units.
 * TOP-LEVEL: o1_source_unit_check, o1_source_unit_check_sound.
 * Helpers: copy_phi_closed is a closure certificate for copy_phi_var, and
 *   copy_phi_vars iterates the closure rules from the seeds; gas_use_check /
 *   retpc_use_check replace the existentials in gas_use_ok / retpc_use_ok.
 * EVAL cannot decide o1_source_unit_ok itself: entry_fn_first is existential
 * and copy_phi_var is inductive.
 *)
Theory o1SourceUnitCheck
Ancestors
  unitShapeDefs list rich_list

(* ===== Closure certificate for copy_phi_var ===== *)

(* Instructions whose outputs some copy_phi_var rule derives, given seen. *)
Definition copy_phi_fires_def:
  copy_phi_fires origin seen inst <=>
    inst.inst_opcode = origin \/
    (inst.inst_opcode = ASSIGN /\
     case inst.inst_operands of
       [Var y] => MEM y seen
     | _ => F) \/
    (inst.inst_opcode = PHI /\
     EXISTS (\op. case op of Var y => MEM y seen | _ => F)
       inst.inst_operands)
End

Definition copy_phi_closed_def:
  copy_phi_closed origin fn seen <=>
    EVERY (\inst. copy_phi_fires origin seen inst ==>
                  EVERY (\x. MEM x seen) inst.inst_outputs) (fn_insts fn)
End

Theorem copy_phi_closed_sound:
  !origin fn x. copy_phi_var origin fn x ==>
    !seen. copy_phi_closed origin fn seen ==> MEM x seen
Proof
  Induct_on `copy_phi_var` >> rw[copy_phi_closed_def, EVERY_MEM]
  >- (first_x_assum drule >> simp[copy_phi_fires_def])
  >- (rename1 `inst.inst_operands = [Var y]` >>
      `MEM y seen` by metis_tac[] >>
      first_x_assum drule >> simp[copy_phi_fires_def])
  >- (rename1 `MEM (Var y) inst.inst_operands` >>
      `MEM y seen` by metis_tac[] >>
      `copy_phi_fires origin seen inst`
        by (simp[copy_phi_fires_def, EXISTS_MEM] >>
            disj2_tac >> qexists_tac `Var y` >> simp[]) >>
      metis_tac[])
QED

(* One round of the copy_phi_var rules. Iterating it stops at the first round
   that adds nothing; copy_phi_closed re-checks the result rather than
   trusting the iteration, so the fuel only bounds evaluation. *)
Definition copy_phi_step_def:
  copy_phi_step origin fn seen =
    seen ++ FLAT (MAP (\inst. if copy_phi_fires origin seen inst
                           then FILTER (\x. ~MEM x seen) inst.inst_outputs
                           else []) (fn_insts fn))
End

Definition copy_phi_iter_def:
  copy_phi_iter origin fn (n:num) seen =
    if n = 0 then seen else
    let seen' = copy_phi_step origin fn seen in
    if LENGTH seen' = LENGTH seen then seen
    else copy_phi_iter origin fn (n - 1) seen'
Termination
  WF_REL_TAC `measure (\(origin, fn, n, seen). n)`
End

Definition copy_phi_vars_def:
  copy_phi_vars origin fn =
    copy_phi_iter origin fn (SUC (LENGTH (fn_insts fn))) []
End

(* ===== Opaque uses ===== *)

Definition gas_use_check_def:
  gas_use_check inst x <=>
    inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
    ((inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
     case inst.inst_operands of
       [] => F
     | op :: rest => op = Var x /\ ~MEM (Var x) rest)
End

Definition retpc_use_check_def:
  retpc_use_check inst x <=>
    inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
    (MEM inst.inst_opcode [RET; RETFMP; DRET] /\ inst.inst_operands <> [] /\
     LAST inst.inst_operands = Var x /\
     ~MEM (Var x) (FRONT inst.inst_operands))
End

Theorem gas_use_check_sound:
  gas_use_check inst x ==> gas_use_ok inst x
Proof
  rw[gas_use_check_def, gas_use_ok_def] >> Cases_on `inst.inst_operands` >> gvs[]
QED

Theorem retpc_use_check_sound:
  retpc_use_check inst x ==> retpc_use_ok inst x
Proof
  rw[retpc_use_check_def, retpc_use_ok_def] >> simp[] >>
  qexists_tac `FRONT inst.inst_operands` >>
  metis_tac[APPEND_FRONT_LAST]
QED

Definition opaque_use_check_def:
  opaque_use_check fn <=>
    let gas = copy_phi_vars GAS fn;
        retpc = copy_phi_vars RETPC_PARAM fn in
    copy_phi_closed GAS fn gas /\ copy_phi_closed RETPC_PARAM fn retpc /\
    EVERY (\inst. EVERY (\op.
      case op of
        Var x =>
          (MEM x gas ==> gas_use_check inst x) /\
          (MEM x retpc ==> retpc_use_check inst x)
      | _ => T)
      inst.inst_operands) (fn_insts fn)
End

Theorem opaque_use_check_sound:
  opaque_use_check fn ==> opaque_use_ok fn
Proof
  rw[opaque_use_check_def, opaque_use_ok_def, gas_var_def, retpc_var_def,
     EVERY_MEM, LET_THM] >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  metis_tac[copy_phi_closed_sound, gas_use_check_sound, retpc_use_check_sound]
QED

(* A RET's last operand must be a RETPC_PARAM output of the entry block
   itself (a seed), no PHI may read a variable of the return-PC closure,
   only RETPC_PARAM may write one, and at most one instruction writes
   each: enough for raw units, which copy no return PC and have no PHI. *)
Definition retpc_shape_check_def:
  retpc_shape_check fn <=>
    let retpc = copy_phi_vars RETPC_PARAM fn in
    copy_phi_closed RETPC_PARAM fn retpc /\
    EVERY (\inst.
      (MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
         inst.inst_operands <> [] /\
         case (LAST inst.inst_operands, fn.fn_blocks) of
           (Var x, bb :: _) => EXISTS (\i. i.inst_opcode = RETPC_PARAM /\
                                           MEM x i.inst_outputs)
                                 bb.bb_instructions
         | _ => F) /\
      (inst.inst_opcode = PHI ==>
         EVERY (\op. case op of Var y => ~MEM y retpc | _ => T)
           inst.inst_operands) /\
      EVERY (\x. MEM x retpc ==> inst.inst_opcode = RETPC_PARAM)
        inst.inst_outputs) (fn_insts fn) /\
    EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) <= 1)
      retpc
End

Theorem FILTER_LENGTH_LE_1_unique[local]:
  !P l i j. LENGTH (FILTER P l) <= 1 /\ MEM i l /\ P i /\ MEM j l /\ P j ==>
            i = j
Proof
  rpt strip_tac >>
  `MEM i (FILTER P l) /\ MEM j (FILTER P l)` by simp[MEM_FILTER] >>
  Cases_on `FILTER P l` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem retpc_shape_check_sound:
  retpc_shape_check fn ==> retpc_shape_ok fn
Proof
  rewrite_tac[retpc_shape_check_def, LET_THM] >> strip_tac >>
  fs[EVERY_MEM] >>
  `!x. retpc_var fn x ==> MEM x (copy_phi_vars RETPC_PARAM fn)`
    by metis_tac[retpc_var_def, copy_phi_closed_sound] >>
  `!x. retpc_var (reachable_fn fn) x ==>
       MEM x (copy_phi_vars RETPC_PARAM fn)`
    by metis_tac[reachable_retpc_var] >>
  rewrite_tac[retpc_shape_ok_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (`inst.inst_opcode <> PHI` by gvs[] >>
      `MEM inst (fn_insts fn)` by metis_tac[reachable_fn_insts_nonphi] >>
      qpat_x_assum `!i. MEM i (fn_insts _) ==> _` (qspec_then `inst` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `_ \/ _ \/ _ ==> _` mp_tac >>
      impl_tac >- fs[] >> strip_tac >>
      Cases_on `LAST inst.inst_operands` >> gvs[] >>
      Cases_on `fn.fn_blocks` >> gvs[EXISTS_MEM] >>
      rename1 `LAST inst.inst_operands = Var r` >>
      qexistsl_tac [`FRONT inst.inst_operands`, `r`] >>
      (conj_tac >- metis_tac[APPEND_FRONT_LAST]) >>
      simp[retpc_var_def] >> irule copy_phi_var_seed >>
      qexists_tac `i` >> simp[] >>
      irule entry_insts_reachable >> simp[])
  >- (qspecl_then [`fn`, `inst`, `Var x`] mp_tac reachable_fn_insts_operand >>
      simp[] >> strip_tac >>
      `MEM x (copy_phi_vars RETPC_PARAM fn)` by res_tac >>
      qpat_x_assum `!i. MEM i (fn_insts _) ==> _` (qspec_then `i` mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum (qspec_then `Var x` mp_tac) >> simp[])
  >- (disj1_tac >>
      `MEM x (copy_phi_vars RETPC_PARAM fn)` by res_tac >>
      qpat_x_assum `!i. MEM i (fn_insts _) ==> _` (qspec_then `inst` mp_tac) >>
      simp[] >> metis_tac[])
  >> `MEM x (copy_phi_vars RETPC_PARAM fn)` by res_tac >>
  irule FILTER_LENGTH_LE_1_unique >>
  qexistsl_tac [`\i. MEM x i.inst_outputs`, `fn_insts fn`] >>
  simp[] >> metis_tac[]
QED

(* ===== Unit check ===== *)

Definition fn_shape_check_def:
  fn_shape_check fn <=>
    fn_entry_label fn = SOME fn.fn_name /\ opaque_use_check fn /\
    retpc_shape_check fn /\ EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks /\
    EVERY inst_shape_ok (fn_insts fn) /\ call_checks_ok fn
End

Theorem fn_shape_check_sound:
  fn_shape_check fn ==> fn_shape_ok fn
Proof
  rw[fn_shape_check_def, fn_shape_ok_def, opaque_use_check_sound,
     retpc_shape_check_sound]
QED

(* Checking every non-head function is stronger than internal_termination_ok
   only when the head function also occurs in the tail. *)
Definition o1_source_unit_check_def:
  o1_source_unit_check unit <=>
    unit.cu_context.ctx_functions <> [] /\
    unit.cu_context.ctx_entry =
      SOME (HD unit.cu_context.ctx_functions).fn_name /\
    entry_fn_no_ret (HD unit.cu_context.ctx_functions) /\
    get_params (HD (HD unit.cu_context.ctx_functions).fn_blocks).bb_instructions = [] /\
    EVERY fn_shape_check unit.cu_context.ctx_functions /\
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts fn))
          unit.cu_context.ctx_functions /\
    EVERY (\fn. EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn))
          (TL unit.cu_context.ctx_functions) /\
    EVERY first_block_no_preds unit.cu_context.ctx_functions
End

Theorem o1_source_unit_check_sound:
  o1_source_unit_check unit ==> o1_source_unit_ok unit
Proof
  rw[o1_source_unit_check_def, o1_source_unit_ok_def, unit_shape_ok_def,
     entry_fn_first_def, internal_termination_ok_def]
  >~ [`EVERY fn_shape_ok _`]
  >- (gvs[EVERY_MEM] >> metis_tac[fn_shape_check_sound]) >>
  Cases_on `unit.cu_context.ctx_functions` >> gvs[EVERY_MEM] >> metis_tac[]
QED
