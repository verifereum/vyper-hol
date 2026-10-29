(* Task-local reclaim queries.  Operand lists are in HOL semantic order.
 * Reference: cd74ce4f, fmp_lowering.py:603-678.  These queries do not
 * assert an operational memory-safety invariant. *)
Theory fmpAliasDefs
Ancestors
  fmpAnalysisDefs livenessDefs memLocDefs rich_list

(* Shared syntactic helpers live below reclaim transfer, so the indexed
 * production transfer can consume this theory without a dependency cycle. *)
Definition fmp_single_output_def:
  fmp_single_output (inst:instruction) =
    case inst.inst_outputs of [v] => SOME v | _ => NONE
End

Definition fmp_transparent_opcode_def:
  fmp_transparent_opcode op <=>
    op = ASSIGN \/ op = ADD \/ op = SUB \/ op = PHI
End

Definition fmp_inst_uses_any_def:
  fmp_inst_uses_any vars inst <=>
    EXISTS (\v. MEM v (inst_uses inst)) vars
End

Definition fmp_access_operands_def:
  fmp_access_operands NONE = [] /\
  fmp_access_operands (SOME a) =
    [a.iao_ofst] ++ OPTION_TO_LIST a.iao_size ++
    (if a.iao_max_size = a.iao_size then []
     else OPTION_TO_LIST a.iao_max_size)
End

Definition fmp_safe_operands_def:
  fmp_safe_operands inst =
    fmp_access_operands (mem_read_ops inst) ++
    fmp_access_operands (mem_write_ops inst)
End

Definition fmp_pointer_propagation_def:
  fmp_pointer_propagation op <=>
    fmp_transparent_opcode op \/ MEM op [BUMP; DALLOCA; ALLOCA]
End

(* Return occurrences, not a set: a safe address occurrence does not excuse
 * another occurrence used as a stored value. *)
Definition fmp_escaping_operands_def:
  fmp_escaping_operands inst =
    if fmp_pointer_propagation inst.inst_opcode then [] else
    FILTER (\v.
      LENGTH (FILTER ($= (Var v)) (fmp_safe_operands inst)) <
      LENGTH (FILTER ($= v) (inst_uses inst))) (inst_uses inst)
End

Definition fmp_capture_step_def:
  fmp_capture_step [] vars = vars /\
  fmp_capture_step (inst::rest) vars =
    fmp_capture_step rest
      (if fmp_transparent_opcode inst.inst_opcode /\
          LENGTH inst.inst_outputs = 1 /\ fmp_inst_uses_any vars inst
       then list_union inst.inst_outputs vars else vars)
End

Definition fmp_capture_closed_def:
  fmp_capture_closed insts vars <=>
    EVERY (\inst. fmp_transparent_opcode inst.inst_opcode /\
      LENGTH inst.inst_outputs = 1 /\ fmp_inst_uses_any vars inst ==>
      EVERY (\v. MEM v vars) inst.inst_outputs) insts
End

(* The bounded iteration is checked, so failure never presents a partial
 * closure as complete.  Roots are current-state captures at the use site. *)
Definition fmp_capture_closure_def:
  fmp_capture_closure insts root =
    let vars = FUNPOW (fmp_capture_step insts) (LENGTH insts) [root] in
    if fmp_capture_closed insts vars then SOME vars else NONE
End

Definition fmp_capture_query_veto_def:
  fmp_capture_query_veto insts live root =
    case fmp_capture_closure insts root of
      NONE => T
    | SOME vars =>
        EXISTS (\v. MEM v live) vars \/
        EXISTS (\inst. EXISTS (\v. MEM v vars)
          (fmp_escaping_operands inst)) insts
End

(* Allocation identities project away offsets, not allocation sites.  Missing
 * variables have the reference's empty pointer set.  inst_id is used only
 * after checking uniqueness within this instruction list. *)
Type fmp_base_env = ``:(string,num list) fmap``

Definition fmp_bases_def:
  fmp_bases (env:fmp_base_env) v =
    case FLOOKUP env v of NONE => [] | SOME ids => ids
End

Definition fmp_operand_bases_def:
  fmp_operand_bases env (Var v) = fmp_bases env v /\
  fmp_operand_bases env (Lit w) = [] /\
  fmp_operand_bases env (Label l) = []
End

Definition fmp_arithmetic_bases_def:
  fmp_arithmetic_bases op lhs rhs =
    if lhs <> [] /\ rhs = [] then lhs
    else if op = ADD /\ rhs <> [] /\ lhs = [] then rhs else []
End

Definition fmp_generated_bases_def:
  fmp_generated_bases env inst =
    if MEM inst.inst_opcode [ALLOCA; DALLOCA; BUMP] then [inst.inst_id]
    else if inst.inst_opcode = ASSIGN then
      (case inst.inst_operands of [x] => fmp_operand_bases env x | _ => [])
    else if inst.inst_opcode = PHI then
      FOLDL list_union [] (MAP (fmp_operand_bases env) inst.inst_operands)
    else if inst.inst_opcode = ADD \/ inst.inst_opcode = SUB then
      (case inst.inst_operands of
         [lhs;rhs] => fmp_arithmetic_bases inst.inst_opcode
           (fmp_operand_bases env lhs) (fmp_operand_bases env rhs)
       | _ => [])
    else []
End

Definition fmp_base_output_def:
  fmp_base_output inst =
    if inst.inst_opcode = BUMP then
      (case inst.inst_outputs of [ptr;runner] => SOME ptr | _ => NONE)
    else fmp_single_output inst
End

Definition fmp_accumulate_bases_def:
  fmp_accumulate_bases env out ids =
    env |+ (out,list_union (fmp_bases env out) ids)
End

Definition fmp_base_transfer_def:
  fmp_base_transfer inst env =
    case fmp_base_output inst of NONE => env
    | SOME out => fmp_accumulate_bases env out (fmp_generated_bases env inst)
End

Definition fmp_base_sweep_def:
  fmp_base_sweep [] env = env /\
  fmp_base_sweep (inst::rest) env =
    fmp_base_sweep rest (fmp_base_transfer inst env)
End

Definition fmp_base_closed_def:
  fmp_base_closed insts env <=>
    EVERY (\inst. case fmp_base_output inst of NONE => T
      | SOME out => EVERY (\id. MEM id (fmp_bases env out))
          (fmp_generated_bases env inst)) insts
End

Definition fmp_base_env_eq_def:
  fmp_base_env_eq insts env1 env2 <=>
    EVERY (\v.
      EVERY (\id. MEM id (fmp_bases env2 v)) (fmp_bases env1 v) /\
      EVERY (\id. MEM id (fmp_bases env1 v)) (fmp_bases env2 v))
      (FLAT (MAP (\inst. inst.inst_outputs) insts))
End

(* Stop as soon as the ordered sweep is stable; retain a bounded total
 * fallback.  Acceptance below still validates the returned environment. *)
Definition fmp_base_iter_def:
  fmp_base_iter 0 insts env = env /\
  fmp_base_iter (SUC fuel) insts env =
    let next = fmp_base_sweep insts env in
    if fmp_base_env_eq insts next env then env else fmp_base_iter fuel insts next
End

Definition fmp_base_analyze_def:
  fmp_base_analyze insts =
    let vars = FLAT (MAP (\inst. inst.inst_outputs) insts) in
    let env = fmp_base_iter (LENGTH vars * LENGTH insts + 1) insts FEMPTY in
    if ALL_DISTINCT (MAP (\inst. inst.inst_id) insts) /\
       fmp_base_env_eq insts (fmp_base_sweep insts env) env /\
       fmp_base_closed insts env
    then SOME env else NONE
End

Definition fmp_dalloca_query_def:
  fmp_dalloca_query insts env v =
    case fmp_bases env v of
      [id] => if EXISTS (\inst. inst.inst_id = id /\
                 inst.inst_opcode = DALLOCA) insts then SOME id else NONE
    | _ => NONE
End

Definition fmp_allocation_live_def:
  fmp_allocation_live env insts live id <=>
    EXISTS (\v. MEM id (fmp_bases env v)) live \/
    EXISTS (\inst. EXISTS (\v. MEM id (fmp_bases env v))
      (fmp_escaping_operands inst)) insts
End

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpAliasDefs");
