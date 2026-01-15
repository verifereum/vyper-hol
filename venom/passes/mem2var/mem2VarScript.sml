(*
 * Mem2Var Pass
 *
 * Port of venom/passes/mem2var.py.
 *)

Theory mem2Var
Ancestors
  list
  ASCIInumbers
  irOps
  dfgAnalysis livenessAnalysis
  instUpdater compilerState

Definition fmap_to_alist_def:
  fmap_to_alist m =
    MAP (λk. (k, THE (FLOOKUP m k))) (SET_TO_LIST (FDOM m))
End

Definition mk_alloca_varname_def:
  mk_alloca_varname v count =
    let base = strip_var_prefix v in
    (STRCAT "alloca_" (STRCAT base (STRCAT "_" (num_to_dec_string count))), count + 1)
End

Definition any_use_opcode_def:
  any_use_opcode fn ids op =
    EXISTS
      (λiid. case lookup_inst_in_function iid fn of
               SOME inst => inst.inst_opcode = op
             | NONE => F)
      ids
End

Definition all_uses_opcode_in_def:
  all_uses_opcode_in fn ids ops =
    EVERY
      (λiid. case lookup_inst_in_function iid fn of
               SOME inst => MEM inst.inst_opcode ops
             | NONE => F)
      ids
End

Definition mem2var_fix_adds_aux_def:
  mem2var_fix_adds_aux 0 updater inst_id = updater /\
  mem2var_fix_adds_aux (SUC fuel) updater inst_id =
    case lookup_inst_in_function inst_id updater.iu_fn of
      NONE => updater
    | SOME inst =>
        case inst_output inst of
          NONE => updater
        | SOME out =>
            let uses = dfg_get_uses updater.iu_dfg out in
            FOLDL
              (λacc iid.
                 case lookup_inst_in_function iid acc.iu_fn of
                   NONE => acc
                 | SOME use_inst =>
                     if use_inst.inst_opcode <> ADD then acc
                     else
                       (case use_inst.inst_operands of
                          op1::op2::_ =>
                            let other = if op1 = Var out then op2 else op1 in
                            let acc1 =
                              inst_updater_update acc use_inst ADD [Var out; other] NONE in
                            mem2var_fix_adds_aux fuel acc1 use_inst.inst_id
                        | _ => acc))
              updater uses
End

Definition mem2var_fix_adds_def:
  mem2var_fix_adds updater inst =
    let fuel = LENGTH (fn_instructions_list updater.iu_fn) + 1 in
    mem2var_fix_adds_aux fuel updater inst.inst_id
End

Definition mem2var_process_alloca_def:
  mem2var_process_alloca updater inst var count =
    case inst_output inst of
      NONE => (updater, count)
    | SOME out =>
        let (varname, count1) = mk_alloca_varname var count in
        let uses = dfg_get_uses updater.iu_dfg out in
        if any_use_opcode updater.iu_fn uses ADD then
          (mem2var_fix_adds updater inst, count1)
        else if ~all_uses_opcode_in updater.iu_fn uses [MSTORE; MLOAD; RETURN] then
          (updater, count1)
        else
          (case inst.inst_operands of
             Lit w :: _ =>
               let size = w2n w in
               let updater' =
                 FOLDL
                   (λacc iid.
                      case lookup_inst_in_function iid acc.iu_fn of
                        NONE => acc
                      | SOME use_inst =>
                          if use_inst.inst_opcode = MSTORE then
                            if size = 32 then
                              (case use_inst.inst_operands of
                                 val::_ =>
                                   inst_updater_mk_assign acc use_inst val (SOME varname)
                               | _ => acc)
                            else acc
                          else if use_inst.inst_opcode = MLOAD then
                            if size = 32 then
                              inst_updater_mk_assign acc use_inst (Var varname) NONE
                            else acc
                          else if use_inst.inst_opcode = RETURN then
                            let acc1 =
                              if size <= 32 then
                                FST (inst_updater_add_before acc use_inst MSTORE
                                       [Var varname; Var out])
                              else acc in
                            (case use_inst.inst_operands of
                               op1::op2::rest =>
                                 inst_updater_update acc1 use_inst RETURN
                                   (op1 :: Var out :: rest) NONE
                             | _ => acc1)
                          else acc)
                   updater uses in
               (updater', count1)
           | _ => (updater, count1))
End

Definition mem2var_process_palloca_def:
  mem2var_process_palloca updater inst var count =
    case inst_output inst of
      NONE => (updater, count)
    | SOME out =>
        let (varname, count1) = mk_alloca_varname var count in
        let uses = dfg_get_uses updater.iu_dfg out in
        if any_use_opcode updater.iu_fn uses ADD then
          (mem2var_fix_adds updater inst, count1)
        else if ~all_uses_opcode_in updater.iu_fn uses [MSTORE; MLOAD] then
          (updater, count1)
        else
          (case inst.inst_operands of
             size_lit :: alloca_id :: _ =>
               let target_var =
                 case alloca_id of
                   Lit w =>
                     (case fn_get_param_by_id updater.iu_fn (w2n w) of
                        NONE =>
                          (case inst_updater_add_after updater inst MLOAD [Var out] of
                             (up, SOME v) => (up, v)
                           | (up, NONE) => (up, varname))
                      | SOME p =>
                          let up =
                            inst_updater_update updater inst ASSIGN [Var p.param_func_var]
                              (SOME varname) in
                          (up, varname))
                 | _ => (updater, varname) in
               let (up1, stack_var) = target_var in
               (case size_lit of
                  Lit w =>
                    let size = w2n w in
                    let updater' =
                      FOLDL
                        (λacc iid.
                           case lookup_inst_in_function iid acc.iu_fn of
                             NONE => acc
                           | SOME use_inst =>
                               if use_inst.inst_opcode = MSTORE then
                                 if size = 32 then
                                   (case use_inst.inst_operands of
                                      val::_ =>
                                        inst_updater_mk_assign acc use_inst val (SOME stack_var)
                                    | _ => acc)
                                 else acc
                               else if use_inst.inst_opcode = MLOAD then
                                 if size = 32 then
                                   inst_updater_mk_assign acc use_inst (Var stack_var) NONE
                                 else acc
                               else acc)
                        up1 uses in
                    (updater', count1)
                | _ => (up1, count1))
           | _ => (updater, count1))
End

Definition mem2var_process_calloca_def:
  mem2var_process_calloca updater inst count =
    (mem2var_fix_adds updater inst, count)
End

Definition mem2var_process_output_def:
  mem2var_process_output updater count (var, iid) =
    case lookup_inst_in_function iid updater.iu_fn of
      NONE => (updater, count)
    | SOME inst =>
        if inst.inst_opcode = ALLOCA then mem2var_process_alloca updater inst var count
        else if inst.inst_opcode = PALLOCA then mem2var_process_palloca updater inst var count
        else if inst.inst_opcode = CALLOCA then mem2var_process_calloca updater inst count
        else (updater, count)
End

Definition mem2var_function_def:
  mem2var_function fn =
    let dfg = dfg_analyze fn in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let outputs = fmap_to_alist dfg.dfg_outputs in
    let (updater', _) =
      FOLDL (λacc kv. mem2var_process_output (FST acc) (SND acc) kv)
            (updater, 0) outputs in
    updater'.iu_fn
End

Definition mem2var_context_def:
  mem2var_context ctx =
    ctx with ctx_functions := MAP mem2var_function ctx.ctx_functions
End

val _ = export_theory();
