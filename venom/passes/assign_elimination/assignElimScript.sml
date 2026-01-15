(*
 * Assign Elimination Pass
 *
 * Port of venom/passes/assign_elimination.py.
 *)

Theory assignElim
Ancestors
  list pred_set
  irOps dfgAnalysis instUpdater compilerState

Definition fmap_to_alist_def:
  fmap_to_alist m =
    MAP (λk. (k, THE (FLOOKUP m k))) (SET_TO_LIST (FDOM m))
End

Definition inst_is_phi_def:
  inst_is_phi inst <=> inst.inst_opcode = PHI
End

Definition uses_contain_phi_def:
  uses_contain_phi fn uses =
    EXISTS
      (λiid. case lookup_inst_in_function iid fn of
               SOME inst => inst_is_phi inst
             | NONE => F)
      uses
End

Definition assign_elim_process_store_def:
  assign_elim_process_store updater inst var new_var =
    let uses_new = dfg_get_uses updater.iu_dfg new_var in
    if uses_contain_phi updater.iu_fn uses_new then updater
    else
      let uses_old = dfg_get_uses updater.iu_dfg var in
      if uses_contain_phi updater.iu_fn uses_old then updater
      else
        let updater' =
          FOLDL
            (λacc iid.
               case lookup_inst_in_function iid acc.iu_fn of
                 NONE => acc
               | SOME use_inst =>
                   inst_updater_update_operands acc use_inst [(Var var, Var new_var)])
            updater uses_old in
        inst_updater_remove updater' inst
End

Definition assign_elim_function_def:
  assign_elim_function fn =
    let dfg = dfg_analyze fn in
    let updater =
      <| iu_dfg := dfg; iu_fn := fn; iu_state := init_state_for_function fn |> in
    let outputs = fmap_to_alist dfg.dfg_outputs in
    let updater' =
      FOLDL
        (λacc (var,iid).
           case lookup_inst_in_function iid acc.iu_fn of
             NONE => acc
           | SOME inst =>
               if inst.inst_opcode <> ASSIGN then acc
               else
                 (case inst.inst_operands of
                    [Var src] => assign_elim_process_store acc inst var src
                  | _ => acc))
        updater outputs in
    updater'.iu_fn
End

Definition assign_elim_context_def:
  assign_elim_context ctx =
    ctx with ctx_functions := MAP assign_elim_function ctx.ctx_functions
End

val _ = export_theory();
