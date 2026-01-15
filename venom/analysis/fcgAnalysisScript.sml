(*
 * Function Call Graph (FCG) Analysis
 *
 * Port of venom/analysis/fcg.py.
 *)

Theory fcgAnalysis
Ancestors
  list finite_map
  orderedSet
  venomInst

Datatype:
  fcg_analysis = <|
    call_sites : (string, (string # num) list) fmap;
    callees : (string, string list) fmap;
    reachable : string list
  |>
End

Definition fcg_add_call_site_def:
  fcg_add_call_site m callee caller inst_id =
    let s = case FLOOKUP m callee of NONE => [] | SOME v => v in
    m |+ (callee, ordset_add (caller, inst_id) s)
End

Definition fcg_add_callee_def:
  fcg_add_callee m fn callee =
    let s = case FLOOKUP m fn of NONE => [] | SOME v => v in
    m |+ (fn, ordset_add callee s)
End

Definition fcg_visit_function_def:
  fcg_visit_function ctx fn_name (call_sites, callees, reachable, stack) =
    if MEM fn_name reachable then (call_sites, callees, reachable, stack)
    else
      case lookup_function fn_name ctx.ctx_functions of
        NONE => (call_sites, callees, reachable, stack)
      | SOME fn =>
          let reachable' = ordset_add fn_name reachable in
          let call_sites' = if IS_SOME (FLOOKUP call_sites fn_name)
                            then call_sites else call_sites |+ (fn_name, []) in
          let callees' = callees |+ (fn_name, []) in
          let (call_sites'', callees'', stack') =
            FOLDL
              (λacc bb.
                 let (cs, cal, st) = acc in
                 FOLDL
                   (λacc2 inst.
                      let (cs2, cal2, st2) = acc2 in
                      if inst.inst_opcode = INVOKE then
                        case inst.inst_operands of
                          (Label lbl :: _) =>
                            let cal2' = fcg_add_callee cal2 fn_name lbl in
                            let cs2' = fcg_add_call_site cs2 lbl fn_name inst.inst_id in
                            (cs2', cal2', ordset_add lbl st2)
                        | _ => (cs2, cal2, st2)
                      else (cs2, cal2, st2))
                   (cs, cal, st) bb.bb_instructions)
              (call_sites', callees', stack) fn.fn_blocks in
          (call_sites'', callees'', reachable', stack')
End

Definition fcg_dfs_def:
  fcg_dfs ctx stack call_sites callees reachable fuel =
    case fuel of
      0 => <| call_sites := call_sites; callees := callees; reachable := reachable |>
    | SUC fuel' =>
        (case ordset_pop stack of
           NONE => <| call_sites := call_sites; callees := callees; reachable := reachable |>
         | SOME (fn_name, stack') =>
             let (cs, cal, reach, st) =
               fcg_visit_function ctx fn_name (call_sites, callees, reachable, stack') in
             fcg_dfs ctx st cs cal reach fuel')
End

Definition fcg_analyze_def:
  fcg_analyze ctx =
    case ctx.ctx_entry of
      NONE => <| call_sites := FEMPTY; callees := FEMPTY; reachable := [] |>
    | SOME entry =>
        let fuel = (LENGTH ctx.ctx_functions + 1) * (LENGTH ctx.ctx_functions + 1) in
        fcg_dfs ctx [entry] FEMPTY FEMPTY [] fuel
End

val _ = export_theory();
