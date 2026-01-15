(*
 * Sparse Conditional Constant Propagation (SCCP)
 *
 * Port of venom/passes/sccp/sccp.py.
 *)

Theory sccp
Ancestors
  list pred_set
  orderedSet
  irOps cfgAnalysis dfgAnalysis
  sccpEval

Datatype:
  lattice_value =
    | LTop
    | LBottom
    | LConst bytes32
    | LLabel string
End

Datatype:
  work_item =
    | FlowItem string string
    | SSAItem num
End

Type lattice = ``:(string # lattice_value) list``
Type exec_map = ``:(string # string list) list``

Datatype:
  sccp_result =
    | SCCP_OK 'a
    | SCCP_FAIL string
End

Definition lattice_lookup_def:
  lattice_lookup lat v =
    case ALOOKUP lat v of NONE => LTop | SOME x => x
End

Definition lattice_update_def:
  lattice_update lat v val = (v, val) :: FILTER (λ(k,_). k <> v) lat
End

Definition exec_lookup_def:
  exec_lookup m k = case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition exec_update_def:
  exec_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition exec_add_def:
  exec_add m k v = exec_update m k (ordset_add v (exec_lookup m k))
End

Definition lattice_meet_def:
  lattice_meet LTop y = y /\
  lattice_meet x LTop = x /\
  lattice_meet x y = if x = y then x else LBottom
End

Definition lattice_eval_operand_def:
  lattice_eval_operand lat (Lit w) = LConst w /\
  lattice_eval_operand lat (Label l) = LLabel l /\
  lattice_eval_operand lat (Var v) = lattice_lookup lat v
End

Definition is_sccp_arith_def:
  is_sccp_arith op <=>
    op IN
    {ADD; SUB; MUL; Div; SDIV; Mod; SMOD; venomInst$EXP; EQ; LT; GT; SLT; SGT;
     OR; AND; XOR; NOT; SIGNEXTEND; ISZERO; SHR; SHL; SAR; ADDMOD; MULMOD}
End

Definition sccp_eval_arith_def:
  sccp_eval_arith op ops =
    case eval_arith op ops of
      NONE => LBottom
    | SOME v => LConst v
End

Definition add_ssa_work_items_def:
  add_ssa_work_items dfg outs work =
    FOLDL
      (λacc out.
         FOLDL (λacc2 iid. SSAItem iid :: acc2) acc (dfg_get_uses dfg out))
      work outs
End

Definition sccp_update_var_def:
  sccp_update_var dfg lat work out value =
    if lattice_lookup lat out = value then (lat, work)
    else
      let lat1 = lattice_update lat out value in
      let work1 = add_ssa_work_items dfg [out] work in
      (lat1, work1)
End

Definition sccp_update_vars_def:
  sccp_update_vars dfg lat work outs value =
    FOLDL
      (λacc out.
         let (l, w) = acc in
         sccp_update_var dfg l w out value)
      (lat, work) outs
End

Definition find_inst_block_def:
  find_inst_block iid [] = NONE /\
  find_inst_block iid (bb::bbs) =
    if MEM iid (MAP (λinst. inst.inst_id) bb.bb_instructions) then SOME bb.bb_label
    else find_inst_block iid bbs
End

Definition sccp_visit_phi_def:
  sccp_visit_phi fn dfg exec lat work bb_label inst =
    let pairs = phi_operands inst.inst_operands in
    let in_vals =
      FOLDL
        (λacc (lbl, v).
           if MEM lbl (exec_lookup exec bb_label) then
             acc ++ [lattice_lookup lat v]
           else acc)
        [] pairs in
    let value = FOLDL lattice_meet LTop in_vals in
    case inst_output inst of
      NONE => (lat, work)
    | SOME out =>
        if value = lattice_lookup lat out then (lat, work)
        else
          let lat1 = lattice_update lat out value in
          let work1 = add_ssa_work_items dfg [out] work in
          (lat1, work1)
End

Definition sccp_eval_inst_def:
  sccp_eval_inst fn cfg dfg lat work bb_label inst =
    let op = inst.inst_opcode in
    if op = ASSIGN then
      (case inst.inst_operands of
         (op1::_) =>
           (case inst_output inst of
              NONE => (lat, work)
            | SOME out =>
                let v = lattice_eval_operand lat op1 in
                sccp_update_var dfg lat work out v)
       | _ => (lat, work))
    else if op = GEP then
      (case inst_output inst of
         NONE => (lat, work)
       | SOME out =>
           sccp_update_var dfg lat work out LBottom)
    else if op = JMP then
      (case inst.inst_operands of
         [Label l] => (lat, FlowItem bb_label l :: work)
       | _ => (lat, work))
    else if op = JNZ then
      (case inst.inst_operands of
         (cond :: Label t :: Label f :: _) =>
           let v = lattice_eval_operand lat cond in
           (case v of
              LBottom => (lat, MAP (λl. FlowItem bb_label l) (fmap_lookup_ordset cfg.cfg_out bb_label) ++ work)
            | LTop => (lat, MAP (λl. FlowItem bb_label l) (fmap_lookup_ordset cfg.cfg_out bb_label) ++ work)
            | LConst w =>
                if w = 0w then (lat, FlowItem bb_label f :: work)
                else (lat, FlowItem bb_label t :: work)
            | LLabel _ => (lat, MAP (λl. FlowItem bb_label l) (fmap_lookup_ordset cfg.cfg_out bb_label) ++ work))
       | _ => (lat, work))
    else if op = DJMP then
      (case inst.inst_operands of
         (cond :: rest) =>
           let v = lattice_eval_operand lat cond in
           (case v of
              LBottom =>
                (lat, MAP (λop. case op of Label l => FlowItem bb_label l | _ => FlowItem bb_label bb_label) rest ++ work)
            | LTop =>
                (lat, MAP (λop. case op of Label l => FlowItem bb_label l | _ => FlowItem bb_label bb_label) rest ++ work)
            | LLabel _ =>
                (lat, MAP (λop. case op of Label l => FlowItem bb_label l | _ => FlowItem bb_label bb_label) rest ++ work)
            | LConst _ => (lat, work))
       | _ => (lat, work))
    else if is_sccp_arith op then
      let evals =
        FOLDL
          (λacc opnd.
             let v = lattice_eval_operand lat opnd in
             acc ++ [v])
          [] inst.inst_operands in
      if EXISTS (λv. v = LBottom) evals then
        (case inst_output inst of
           NONE => (lat, work)
         | SOME out =>
             sccp_update_var dfg lat work out LBottom)
      else if EXISTS (λv. v = LTop) evals then
        (case inst_output inst of
           NONE => (lat, work)
         | SOME out =>
             sccp_update_var dfg lat work out LTop)
      else if EXISTS (λv. case v of LLabel _ => T | _ => F) evals then
        (case inst_output inst of
           NONE => (lat, work)
         | SOME out =>
             sccp_update_var dfg lat work out LBottom)
      else
        let ops =
          MAP (λv. case v of LConst w => w | _ => 0w) evals in
        (case inst_output inst of
           NONE => (lat, work)
         | SOME out =>
             let v = sccp_eval_arith op ops in
             sccp_update_var dfg lat work out v)
    else
      (case inst.inst_outputs of
         [] => (lat, work)
       | outs =>
           sccp_update_vars dfg lat work outs LBottom)
End

Definition sccp_handle_flow_def:
  sccp_handle_flow fn cfg dfg exec lat work start_lbl end_lbl =
    if MEM start_lbl (exec_lookup exec end_lbl) then (exec, lat, work)
    else
      case lookup_block end_lbl fn.fn_blocks of
        NONE => (exec, lat, work)
      | SOME bb =>
          let exec1 = exec_add exec end_lbl start_lbl in
          let (lat1, work1) =
            FOLDL
              (λacc inst.
                 let (l, w) = acc in
                 if inst.inst_opcode = PHI then sccp_visit_phi fn dfg exec1 l w end_lbl inst
                 else (l, w))
              (lat, work) bb.bb_instructions in
          let (lat2, work2) =
            if LENGTH (exec_lookup exec1 end_lbl) = 1 then
              FOLDL
                (λacc inst.
                   let (l, w) = acc in
                   if inst.inst_opcode = PHI then (l, w)
                   else sccp_eval_inst fn cfg dfg l w end_lbl inst)
                (lat1, work1) bb.bb_instructions
            else (lat1, work1) in
          (exec1, lat2, work2)
End

Definition sccp_handle_ssa_def:
  sccp_handle_ssa fn cfg dfg exec lat work iid =
    case find_inst_block iid fn.fn_blocks of
      NONE => (exec, lat, work)
    | SOME lbl =>
        if exec_lookup exec lbl = [] then (exec, lat, work)
        else
          case lookup_inst_in_function iid fn of
            NONE => (exec, lat, work)
          | SOME inst =>
              if inst.inst_opcode = PHI then
                let (lat1, work1) = sccp_visit_phi fn dfg exec lat work lbl inst in
                (exec, lat1, work1)
              else
                let (lat1, work1) = sccp_eval_inst fn cfg dfg lat work lbl inst in
                (exec, lat1, work1)
End

Definition sccp_iter_def:
  sccp_iter 0 fn cfg dfg exec lat work = (exec, lat, work) /\
  sccp_iter (SUC fuel) fn cfg dfg exec lat work =
    case work of
      [] => (exec, lat, work)
    | item::rest =>
        (case item of
           FlowItem s e =>
             let (exec1, lat1, work1) = sccp_handle_flow fn cfg dfg exec lat rest s e in
             sccp_iter fuel fn cfg dfg exec1 lat1 work1
         | SSAItem iid =>
             let (exec1, lat1, work1) = sccp_handle_ssa fn cfg dfg exec lat rest iid in
             sccp_iter fuel fn cfg dfg exec1 lat1 work1)
End

Definition init_exec_map_def:
  init_exec_map bbs =
    FOLDL (λm bb. exec_update m bb.bb_label []) [] bbs
End

Definition init_lattice_def:
  init_lattice dfg =
    FOLDL
      (λacc v. lattice_update acc v LTop)
      [] (SET_TO_LIST (FDOM dfg.dfg_outputs))
End

Definition sccp_analyze_def:
  sccp_analyze fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    case entry_block fn of
      NONE => (cfg, dfg, init_exec_map fn.fn_blocks, init_lattice dfg)
    | SOME entry =>
        let exec0 = init_exec_map fn.fn_blocks in
        let lat0 = init_lattice dfg in
        let work0 = [FlowItem "__dummy_start" entry.bb_label] in
        let fuel = (LENGTH (fn_instructions_list fn) + 1) * (LENGTH (fn_instructions_list fn) + 1) in
        let (exec1, lat1, _) = sccp_iter fuel fn cfg dfg exec0 lat0 work0 in
        (cfg, dfg, exec1, lat1)
End

Definition sccp_assert_fail_msg_def:
  sccp_assert_fail_msg = "assertion found to fail at compile time"
End

Definition sccp_djmp_fail_msg_def:
  sccp_djmp_fail_msg = "Unimplemented djmp with literal"
End

Definition sccp_fail_inst_def:
  sccp_fail_inst lat inst =
    case inst.inst_opcode of
      ASSERT =>
        (case inst.inst_operands of
           [cond] =>
             (case lattice_eval_operand lat cond of
                LConst w => if w = 0w then SOME sccp_assert_fail_msg else NONE
              | _ => NONE)
         | _ => NONE)
    | ASSERT_UNREACHABLE =>
        (case inst.inst_operands of
           [cond] =>
             (case lattice_eval_operand lat cond of
                LConst w => if w = 0w then SOME sccp_assert_fail_msg else NONE
              | _ => NONE)
         | _ => NONE)
    | DJMP =>
        (case inst.inst_operands of
           cond::_ =>
             (case lattice_eval_operand lat cond of
                LConst _ => SOME sccp_djmp_fail_msg
              | _ => NONE)
         | _ => NONE)
    | _ => NONE
End

Definition sccp_fail_block_def:
  sccp_fail_block lat bb =
    FOLDL
      (λacc inst. case acc of SOME _ => acc | NONE => sccp_fail_inst lat inst)
      NONE bb.bb_instructions
End

Definition sccp_fail_function_def:
  sccp_fail_function lat fn =
    FOLDL
      (λacc bb. case acc of SOME _ => acc | NONE => sccp_fail_block lat bb)
      NONE fn.fn_blocks
End

Definition transform_operand_def:
  transform_operand lat (Lit w) = Lit w /\
  transform_operand lat (Label l) = Label l /\
  transform_operand lat (Var v) =
    (case lattice_lookup lat v of
       LConst w => Lit w
     | _ => Var v)
End

Definition transform_operands_def:
  transform_operands lat ops = MAP (transform_operand lat) ops
End

Definition transform_inst_def:
  transform_inst lat inst =
    case inst.inst_opcode of
      JNZ =>
        (case inst.inst_operands of
           [cond; Label t; Label f] =>
             (case lattice_eval_operand lat cond of
                LConst w =>
                  if w = 0w then inst with <| inst_opcode := JMP; inst_operands := [Label f] |>
                  else inst with <| inst_opcode := JMP; inst_operands := [Label t] |>
              | _ =>
                  inst with <| inst_operands := transform_operands lat inst.inst_operands |>)
         | _ => inst)
    | ASSERT =>
        (case inst.inst_operands of
           [cond] =>
             (case lattice_eval_operand lat cond of
                LConst w =>
                  if w = 0w then inst else inst_make_nop inst
              | _ =>
                  inst with <| inst_operands := transform_operands lat inst.inst_operands |>)
         | _ => inst)
    | ASSERT_UNREACHABLE =>
        (case inst.inst_operands of
           [cond] =>
             (case lattice_eval_operand lat cond of
                LConst w =>
                  if w = 0w then inst else inst_make_nop inst
              | _ =>
                  inst with <| inst_operands := transform_operands lat inst.inst_operands |>)
         | _ => inst)
    | PHI => inst
    | _ => inst with <| inst_operands := transform_operands lat inst.inst_operands |>
End

Definition transform_block_def:
  transform_block lat bb =
    bb with bb_instructions := MAP (transform_inst lat) bb.bb_instructions
End

Definition transform_function_def:
  transform_function lat fn =
    fn with fn_blocks := MAP (transform_block lat) fn.fn_blocks
End

Definition sccp_run_def:
  sccp_run fn =
    let (_, _, _, lat) = sccp_analyze fn in
    case sccp_fail_function lat fn of
      SOME msg => SCCP_FAIL msg
    | NONE =>
        let fn' = transform_function lat fn in
        SCCP_OK fn'
End

Definition sccp_context_def:
  sccp_context ctx =
    let res =
      FOLDL
        (λacc fn.
           case acc of
             SCCP_FAIL msg => SCCP_FAIL msg
           | SCCP_OK fns =>
               (case sccp_run fn of
                  SCCP_OK fn' => SCCP_OK (fns ++ [fn'])
                | SCCP_FAIL msg => SCCP_FAIL msg))
        (SCCP_OK []) ctx.ctx_functions in
    case res of
      SCCP_OK fns => SCCP_OK (ctx with ctx_functions := fns)
    | SCCP_FAIL msg => SCCP_FAIL msg
End

val _ = export_theory();
