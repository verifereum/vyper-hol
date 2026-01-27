(*
 * Function Inliner Pass
 *
 * Port of venom/passes/function_inliner.py.
 *)

Theory functionInliner
Ancestors
  list alist pred_set
  orderedSet
  ASCIInumbers
  irOps
  compilerState
  fcgAnalysis
  floatAllocas
  optimizationFlags

Datatype:
  dfs_item =
    | Enter string
    | Exit string
End

Datatype:
  inliner_state = <|
    inl_ctx : ir_context;
    inl_compiler_state : compiler_state;
    inl_count : num
  |>
End

Definition ctx_replace_function_def:
  ctx_replace_function ctx name fn' =
    ctx with ctx_functions :=
      MAP (λfn. if fn.fn_name = name then fn' else fn) ctx.ctx_functions
End

Definition ctx_remove_function_def:
  ctx_remove_function ctx name =
    ctx with ctx_functions := FILTER (λfn. fn.fn_name <> name) ctx.ctx_functions
End

Definition fcg_get_call_sites_def:
  fcg_get_call_sites fcg name =
    case FLOOKUP fcg.call_sites name of NONE => [] | SOME v => v
End

Definition fcg_get_callees_def:
  fcg_get_callees fcg name =
    case FLOOKUP fcg.callees name of NONE => [] | SOME v => v
End

Definition call_walk_iter_def:
  call_walk_iter 0 fcg stack visited walk = walk /\
  call_walk_iter (SUC fuel) fcg stack visited walk =
    case stack of
      [] => walk
    | item::rest =>
        (case item of
           Enter fn =>
             if MEM fn visited then call_walk_iter fuel fcg rest visited walk
             else
               let visited1 = ordset_add fn visited in
               let callees = fcg_get_callees fcg fn in
               let enters = MAP Enter callees in
               call_walk_iter fuel fcg (enters ++ (Exit fn :: rest)) visited1 walk
         | Exit fn =>
             call_walk_iter fuel fcg rest visited (walk ++ [fn]))
End

Definition build_call_walk_def:
  build_call_walk fcg ctx =
    case ctx.ctx_entry of
      NONE => []
    | SOME entry =>
        let fuel = (LENGTH ctx.ctx_functions + 1) * (LENGTH ctx.ctx_functions + 1) in
        call_walk_iter fuel fcg [Enter entry] [] []
End

Definition inline_prefix_def:
  inline_prefix n = STRCAT "inl" (STRCAT (num_to_dec_string n) "_")
End

Definition prefix_var_name_def:
  prefix_var_name prefix v =
    STRCAT "%" (STRCAT prefix (strip_var_prefix v))
End

Definition fn_labels_def:
  fn_labels fn = MAP (λbb. bb.bb_label) fn.fn_blocks
End

Definition clone_operand_def:
  clone_operand prefix labels op =
    case op of
      Label l => if MEM l labels then Label (STRCAT prefix l) else op
    | Var v => Var (prefix_var_name prefix v)
    | Lit w => Lit w
End

Definition clone_inst_def:
  clone_inst prefix labels inst st =
    let (iid, st1) = fresh_inst_id st in
    let ops' = MAP (clone_operand prefix labels) inst.inst_operands in
    let outs' = MAP (prefix_var_name prefix) inst.inst_outputs in
    (inst with <| inst_id := iid; inst_operands := ops'; inst_outputs := outs' |>, st1)
End

Definition clone_inst_list_def:
  clone_inst_list prefix labels [] st = ([], st) /\
  clone_inst_list prefix labels (inst::rest) st =
    let (inst', st1) = clone_inst prefix labels inst st in
    let (rest', st2) = clone_inst_list prefix labels rest st1 in
    (inst'::rest', st2)
End

Definition clone_block_def:
  clone_block prefix labels bb st =
    let label' = STRCAT prefix bb.bb_label in
    let (insts', st1) = clone_inst_list prefix labels bb.bb_instructions st in
    (<| bb_label := label'; bb_instructions := insts' |>, st1)
End

Definition clone_blocks_def:
  clone_blocks prefix labels [] st = ([], st) /\
  clone_blocks prefix labels (bb::rest) st =
    let (bb', st1) = clone_block prefix labels bb st in
    let (rest', st2) = clone_blocks prefix labels rest st1 in
    (bb'::rest', st2)
End

Definition find_inst_index_aux_def:
  find_inst_index_aux iid [] (idx:num) = NONE /\
  find_inst_index_aux iid (inst::rest) idx =
    if inst.inst_id = iid then SOME idx
    else find_inst_index_aux iid rest (idx + 1)
End

Definition find_inst_index_def:
  find_inst_index iid insts = find_inst_index_aux iid insts (0:num)
End

Definition find_inst_block_def:
  find_inst_block iid [] = NONE /\
  find_inst_block iid (bb::bbs) =
    case find_inst_index iid bb.bb_instructions of
      NONE => find_inst_block iid bbs
    | SOME idx => SOME (bb.bb_label, idx)
End

Definition update_block_in_blocks_def:
  update_block_in_blocks lbl bb' [] = [] /\
  update_block_in_blocks lbl bb' (bb::bbs) =
    if bb.bb_label = lbl then bb' :: bbs
    else bb :: update_block_in_blocks lbl bb' bbs
End

Definition mk_assign_inst_def:
  mk_assign_inst op out st =
    let (iid, st1) = fresh_inst_id st in
    (mk_inst iid ASSIGN [op] [out], st1)
End

Definition mk_return_assigns_def:
  mk_return_assigns [] outs st = ([], st) /\
  mk_return_assigns (op::ops') [] st = ([], st) /\
  mk_return_assigns (op::ops') (out::outs') st =
    let (inst, st1) = mk_assign_inst op out st in
    let (rest, st2) = mk_return_assigns ops' outs' st1 in
    (inst::rest, st2)
End

Definition inline_inst_list_def:
  inline_inst_list ops outs ret_lbl [] st param_idx = ([], st) /\
  inline_inst_list ops outs ret_lbl (inst::rest) st param_idx =
    if inst.inst_opcode = PARAM then
      let val = EL param_idx ops in
      let inst' = inst with <| inst_opcode := ASSIGN; inst_operands := [val] |> in
      let (rest', st1) = inline_inst_list ops outs ret_lbl rest st (param_idx + 1) in
      (inst'::rest', st1)
    else if inst.inst_opcode = RET then
      let ret_ops = if inst.inst_operands = [] then [] else BUTLAST inst.inst_operands in
      let ret_vals =
        FILTER (λop. case op of Label _ => F | _ => T) ret_ops in
      let (assigns, st1) = mk_return_assigns ret_vals outs st in
      let inst' = inst with <| inst_opcode := JMP;
                               inst_operands := [Label ret_lbl];
                               inst_outputs := [] |> in
      let (rest', st2) = inline_inst_list ops outs ret_lbl rest st1 param_idx in
      (assigns ++ (inst'::rest'), st2)
    else
      let (rest', st1) = inline_inst_list ops outs ret_lbl rest st param_idx in
      (inst::rest', st1)
End

Definition inline_block_def:
  inline_block ops outs ret_lbl bb st =
    let (insts', st1) = inline_inst_list ops outs ret_lbl bb.bb_instructions st 0 in
    (bb with bb_instructions := insts', st1)
End

Definition inline_blocks_def:
  inline_blocks ops outs ret_lbl [] st = ([], st) /\
  inline_blocks ops outs ret_lbl (bb::bbs) st =
    let (bb', st1) = inline_block ops outs ret_lbl bb st in
    let (rest', st2) = inline_blocks ops outs ret_lbl bbs st1 in
    (bb'::rest', st2)
End

Definition update_phi_block_def:
  update_phi_block orig new bb =
    bb with bb_instructions :=
      MAP (λinst. if inst.inst_opcode = PHI then replace_label_operands [(orig, new)] inst else inst)
          bb.bb_instructions
End

Definition fix_phi_in_succs_def:
  fix_phi_in_succs orig new succs bbs =
    MAP (λbb. if MEM bb.bb_label succs then update_phi_block orig new bb else bb) bbs
End

Definition alloca_id_of_operand_def:
  alloca_id_of_operand op =
    case op of
      Lit w => SOME (w2n w)
    | _ => NONE
End

Definition alloca_id_of_inst_def:
  alloca_id_of_inst inst =
    case inst.inst_operands of
      _::op::_ => alloca_id_of_operand op
    | _ => NONE
End

Definition calloca_update_def:
  calloca_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition fix_callocas_insts_def:
  fix_callocas_insts [] callocas found = ([], callocas, found) /\
  fix_callocas_insts (inst::rest) callocas found =
    let (inst', callocas', found') =
      if inst.inst_opcode IN {ALLOCA; CALLOCA} then
        (case alloca_id_of_inst inst of
           NONE => (inst, callocas, found)
         | SOME id =>
             (case ALOOKUP callocas id of
                SOME out =>
                  (inst with <| inst_opcode := ASSIGN;
                                inst_operands := [Var out] |>, callocas, found)
              | NONE =>
                  (case inst_output inst of
                     NONE => (inst, callocas, found)
                   | SOME out => (inst, calloca_update callocas id out, found))))
      else if inst.inst_opcode = PALLOCA then
        (case alloca_id_of_inst inst of
           NONE => (inst, callocas, found)
         | SOME id =>
             (case ALOOKUP callocas id of
                SOME out =>
                  (inst with <| inst_opcode := ASSIGN;
                                inst_operands := [Var out] |>, callocas,
                   ordset_add id found)
              | NONE => (inst, callocas, found)))
      else (inst, callocas, found) in
    let (rest', callocas'', found'') = fix_callocas_insts rest callocas' found' in
    (inst'::rest', callocas'', found'')
End

Definition demote_calloca_insts_def:
  demote_calloca_insts found [] = [] /\
  demote_calloca_insts found (inst::rest) =
    let inst' =
      if inst.inst_opcode = CALLOCA then
        (case inst.inst_operands of
           sz::Lit w::callee::rest_ops =>
             if MEM (w2n w) found then
               inst with <| inst_opcode := ALLOCA;
                            inst_operands := [sz; Lit w] |>
             else inst
         | _ => inst)
      else inst in
    inst' :: demote_calloca_insts found rest
End

Definition fix_callocas_function_def:
  fix_callocas_function fn =
    let (bbs', _, found) =
      FOLDL
        (λacc bb.
           let (bbs_acc, callocas, found_acc) = acc in
           let (insts', callocas', found') =
             fix_callocas_insts bb.bb_instructions callocas found_acc in
           (bbs_acc ++ [bb with bb_instructions := insts'], callocas', found'))
        ([], [], []) fn.fn_blocks in
    let bbs'' =
      MAP (λbb. bb with bb_instructions := demote_calloca_insts found bb.bb_instructions) bbs' in
    fn with fn_blocks := bbs''
End

Definition ctx_fix_callocas_def:
  ctx_fix_callocas ctx callers =
    ctx with ctx_functions :=
      MAP (λfn. if MEM fn.fn_name callers then fix_callocas_function fn else fn) ctx.ctx_functions
End

Definition call_site_callers_def:
  call_site_callers call_sites =
    FOLDL (λacc (caller, _). ordset_add caller acc) [] call_sites
End

Definition inline_call_site_def:
  inline_call_site callee site st =
    case site of
      (caller_name, iid) =>
        (case lookup_function caller_name st.inl_ctx.ctx_functions of
           NONE => st
         | SOME caller_fn =>
             case find_inst_block iid caller_fn.fn_blocks of
               NONE => st
             | SOME (bb_label, idx) =>
                 case lookup_block bb_label caller_fn.fn_blocks of
                   NONE => st
                 | SOME bb =>
                     let call_site = EL idx bb.bb_instructions in
                     if call_site.inst_opcode <> INVOKE then st
                     else
                       case entry_block callee of
                         NONE => st
                       | SOME entry =>
                           let prefix = inline_prefix st.inl_count in
                           let (ret_lbl, st1) =
                             fresh_label (STRCAT prefix "inline_return") st.inl_compiler_state in
                           let (jmp_id, st2) = fresh_inst_id st1 in
                           let labels = fn_labels callee in
                           let (cloned_blocks, st3) = clone_blocks prefix labels callee.fn_blocks st2 in
                           let entry_lbl = STRCAT prefix entry.bb_label in
                           let jmp_inst = mk_inst jmp_id JMP [Label entry_lbl] [] in
                           let before = TAKE idx bb.bb_instructions in
                           let after = DROP (idx + 1) bb.bb_instructions in
                           let call_site_bb' = bb with bb_instructions := before ++ [jmp_inst] in
                           let return_bb = <| bb_label := ret_lbl; bb_instructions := after |> in
                           let ops =
                             case call_site.inst_operands of
                               [] => []
                             | op0::rest => rest ++ [op0] in
                           let outs = call_site.inst_outputs in
                           let (cloned_blocks', st4) = inline_blocks ops outs ret_lbl cloned_blocks st3 in
                           let bbs1 = update_block_in_blocks bb_label call_site_bb' caller_fn.fn_blocks in
                           let bbs2 = bbs1 ++ [return_bb] ++ cloned_blocks' in
                           let succs = bb_out_labels return_bb in
                           let bbs3 = fix_phi_in_succs bb_label ret_lbl succs bbs2 in
                           let caller_fn' = caller_fn with fn_blocks := bbs3 in
                           let ctx' = ctx_replace_function st.inl_ctx caller_name caller_fn' in
                           st with <| inl_ctx := ctx';
                                     inl_compiler_state := st4;
                                     inl_count := st.inl_count + 1 |>)
End

Definition inline_call_sites_def:
  inline_call_sites callee call_sites st =
    FOLDL (λacc site. inline_call_site callee site acc) st call_sites
End

Definition inline_function_def:
  inline_function callee call_sites st =
    let callee1 = float_allocas_function callee in
    let st1 = inline_call_sites callee1 call_sites st in
    let callers = call_site_callers call_sites in
    let ctx' = ctx_fix_callocas st1.inl_ctx callers in
    st1 with inl_ctx := ctx'
End

Definition select_inline_candidate_def:
  select_inline_candidate flags ctx fcg walk =
    case walk of
      [] => NONE
    | fn_name::rest =>
        let calls = fcg_get_call_sites fcg fn_name in
        if calls = [] then select_inline_candidate flags ctx fcg rest
        else if LENGTH calls = 1 then SOME fn_name
        else
          case lookup_function fn_name ctx.ctx_functions of
            NONE => select_inline_candidate flags ctx fcg rest
          | SOME fn =>
              if fn_code_size_cost fn <= flags.vof_inline_threshold then SOME fn_name
              else select_inline_candidate flags ctx fcg rest
End

Definition inline_iter_def:
  inline_iter 0 flags fcg walk st = st /\
  inline_iter (SUC fuel) flags fcg walk st =
    case select_inline_candidate flags st.inl_ctx fcg walk of
      NONE => st
    | SOME cand =>
        (case lookup_function cand st.inl_ctx.ctx_functions of
           NONE =>
             inline_iter fuel flags fcg (FILTER (λn. n <> cand) walk) st
         | SOME fn =>
             let calls = fcg_get_call_sites fcg cand in
             let st1 = inline_function fn calls st in
             let ctx1 = ctx_remove_function st1.inl_ctx cand in
             let fcg1 = fcg_analyze ctx1 in
             let walk1 = FILTER (λn. n <> cand) walk in
             let st2 = st1 with inl_ctx := ctx1 in
             inline_iter fuel flags fcg1 walk1 st2)
End

Definition function_inliner_context_def:
  function_inliner_context flags ctx =
    if flags.vof_disable_inlining then ctx
    else
      let st0 =
        <| inl_ctx := ctx;
           inl_compiler_state := init_state_for_context ctx;
           inl_count := 0 |> in
      let fcg0 = fcg_analyze ctx in
      let walk0 = build_call_walk fcg0 ctx in
      let fuel = LENGTH ctx.ctx_functions in
      (inline_iter fuel flags fcg0 walk0 st0).inl_ctx
End

val _ = export_theory();
