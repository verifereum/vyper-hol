(*
 * Stack Order Analysis
 *
 * Port of venom/analysis/stack_order.py.
 *)

Theory stackOrderAnalysis
Ancestors
  list
  orderedSet
  irOps
  cfgAnalysis
  livenessAnalysis

Type needed = ``:string list``
Type stack = ``:operand list``
Type from_to_map = ``:(string # string) # (string list)``

Definition from_to_lookup_def:
  from_to_lookup m key =
    case ALOOKUP m key of NONE => [] | SOME v => v
End

Definition from_to_update_def:
  from_to_update m key v =
    (key, v) :: FILTER (λ(kk,_). kk <> key) m
End

Definition list_find_last_index_aux_def:
  list_find_last_index_aux x [] (idx:num) (last:num option) = last /\
  list_find_last_index_aux x (y::ys) idx last =
    if x = y then list_find_last_index_aux x ys (idx + 1) (SOME idx)
    else list_find_last_index_aux x ys (idx + 1) last
End

Definition list_find_last_index_def:
  list_find_last_index x xs = list_find_last_index_aux x xs 0 NONE
End

Definition swap_indices_def:
  swap_indices i j xs =
    if i = j then xs else
    if i >= LENGTH xs \/ j >= LENGTH xs then xs else
      let xi = EL i xs in
      let xj = EL j xs in
      LUPDATE xi j (LUPDATE xj i xs)
End

Definition stack_swap_def:
  stack_swap st op =
    case list_find_last_index op st of
      NONE => st
    | SOME idx =>
        let top = LENGTH st - 1 in
        swap_indices idx top st
End

Definition stack_swap_to_def:
  stack_swap_to st depth =
    let top = LENGTH st - 1 in
    let idx = top - depth in
    swap_indices idx top st
End

Definition max_same_prefix_def:
  max_same_prefix [] _ = [] /\
  max_same_prefix _ [] = [] /\
  max_same_prefix (a::as) (b::bs) =
    if a = b then a :: max_same_prefix as bs else []
End

Definition add_needed_def:
  add_needed v needed =
    if MEM v needed then needed else needed ++ [v]
End

Definition reorder_stack_def:
  reorder_stack st [] = st /\
  reorder_stack st (op::ops) =
    let count = LENGTH (op::ops) in
    let depth = count - 1 in
    let st1 = stack_swap st op in
    let st2 = stack_swap_to st1 depth in
    reorder_stack st2 ops
End

Definition handle_inst_def:
  handle_inst st needed inst =
    let ops = inst.inst_operands in
    let (needed', st') =
      FOLDL
        (λacc op.
           let (need, stack) = acc in
           let need' =
             case op of
               Var v => if MEM op stack then need else add_needed v need
             | _ => need in
           let stack' = if MEM op stack then stack else stack ++ [op] in
           (need', stack'))
        (needed, st) ops in
    let st'' = reorder_stack st' ops in
    (needed', st'')
End

Definition handle_assign_def:
  handle_assign liveness bb inst needed st =
    case inst.inst_operands of
      [] => (needed, st)
    | (src::_) =>
        let idx =
          case list_find_last_index inst bb.bb_instructions of
            NONE => 0
          | SOME i => i in
        let next_inst = if idx + 1 < LENGTH bb.bb_instructions
                        then SOME (EL (idx + 1) bb.bb_instructions) else NONE in
        let next_live =
          case next_inst of
            NONE => []
          | SOME ni => liveness_live_vars_at liveness ni.inst_id in
        (case src of
           Var v =>
             if MEM v next_live then
               let st1 = st ++ [src] in
               let need1 = add_needed v needed in
               (need1, st1)
             else if ~MEM src st then
               let st1 = st ++ [src] in
               let need1 = add_needed v needed in
               (need1, st1)
             else
               (needed, stack_swap st src)
         | _ =>
             (needed, st ++ [src]))
End

Definition handle_terminator_def:
  handle_terminator cfg from_to bb inst needed st =
    let orders =
      MAP (λsucc. from_to_lookup from_to (bb.bb_label, succ))
          (fmap_lookup_ordset cfg.cfg_out bb.bb_label) in
    let merged = FOLDL max_same_prefix (if orders = [] then [] else HD orders) (TL orders) in
    let needed1 =
      FOLDL
        (λacc op. case op of Var v => add_needed v acc | _ => acc)
        needed inst.inst_operands in
    let needed2 = FOLDL (λacc v. add_needed v acc) needed1 merged in
    (needed2, st)
End

Definition pop_operands_def:
  pop_operands st n =
    let len = LENGTH st in
    if n = 0 then st else TAKE (len - n) st
End

Definition push_outputs_def:
  push_outputs st outs = st ++ MAP Var outs
End

Definition analyze_bb_def:
  analyze_bb cfg liveness from_to bb =
    let (needed, st) =
      FOLDL
        (λacc inst.
           let (need, stack) = acc in
           let (need1, stack1) =
             if inst.inst_opcode = ASSIGN then
               handle_assign liveness bb inst need stack
             else if inst.inst_opcode = PHI then
               handle_inst stack need inst
             else if inst_is_bb_terminator inst then
               handle_terminator cfg from_to bb inst need stack
             else
               handle_inst stack need inst in
           let nops = LENGTH inst.inst_operands in
           let stack2 = pop_operands stack1 nops in
           let stack3 = push_outputs stack2 inst.inst_outputs in
           (need1, stack3))
        ([], []) bb.bb_instructions in
    let from_to' =
      FOLDL
        (λm pred. from_to_update m (pred, bb.bb_label) needed)
        from_to (fmap_lookup_ordset cfg.cfg_in bb.bb_label) in
    (from_to', needed)
End

Definition merge_orders_def:
  merge_orders orders =
    case orders of
      [] => []
    | (order::rest) => FOLDL max_same_prefix order rest
End

Definition stack_order_get_stack_def:
  stack_order_get_stack fn cfg liveness from_to bb =
    let succs = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
    let (from_to', _) =
      FOLDL
        (λacc lbl.
           let (m, _) = acc in
           case lookup_block lbl fn.fn_blocks of
             NONE => (m, [])
           | SOME b => analyze_bb cfg liveness m b)
        (from_to, []) succs in
    let orders = MAP (λsucc. from_to_lookup from_to' (bb.bb_label, succ)) succs in
    (from_to', merge_orders orders)
End

Definition stack_order_from_to_def:
  stack_order_from_to liveness bbs from_to origin_lbl succ_lbl =
    let target = from_to_lookup from_to (origin_lbl, succ_lbl) in
    let live = liveness_input_vars_from liveness bbs origin_lbl succ_lbl in
    ordset_union target live
End

val _ = export_theory();
