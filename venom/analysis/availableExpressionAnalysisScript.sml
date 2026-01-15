(*
 * Available Expression Analysis
 *
 * Port of venom/analysis/available_expression.py.
 *)

Theory availableExpressionAnalysis
Ancestors
  list pred_set
  orderedSet
  irOps
  cfgAnalysis dfgAnalysis
  venomSem

(* ===== Expression Types ===== *)

Datatype:
  expr_operand =
    ExprOp operand
  | ExprRef num
End

Datatype:
  expr = <|
    expr_opcode : opcode;
    expr_operands : expr_operand list
  |>
End

Definition expr_operand_same_def:
  expr_operand_same op1 op2 <=>
    case (op1, op2) of
      (ExprOp a, ExprOp b) => a = b
    | (ExprRef a, ExprRef b) => a = b
    | _ => F
End

Definition expr_operands_same_def:
  expr_operands_same [] [] = T /\
  expr_operands_same (a::rest_a) (b::rest_b) =
    (expr_operand_same a b /\ expr_operands_same rest_a rest_b) /\
  expr_operands_same _ _ = F
End

Definition expr_is_commutative_def:
  expr_is_commutative op <=>
    op IN {ADD; MUL; SMUL; OR; XOR; AND; EQ}
End

Definition expr_same_def:
  expr_same e1 e2 <=>
    e1.expr_opcode = e2.expr_opcode /\
    (expr_operands_same e1.expr_operands e2.expr_operands \/
     (expr_is_commutative e1.expr_opcode /\
      expr_operands_same e1.expr_operands (REVERSE e2.expr_operands)))
End

(* ===== Effect Helpers ===== *)

Definition sys_effects_def:
  sys_effects = {Eff_LOG; Eff_BALANCE; Eff_EXTCODE}
End

Definition expr_read_effects_def:
  expr_read_effects op ignore_msize =
    let eff = read_effects op in
    if ignore_msize then eff DIFF {Eff_MSIZE} else eff
End

Definition expr_write_effects_def:
  expr_write_effects op ignore_msize =
    let eff = write_effects op in
    if ignore_msize then eff DIFF {Eff_MSIZE} else eff
End

Definition expr_effects_def:
  expr_effects op ignore_msize =
    expr_read_effects op ignore_msize UNION expr_write_effects op ignore_msize
End

Definition expr_overlap_effects_def:
  expr_overlap_effects op ignore_msize =
    expr_read_effects op ignore_msize INTER expr_write_effects op ignore_msize
End

Definition expr_is_nonidempotent_def:
  expr_is_nonidempotent op <=>
    op = STATICCALL \/
    ~(expr_write_effects op F INTER sys_effects = {})
End

(* ===== Available Expressions Map ===== *)

Datatype:
  available_exprs = <|
    ae_entries : (expr # num list) list
  |>
End

Definition expr_map_lookup_def:
  expr_map_lookup e [] = NONE /\
  expr_map_lookup e ((k,v)::rest) =
    if expr_same e k then SOME v else expr_map_lookup e rest
End

Definition expr_map_update_def:
  expr_map_update e v m =
    (e, v) :: FILTER (λ(k,_). ~expr_same e k) m
End

Definition available_exprs_empty_def:
  available_exprs_empty = <| ae_entries := [] |>
End

Definition available_exprs_copy_def:
  available_exprs_copy ae = ae
End

Definition available_exprs_add_def:
  available_exprs_add ae e inst_id =
    case expr_map_lookup e ae.ae_entries of
      NONE => ae with ae_entries := (e, [inst_id]) :: ae.ae_entries
    | SOME insts =>
        ae with ae_entries := expr_map_update e (insts ++ [inst_id]) ae.ae_entries
End

Definition available_exprs_remove_effect_def:
  available_exprs_remove_effect ae effect ignore_msize =
    if effect = {} then ae
    else
      ae with ae_entries :=
        FILTER
          (λ(k,_). expr_effects k.expr_opcode ignore_msize INTER effect = {})
          ae.ae_entries
End

Definition available_exprs_get_source_def:
  available_exprs_get_source ae e =
    case expr_map_lookup e ae.ae_entries of
      NONE => NONE
    | SOME insts =>
        case insts of
          [] => NONE
        | (i::_) => SOME i
End

Definition list_intersection_def:
  list_intersection xs ys = FILTER (λx. MEM x ys) xs
End

Definition expr_map_intersect_def:
  expr_map_intersect m1 m2 =
    FOLDL
      (λacc (e,insts).
         case expr_map_lookup e m2 of
           NONE => acc
         | SOME insts2 =>
             let insts' = list_intersection insts insts2 in
             if insts' = [] then acc else acc ++ [(e, insts')])
      [] m1
End

Definition available_exprs_lattice_meet_def:
  available_exprs_lattice_meet [] = available_exprs_empty /\
  available_exprs_lattice_meet (ae::rest) =
    let entries =
      FOLDL
        (λacc other. expr_map_intersect acc other.ae_entries)
        ae.ae_entries rest in
    <| ae_entries := entries |>
End

(* ===== Analysis State ===== *)

Datatype:
  available_expr_analysis = <|
    ae_inst_expr : (num # expr) list;
    ae_inst_available : (num # available_exprs) list;
    ae_bb_in : (string # available_exprs) list;
    ae_bb_out : (string # available_exprs) list;
    ae_inst_block : (num # string) list;
    ae_ignore_msize : bool
  |>
End

Definition alist_lookup_def:
  alist_lookup k [] = NONE /\
  alist_lookup k ((k',v)::rest) =
    if k = k' then SOME v else alist_lookup k rest
End

Definition alist_update_def:
  alist_update k v m =
    (k, v) :: FILTER (λ(k',_). k' <> k) m
End

Definition inst_block_map_def:
  inst_block_map fn =
    FOLDL
      (λacc bb.
         FOLDL
           (λacc2 inst. (inst.inst_id, bb.bb_label) :: acc2)
           acc bb.bb_instructions)
      [] fn.fn_blocks
End

Definition contains_msize_def:
  contains_msize fn <=>
    EXISTS (λbb. EXISTS (λinst. inst.inst_opcode = MSIZE) bb.bb_instructions)
           fn.fn_blocks
End

Definition available_expr_init_def:
  available_expr_init fn =
    <| ae_inst_expr := [];
       ae_inst_available := [];
       ae_bb_in := [];
       ae_bb_out := [];
       ae_inst_block := inst_block_map fn;
       ae_ignore_msize := ~contains_msize fn |>
End

Definition get_operand_expr_def:
  get_operand_expr fn dfg op fuel =
    case fuel of
      0 => ExprOp op
    | SUC fuel' =>
        (case op of
           Var v =>
             (case dfg_get_producing dfg v of
                NONE => ExprOp op
              | SOME iid =>
                  (case lookup_inst_in_function iid fn of
                     NONE => ExprOp op
                   | SOME inst =>
                       if inst.inst_opcode IN {PHI; PARAM} then ExprOp op
                       else if inst.inst_opcode = ASSIGN then
                         (case inst.inst_operands of
                            [op1] => get_operand_expr fn dfg op1 fuel'
                          | _ => ExprOp op)
                       else if inst_num_outputs inst > 1 then ExprOp op
                       else ExprRef iid))
         | _ => ExprOp op)
End

Definition mk_expr_def:
  mk_expr fn dfg inst =
    let fuel = LENGTH (fn_instructions_list fn) + 1 in
    <| expr_opcode := inst.inst_opcode;
       expr_operands :=
         MAP (λop. get_operand_expr fn dfg op fuel) inst.inst_operands |>
End

Definition available_expr_update_inst_available_def:
  available_expr_update_inst_available st inst_id ae =
    case alist_lookup inst_id st.ae_inst_available of
      SOME prev => if prev = ae then st
                   else st with ae_inst_available :=
                          alist_update inst_id ae st.ae_inst_available
    | NONE => st with ae_inst_available :=
                alist_update inst_id ae st.ae_inst_available
End

Definition available_expr_update_inst_expr_def:
  available_expr_update_inst_expr st inst_id e =
    st with ae_inst_expr := alist_update inst_id e st.ae_inst_expr
End

Definition blocks_from_labels_def:
  blocks_from_labels bbs lbls =
    MAP (\lbl. THE (lookup_block lbl bbs)) lbls
End

Definition handle_bb_available_expr_def:
  handle_bb_available_expr fn cfg dfg st bb =
    let preds = fmap_lookup_ordset cfg.cfg_in bb.bb_label in
    let pred_outs =
      MAP (λlbl. case alist_lookup lbl st.ae_bb_out of
                   NONE => available_exprs_empty
                 | SOME ae => ae) preds in
    let ae_in = available_exprs_lattice_meet pred_outs in
    case alist_lookup bb.bb_label st.ae_bb_in of
      SOME prev =>
        if prev = ae_in then (st, F)
        else
          let st1 = st with ae_bb_in := alist_update bb.bb_label ae_in st.ae_bb_in in
          let (st2, ae_out) =
            FOLDL
              (λacc inst.
                 let (st_acc, ae_acc) = acc in
                 if inst.inst_opcode = ASSIGN \/
                    inst_is_pseudo inst \/
                    inst_is_bb_terminator inst \/
                    inst_num_outputs inst > 1 then
                   (st_acc, ae_acc)
                 else
                   let st3 = available_expr_update_inst_available st_acc inst.inst_id ae_acc in
                   let e = mk_expr fn dfg inst in
                   let st4 = available_expr_update_inst_expr st3 inst.inst_id e in
                   let w_eff = expr_write_effects e.expr_opcode st.ae_ignore_msize in
                   let ae1 = available_exprs_remove_effect ae_acc w_eff st.ae_ignore_msize in
                   if expr_is_nonidempotent e.expr_opcode then (st4, ae1)
                   else
                     let o_eff = expr_overlap_effects e.expr_opcode st.ae_ignore_msize in
                     if o_eff = {} then
                       (st4, available_exprs_add ae1 e inst.inst_id)
                     else (st4, ae1))
              (st1, ae_in) bb.bb_instructions in
          let st3 =
            st2 with ae_bb_out := alist_update bb.bb_label ae_out st2.ae_bb_out in
          (st3, T)
    | NONE =>
        let st1 = st with ae_bb_in := alist_update bb.bb_label ae_in st.ae_bb_in in
        let (st2, ae_out) =
          FOLDL
            (λacc inst.
               let (st_acc, ae_acc) = acc in
               if inst.inst_opcode = ASSIGN \/
                  inst_is_pseudo inst \/
                  inst_is_bb_terminator inst \/
                  inst_num_outputs inst > 1 then
                 (st_acc, ae_acc)
               else
                 let st3 = available_expr_update_inst_available st_acc inst.inst_id ae_acc in
                 let e = mk_expr fn dfg inst in
                 let st4 = available_expr_update_inst_expr st3 inst.inst_id e in
                 let w_eff = expr_write_effects e.expr_opcode st.ae_ignore_msize in
                 let ae1 = available_exprs_remove_effect ae_acc w_eff st.ae_ignore_msize in
                 if expr_is_nonidempotent e.expr_opcode then (st4, ae1)
                 else
                   let o_eff = expr_overlap_effects e.expr_opcode st.ae_ignore_msize in
                   if o_eff = {} then
                     (st4, available_exprs_add ae1 e inst.inst_id)
                   else (st4, ae1))
            (st1, ae_in) bb.bb_instructions in
        let st3 =
          st2 with ae_bb_out := alist_update bb.bb_label ae_out st2.ae_bb_out in
        (st3, T)
End

Definition available_expr_iter_def:
  available_expr_iter 0 fn cfg dfg work st = st /\
  available_expr_iter (SUC fuel) fn cfg dfg work st =
    case work of
      [] => st
    | bb::rest =>
        let (st1, changed) = handle_bb_available_expr fn cfg dfg st bb in
        let succs = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
        let succ_bbs = blocks_from_labels fn.fn_blocks succs in
        let work' = if changed then rest ++ succ_bbs else rest in
        available_expr_iter fuel fn cfg dfg work' st1
End

Definition available_expr_analyze_def:
  available_expr_analyze fn cfg dfg =
    let st0 = available_expr_init fn in
    case entry_block fn of
      NONE => st0
    | SOME entry =>
        let fuel = (LENGTH fn.fn_blocks) * (LENGTH fn.fn_blocks) + 1 in
        available_expr_iter fuel fn cfg dfg [entry] st0
End

Definition available_expr_get_expression_def:
  available_expr_get_expression st inst_id =
    case alist_lookup inst_id st.ae_inst_expr of
      NONE => NONE
    | SOME e =>
        let ae =
          case alist_lookup inst_id st.ae_inst_available of
            NONE => available_exprs_empty
          | SOME a => a in
        case available_exprs_get_source ae e of
          NONE => NONE
        | SOME src =>
            if src = inst_id then NONE else SOME (e, src)
End

Definition available_expr_get_from_same_bb_def:
  available_expr_get_from_same_bb fn st inst_id e =
    case alist_lookup inst_id st.ae_inst_available of
      NONE => []
    | SOME ae =>
        let insts = case expr_map_lookup e ae.ae_entries of
                      NONE => []
                    | SOME xs => xs in
        case alist_lookup inst_id st.ae_inst_block of
          NONE => []
        | SOME lbl =>
            FILTER
              (λiid.
                 iid <> inst_id /\
                 case alist_lookup iid st.ae_inst_block of
                   SOME lbl' => lbl' = lbl
                 | NONE => F)
              insts
End

(* Depth calculation for heuristics (treat missing refs as leaves) *)
Definition list_max_def:
  list_max [] = 0 /\
  list_max (x::xs) = MAX x (list_max xs)
End

Definition expr_depth_aux_def:
  expr_depth_aux exprs e 0 = 1 /\
  expr_depth_aux exprs e (SUC fuel) =
    let depths =
      MAP
        (λop.
           case op of
             ExprOp _ => 0
           | ExprRef iid =>
               (case alist_lookup iid exprs of
                  NONE => 0
                | SOME e' => expr_depth_aux exprs e' fuel))
        e.expr_operands in
    list_max depths + 1
End

Definition available_expr_depth_def:
  available_expr_depth st e =
    let fuel = LENGTH st.ae_inst_expr + 1 in
    expr_depth_aux st.ae_inst_expr e fuel
End

val _ = export_theory();
