(*
 * Memory SSA Analysis
 *
 * Port of venom/analysis/mem_ssa.py.
 *)

Theory memSSAAnalysis
Ancestors
  list
  orderedSet
  cfgAnalysis dominatorsAnalysis
  basePtrAnalysis memAliasAnalysis
  memoryLocation addrSpace
  irOps

(* ===== Memory SSA Node Types ===== *)

Datatype:
  mem_def = <|
    md_id : num;
    md_inst_id : num;
    md_loc : memory_location;
    md_reaching : num option
  |>
End

Datatype:
  mem_use = <|
    mu_id : num;
    mu_inst_id : num;
    mu_loc : memory_location;
    mu_reaching : num option
  |>
End

Datatype:
  mem_phi = <|
    mp_id : num;
    mp_block : string;
    mp_operands : (num # string) list;
    mp_reaching : num option
  |>
End

Datatype:
  mem_access =
    LiveOnEntry
  | MemDef mem_def
  | MemUse mem_use
  | MemPhi mem_phi
End

Datatype:
  mem_ssa_analysis = <|
    msa_next_id : num;
    msa_defs : (string # mem_def list) list;
    msa_uses : (string # mem_use list) list;
    msa_phis : (string # mem_phi) list;
    msa_volatiles : memory_location list;
    msa_mem_alias : mem_alias_analysis;
    msa_addr_space : addr_space
  |>
End

(* ===== Basic alist helpers ===== *)

Definition alist_lookup_def:
  alist_lookup k [] = NONE /\
  alist_lookup k ((k',v)::rest) =
    if k = k' then SOME v else alist_lookup k rest
End

Definition alist_update_def:
  alist_update k v m =
    (k, v) :: FILTER (λ(k',_). k' <> k) m
End

Definition alist_keys_def:
  alist_keys m = MAP FST m
End

(* ===== Access lookups ===== *)

Definition mem_defs_in_block_def:
  mem_defs_in_block st lbl =
    case alist_lookup lbl st.msa_defs of NONE => [] | SOME ds => ds
End

Definition mem_uses_in_block_def:
  mem_uses_in_block st lbl =
    case alist_lookup lbl st.msa_uses of NONE => [] | SOME us => us
End

Definition mem_phi_in_block_def:
  mem_phi_in_block st lbl = alist_lookup lbl st.msa_phis
End

Definition mem_ssa_all_defs_def:
  mem_ssa_all_defs st = FLAT (MAP SND st.msa_defs)
End

Definition mem_ssa_all_uses_def:
  mem_ssa_all_uses st = FLAT (MAP SND st.msa_uses)
End

Definition mem_ssa_all_phis_def:
  mem_ssa_all_phis st = MAP SND st.msa_phis
End

Definition find_mem_def_by_id_def:
  find_mem_def_by_id id [] = NONE /\
  find_mem_def_by_id id (d::ds) =
    if d.md_id = id then SOME d else find_mem_def_by_id id ds
End

Definition find_mem_use_by_id_def:
  find_mem_use_by_id id [] = NONE /\
  find_mem_use_by_id id (u::us) =
    if u.mu_id = id then SOME u else find_mem_use_by_id id us
End

Definition find_mem_phi_by_id_def:
  find_mem_phi_by_id id [] = NONE /\
  find_mem_phi_by_id id (p::ps) =
    if p.mp_id = id then SOME p else find_mem_phi_by_id id ps
End

Definition mem_ssa_lookup_access_def:
  mem_ssa_lookup_access st id =
    if id = 0 then SOME LiveOnEntry
    else
      case find_mem_def_by_id id (mem_ssa_all_defs st) of
        SOME d => SOME (MemDef d)
      | NONE =>
          (case find_mem_use_by_id id (mem_ssa_all_uses st) of
             SOME u => SOME (MemUse u)
           | NONE =>
               (case find_mem_phi_by_id id (mem_ssa_all_phis st) of
                  SOME p => SOME (MemPhi p)
                | NONE => NONE))
End

Definition mem_access_loc_def:
  mem_access_loc acc =
    case acc of
      LiveOnEntry => memory_location_empty
    | MemDef d => d.md_loc
    | MemUse u => u.mu_loc
    | MemPhi _ => memory_location_empty
End

Definition mem_access_reaching_def:
  mem_access_reaching acc =
    case acc of
      LiveOnEntry => NONE
    | MemDef d => d.md_reaching
    | MemUse u => u.mu_reaching
    | MemPhi p => p.mp_reaching
End

(* ===== Constructing SSA ===== *)

Definition mem_ssa_add_def_def:
  mem_ssa_add_def st lbl d =
    let defs = mem_defs_in_block st lbl in
    st with msa_defs := alist_update lbl (defs ++ [d]) st.msa_defs
End

Definition mem_ssa_add_use_def:
  mem_ssa_add_use st lbl u =
    let uses = mem_uses_in_block st lbl in
    st with msa_uses := alist_update lbl (uses ++ [u]) st.msa_uses
End

Definition mem_ssa_add_phi_def:
  mem_ssa_add_phi st lbl p =
    st with msa_phis := alist_update lbl p st.msa_phis
End

Definition mem_ssa_process_block_definitions_def:
  mem_ssa_process_block_definitions st bpa space bb =
    FOLDL
      (λacc inst.
         let st1 = acc in
         let loc_r = get_read_location bpa inst space in
         let st2 =
           if memory_location_is_empty loc_r then st1
           else
             let u = <| mu_id := st1.msa_next_id;
                        mu_inst_id := inst.inst_id;
                        mu_loc := loc_r;
                        mu_reaching := NONE |> in
             mem_ssa_add_use (st1 with msa_next_id := st1.msa_next_id + 1) bb.bb_label u in
         let loc_w = get_write_location bpa inst space in
         if memory_location_is_empty loc_w then st2
         else
           let d = <| md_id := st2.msa_next_id;
                      md_inst_id := inst.inst_id;
                      md_loc := loc_w;
                      md_reaching := NONE |> in
           mem_ssa_add_def (st2 with msa_next_id := st2.msa_next_id + 1) bb.bb_label d)
      st bb.bb_instructions
End

Definition mem_ssa_get_exit_def_def:
  mem_ssa_get_exit_def 0 fn dom st lbl = SOME 0 /\
  mem_ssa_get_exit_def (SUC fuel) fn dom st lbl =
    case mem_defs_in_block st lbl of
      d::ds => SOME (LAST (d::ds)).md_id
    | [] =>
        (case mem_phi_in_block st lbl of
           SOME p => SOME p.mp_id
         | NONE =>
             case entry_block fn of
               NONE => SOME 0
             | SOME entry_bb =>
                 if lbl = entry_bb.bb_label then SOME 0
                 else
                   (case FLOOKUP dom.immediate_dominators lbl of
                      NONE => SOME 0
                    | SOME NONE => SOME 0
                    | SOME (SOME idom) =>
                        mem_ssa_get_exit_def fuel fn dom st idom))
End

Definition mem_ssa_insert_phi_nodes_def:
  mem_ssa_insert_phi_nodes 0 fn cfg dom st work = st /\
  mem_ssa_insert_phi_nodes (SUC fuel) fn cfg dom st work =
    case work of
      [] => st
    | bb::rest =>
        let frontiers = fmap_lookup_ordset dom.dominator_frontiers bb in
        let (st1, new_work) =
          FOLDL
            (λacc fr.
               let (st_acc, wl) = acc in
               case alist_lookup fr st_acc.msa_phis of
                 SOME _ => (st_acc, wl)
               | NONE =>
                   let preds = fmap_lookup_ordset cfg.cfg_in fr in
                   let ops =
                     FOLDL
                       (λops_acc pred.
                          case mem_ssa_get_exit_def (LENGTH fn.fn_blocks + 1) fn dom st_acc pred of
                            NONE => ops_acc
                          | SOME def_id => ops_acc ++ [(def_id, pred)])
                       [] preds in
                   let phi = <| mp_id := st_acc.msa_next_id;
                               mp_block := fr;
                               mp_operands := ops;
                               mp_reaching := NONE |> in
                   let st' = mem_ssa_add_phi (st_acc with msa_next_id := st_acc.msa_next_id + 1) fr phi in
                   (st', wl ++ [fr]))
            (st, []) frontiers in
        mem_ssa_insert_phi_nodes fuel fn cfg dom st1 (rest ++ new_work)
End

Definition update_use_reaching_def:
  update_use_reaching uses inst_id reach =
    MAP (λu. if u.mu_inst_id = inst_id then u with mu_reaching := SOME reach else u) uses
End

Definition update_def_reaching_def:
  update_def_reaching defs inst_id reach =
    MAP (λd. if d.md_inst_id = inst_id then d with md_reaching := SOME reach else d) defs
End

Definition get_def_id_for_inst_def:
  get_def_id_for_inst inst_id [] = NONE /\
  get_def_id_for_inst inst_id (d::ds) =
    if d.md_inst_id = inst_id then SOME d.md_id else get_def_id_for_inst inst_id ds
End

Definition mem_ssa_entry_def_def:
  mem_ssa_entry_def fn dom st lbl =
    case mem_phi_in_block st lbl of
      SOME p => p.mp_id
    | NONE =>
        case entry_block fn of
          NONE => 0
        | SOME entry_bb =>
            if lbl = entry_bb.bb_label then 0
            else
              (case FLOOKUP dom.immediate_dominators lbl of
                 NONE => 0
               | SOME NONE => 0
               | SOME (SOME idom) =>
                   case mem_ssa_get_exit_def (LENGTH fn.fn_blocks + 1) fn dom st idom of
                     NONE => 0
                   | SOME def_id => def_id)
End

Definition mem_ssa_connect_block_def:
  mem_ssa_connect_block defs uses insts current =
    case insts of
      [] => (defs, uses, current)
    | inst::rest =>
        let uses' = update_use_reaching uses inst.inst_id current in
        let defs' = update_def_reaching defs inst.inst_id current in
        let current' =
          case get_def_id_for_inst inst.inst_id defs of
            NONE => current
          | SOME did => did in
        mem_ssa_connect_block defs' uses' rest current'
End

Definition mem_ssa_connect_defs_uses_def:
  mem_ssa_connect_defs_uses fn cfg dom st =
    FOLDL
      (λacc lbl.
         case lookup_block lbl fn.fn_blocks of
           NONE => acc
         | SOME bb =>
             let defs = mem_defs_in_block acc bb.bb_label in
             let uses = mem_uses_in_block acc bb.bb_label in
             let entry_def = mem_ssa_entry_def fn dom acc bb.bb_label in
             let (defs', uses', _) =
               mem_ssa_connect_block defs uses bb.bb_instructions entry_def in
             let acc1 = acc with msa_defs := alist_update bb.bb_label defs' acc.msa_defs in
             acc1 with msa_uses := alist_update bb.bb_label uses' acc1.msa_uses)
      st cfg.dfs_pre
End

Definition mem_ssa_remove_redundant_phis_def:
  mem_ssa_remove_redundant_phis st =
    let phis =
      FILTER
        (λ(_,phi).
           case phi.mp_operands of
             [] => F
           | (op0,_)::rest =>
               ~EVERY (λ(op,_) . op = op0) rest)
        st.msa_phis in
    st with msa_phis := phis
End

Definition mem_ssa_analyze_def:
  mem_ssa_analyze space ctx fn cfg dom bpa =
    let mem_alias = mem_alias_analyze space ctx fn cfg bpa in
    let st0 =
      <| msa_next_id := 1;
         msa_defs := [];
         msa_uses := [];
         msa_phis := [];
         msa_volatiles := [];
         msa_mem_alias := mem_alias;
         msa_addr_space := space |> in
    let st1 =
      FOLDL
        (λacc lbl.
           case lookup_block lbl fn.fn_blocks of
             NONE => acc
           | SOME bb => mem_ssa_process_block_definitions acc bpa space bb)
        st0 cfg.dfs_pre in
    let work = alist_keys st1.msa_defs in
    let fuel = (LENGTH fn.fn_blocks) * (LENGTH fn.fn_blocks) + 1 in
    let st2 = mem_ssa_insert_phi_nodes fuel fn cfg dom st1 work in
    let st3 = mem_ssa_connect_defs_uses fn cfg dom st2 in
    mem_ssa_remove_redundant_phis st3
End

(* ===== Public API ===== *)

Definition mem_ssa_get_memory_def_def:
  mem_ssa_get_memory_def st inst_id =
    FIND (λd. d.md_inst_id = inst_id) (mem_ssa_all_defs st)
End

Definition mem_ssa_get_memory_use_def:
  mem_ssa_get_memory_use st inst_id =
    FIND (λu. u.mu_inst_id = inst_id) (mem_ssa_all_uses st)
End

Definition mem_ssa_get_memory_defs_def:
  mem_ssa_get_memory_defs st = mem_ssa_all_defs st
End

Definition mem_ssa_get_memory_uses_def:
  mem_ssa_get_memory_uses st = mem_ssa_all_uses st
End

Definition mem_ssa_mark_location_volatile_def:
  mem_ssa_mark_location_volatile st loc =
    let (alias', volatile_loc) = mem_alias_mark_volatile st.msa_mem_alias loc in
    let defs' =
      MAP
        (λ(lbl,defs).
           (lbl, MAP (λd.
                       if mem_alias_may_alias alias' d.md_loc loc then
                         d with md_loc := memory_location_mk_volatile d.md_loc
                       else d) defs))
        st.msa_defs in
    (st with <| msa_mem_alias := alias';
                msa_defs := defs';
                msa_volatiles := st.msa_volatiles ++ [loc] |>, volatile_loc)
End

Definition mem_ssa_walk_aliased_def:
  mem_ssa_walk_aliased 0 st current query_loc visited result = result /\
  mem_ssa_walk_aliased (SUC fuel) st current query_loc visited result =
    case current of
      NONE => result
    | SOME id =>
        if MEM id visited then result
        else
          let visited' = ordset_add id visited in
          case mem_ssa_lookup_access st id of
            NONE => result
          | SOME LiveOnEntry => result
          | SOME (MemUse u) =>
              mem_ssa_walk_aliased fuel st u.mu_reaching query_loc visited' result
          | SOME (MemDef d) =>
              let result' =
                if mem_alias_may_alias st.msa_mem_alias query_loc d.md_loc then
                  ordset_add d.md_id result
                else result in
              mem_ssa_walk_aliased fuel st d.md_reaching query_loc visited' result'
          | SOME (MemPhi p) =>
              let result' =
                FOLDL
                  (λacc (op_id,_).
                     mem_ssa_walk_aliased fuel st (SOME op_id) query_loc visited' acc)
                  result p.mp_operands in
              mem_ssa_walk_aliased fuel st p.mp_reaching query_loc visited' result'
End

Definition mem_ssa_get_aliased_accesses_def:
  mem_ssa_get_aliased_accesses st access_id =
    if access_id = 0 then []
    else
      case mem_ssa_lookup_access st access_id of
        NONE => []
      | SOME acc =>
          let query_loc = mem_access_loc acc in
          let fuel = (LENGTH (mem_ssa_all_defs st) + LENGTH (mem_ssa_all_phis st) + 1) in
          mem_ssa_walk_aliased fuel st (SOME access_id) query_loc [] []
End

Definition mem_ssa_walk_clobbered_def:
  mem_ssa_walk_clobbered 0 st current query_loc visited = NONE /\
  mem_ssa_walk_clobbered (SUC fuel) st current query_loc visited =
    case current of
      NONE => NONE
    | SOME id =>
        if MEM id visited then NONE
        else
          let visited' = ordset_add id visited in
          case mem_ssa_lookup_access st id of
            NONE => NONE
          | SOME LiveOnEntry => NONE
          | SOME (MemUse u) =>
              mem_ssa_walk_clobbered fuel st u.mu_reaching query_loc visited'
          | SOME (MemDef d) =>
              if memory_location_completely_contains query_loc d.md_loc then SOME d.md_id
              else mem_ssa_walk_clobbered fuel st d.md_reaching query_loc visited'
          | SOME (MemPhi p) =>
              let clobbers =
                FOLDL
                  (λacc (op_id,_).
                     case mem_ssa_walk_clobbered fuel st (SOME op_id) query_loc visited' of
                       NONE => acc
                     | SOME cid => ordset_add cid acc)
                  [] p.mp_operands in
              if LENGTH clobbers > 1 then SOME p.mp_id
              else if clobbers = [] then NONE
              else SOME (HD clobbers)
End

Definition mem_ssa_get_clobbered_access_def:
  mem_ssa_get_clobbered_access st access_id =
    if access_id = 0 then NONE
    else
      case mem_ssa_lookup_access st access_id of
        NONE => NONE
      | SOME acc =>
          let query_loc = mem_access_loc acc in
          let start = mem_access_reaching acc in
          let fuel = (LENGTH (mem_ssa_all_defs st) + LENGTH (mem_ssa_all_phis st) + 1) in
          case mem_ssa_walk_clobbered fuel st start query_loc [] of
            NONE => SOME 0
          | SOME cid => SOME cid
End

val _ = export_theory();
