(*
 * Memory Alias Analysis
 *
 * Port of venom/analysis/mem_alias.py.
 *)

Theory memAliasAnalysis
Ancestors
  list
  orderedSet
  memoryLocation basePtrAnalysis addrSpace
  irOps

Type alias_sets = ``:(memory_location # memory_location list) list``

Datatype:
  mem_alias_analysis = <|
    alias_sets : alias_sets
  |>
End

Definition alias_lookup_def:
  alias_lookup m k =
    case ALOOKUP m k of NONE => [] | SOME v => v
End

Definition alias_update_def:
  alias_update m k v = (k, v) :: FILTER (λ(kk,_). kk <> k) m
End

Definition alias_keys_def:
  alias_keys m = MAP FST m
End

Definition analyze_mem_location_def:
  analyze_mem_location m loc =
    let m1 = if MEM loc (alias_keys m) then m else alias_update m loc [] in
    FOLDL
      (λacc other.
         if memory_location_may_overlap loc other then
           let s1 = alias_lookup acc loc in
           let s2 = alias_lookup acc other in
           let acc1 = alias_update acc loc (ordset_add other s1) in
           alias_update acc1 other (ordset_add loc s2)
         else acc)
      m1 (alias_keys m1)
End

Definition mem_alias_analyze_def:
  mem_alias_analyze space ctx fn cfg bpa =
    let m =
      FOLDL
        (λacc bb.
           FOLDL
             (λacc2 inst.
                let loc_r = get_read_location bpa inst space in
                let acc3 = analyze_mem_location acc2 loc_r in
                let loc_w = get_write_location bpa inst space in
                analyze_mem_location acc3 loc_w)
             acc bb.bb_instructions)
        [] fn.fn_blocks in
    <| alias_sets := m |>
End

Definition mem_alias_may_alias_def:
  mem_alias_may_alias analysis loc1 loc2 =
    if loc1.ml_volatile \/ loc2.ml_volatile then
      memory_location_may_overlap loc1 loc2
    else if MEM loc1 (alias_keys analysis.alias_sets) /\ MEM loc2 (alias_keys analysis.alias_sets) then
      MEM loc2 (alias_lookup analysis.alias_sets loc1)
    else
      memory_location_may_overlap loc1 loc2
End

Definition mem_alias_mark_volatile_def:
  mem_alias_mark_volatile analysis loc =
    let volatile_loc = memory_location_mk_volatile loc in
    if MEM loc (alias_keys analysis.alias_sets) then
      let s = alias_lookup analysis.alias_sets loc in
      let m1 = alias_update analysis.alias_sets volatile_loc [volatile_loc] in
      let m2 = alias_update m1 volatile_loc (ordset_add loc (alias_lookup m1 volatile_loc)) in
      let m3 = alias_update m2 loc (ordset_add volatile_loc (alias_lookup m2 loc)) in
      let m4 =
        FOLDL
          (λacc other.
             if other <> loc /\ other <> volatile_loc then
               let s1 = alias_lookup acc volatile_loc in
               let s2 = alias_lookup acc other in
               let acc1 = alias_update acc volatile_loc (ordset_add other s1) in
               alias_update acc1 other (ordset_add volatile_loc s2)
             else acc)
          m3 s in
      (<| alias_sets := m4 |>, volatile_loc)
    else (analysis, volatile_loc)
End

val _ = export_theory();
