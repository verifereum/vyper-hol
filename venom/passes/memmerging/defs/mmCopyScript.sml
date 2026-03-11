(*
 * Memmerging — Copy Group Definitions
 *
 * Ports _Copy dataclass and hazard detection from memmerging.py.
 *
 * A copy_group represents a set of instructions that collectively
 * copy [src, src+length) → [dst, dst+length). Instructions can be
 * merged when their source and destination are contiguous with
 * matching offsets.
 *
 * TOP-LEVEL:
 *   copy_group            — record type
 *   copy_src_interval     — source region
 *   copy_dst_interval     — destination region
 *   copy_overwrites       — does dst overlap an interval?
 *   copy_overwrites_src   — does dst overlap own src?
 *   copy_can_merge        — can two copies be merged?
 *   copy_merge            — merge two copies
 *
 * Helper (hazards):
 *   waw_hazards           — write-after-write conflicts
 *   raw_hazards           — read-after-write conflicts
 *   war_hazards           — write-after-read conflicts
 *   copies_that_overwrite — copies whose dst overlaps a region
 *)

Theory mmCopy
Ancestors
  mmInterval venomInst

(* ===== Copy group ===== *)

(* A copy group: dst/src/length describe the merged region,
   inst_ids tracks which instructions belong to this group.
   Python: _Copy(dst, src, length, insts) *)
Datatype:
  copy_group = <|
    cg_dst : num;
    cg_src : num;
    cg_length : num;
    cg_inst_ids : num list  (* inst_id values, sorted by block position *)
  |>
End

(* Factory for memzero: src = dst so can_merge works for
   overlapping zero regions.
   Python: _Copy.memzero *)
Definition copy_memzero_def:
  copy_memzero dst length inst_ids =
    <| cg_dst := dst; cg_src := dst;
       cg_length := length; cg_inst_ids := inst_ids |>
End

(* ===== Interval projections ===== *)

Definition copy_src_interval_def:
  copy_src_interval cg = mk_interval cg.cg_src cg.cg_length
End

Definition copy_dst_interval_def:
  copy_dst_interval cg = mk_interval cg.cg_dst cg.cg_length
End

(* Does this copy's destination overwrite the given interval?
   Python: _Copy.overwrites *)
Definition copy_overwrites_def:
  copy_overwrites cg iv = interval_overlaps (copy_dst_interval cg) iv
End

(* Does this copy's destination overlap its own source?
   Python: _Copy.overwrites_self_src *)
Definition copy_overwrites_src_def:
  copy_overwrites_src cg = copy_overwrites cg (copy_src_interval cg)
End

(* ===== Merging ===== *)

(* Can two copies be merged? Both source and destination offsets
   must match, and the regions must at least touch.
   Python: _Copy.can_merge
   Uses addition to avoid natural number subtraction underflow:
   src1 - src2 = dst1 - dst2  ⟺  src1 + dst2 = dst1 + src2 *)
Definition copy_can_merge_def:
  copy_can_merge c1 c2 <=>
    (c1.cg_src + c2.cg_dst = c1.cg_dst + c2.cg_src) /\
    c2.cg_dst <= c1.cg_dst + c1.cg_length
End

(* Merge c2 into c1. Precondition: c1.dst <= c2.dst /\ can_merge c1 c2.
   Python: _Copy.merge *)
Definition copy_merge_def:
  copy_merge c1 c2 =
    c1 with <|
      cg_length :=
        MAX (c1.cg_dst + c1.cg_length) (c2.cg_dst + c2.cg_length)
        - c1.cg_dst;
      cg_inst_ids := c1.cg_inst_ids ++ c2.cg_inst_ids
    |>
End

(* ===== Sorted insertion + merge (bisect_left logic) ===== *)

(* Insert a new copy into the sorted list and merge with neighbors.
   Python: _add_copy *)
Definition insert_sorted_def:
  insert_sorted [] cg = [cg] /\
  insert_sorted (c :: rest) cg =
    if cg.cg_dst < c.cg_dst then cg :: c :: rest
    else c :: insert_sorted rest cg
End

(* Merge adjacent pairs where possible, left to right.
   Python: the merge loop in _add_copy *)
Definition merge_adjacent_def:
  merge_adjacent [] = [] /\
  merge_adjacent [c] = [c] /\
  merge_adjacent (c1 :: c2 :: rest) =
    if copy_can_merge c1 c2 then
      merge_adjacent (copy_merge c1 c2 :: rest)
    else
      c1 :: merge_adjacent (c2 :: rest)
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End

(* Insert a new copy into the sorted list and merge with neighbors.
   Python: _add_copy *)
Definition add_copy_def:
  add_copy copies new_cg =
    merge_adjacent (insert_sorted copies new_cg)
End

(* ===== Hazard detection ===== *)

(* Copies in list whose dst overlaps the given interval.
   Python: _copies_that_overwrite *)
Definition copies_that_overwrite_def:
  copies_that_overwrite copies iv =
    FILTER (\cg. copy_overwrites cg iv) copies
End

(* Write-after-write hazards: existing copies whose dst overlaps
   new_copy's dst, unless they can be merged.
   Python: _write_after_write_hazards *)
Definition waw_hazards_def:
  waw_hazards copies new_cg =
    FILTER (\cg.
      ~copy_can_merge cg new_cg /\ ~copy_can_merge new_cg cg /\
      copy_overwrites new_cg (copy_dst_interval cg))
    copies
End

(* Read-after-write hazards: existing copies whose dst overlaps
   new_copy's src (they overwrote data we need to read).
   Python: _read_after_write_hazards *)
Definition raw_hazards_def:
  raw_hazards copies new_cg =
    copies_that_overwrite copies (copy_src_interval new_cg)
End

(* Write-after-read hazards: new_copy's dst overlaps existing
   copies' src (we would overwrite data they need to read).
   Python: _write_after_read_hazards *)
Definition war_hazards_def:
  war_hazards copies new_cg =
    FILTER (\cg. copy_overwrites new_cg (copy_src_interval cg)) copies
End
