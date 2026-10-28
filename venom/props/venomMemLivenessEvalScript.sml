(* TOP-LEVEL: exact fuelled base-pointer and memory-liveness iterations. *)
Theory venomMemLivenessEval
Ancestors concretizeMemLocDefs arithmetic finite_map

Theorem ml_lookup_empty:
  ml_lookup FEMPTY addr = []
Proof
  simp[ml_lookup_def]
QED

Theorem ml_lookup_update:
  ml_lookup (live |+ (key,addresses)) addr =
    if key = addr then addresses else ml_lookup live addr
Proof
  Cases_on `key = addr` >> simp[ml_lookup_def, FLOOKUP_UPDATE]
QED

(* Name the actual accumulator operation so evaluation need not expand a
   lambda containing the entire live-set map before reaching a boundary. *)
Definition ml_add_live_addr_def:
  ml_add_live_addr addr live alloc =
    let cur = case FLOOKUP live alloc of SOME addresses => addresses | NONE => [] in
    live |+ (alloc, smerge inst_addr_to [addr] cur)
End

Theorem ml_add_live_addr_eq:
  ml_add_live_addr addr =
    (\live alloc.
      let cur = case FLOOKUP live alloc of SOME addresses => addresses | NONE => [] in
      live |+ (alloc, smerge inst_addr_to [addr] cur))
Proof
  simp[FUN_EQ_THM, ml_add_live_addr_def]
QED

Theorem ml_add_live_addr_step:
  ml_add_live_addr addr live alloc =
    live |+ (alloc, smerge inst_addr_to [addr]
      (case FLOOKUP live alloc of SOME addresses => addresses | NONE => []))
Proof
  simp[ml_add_live_addr_def]
QED

Definition ml_add_live_addrs_def:
  ml_add_live_addrs addr live allocs =
    FOLDL (ml_add_live_addr addr) live allocs
End

Theorem ml_add_live_addrs_nil:
  ml_add_live_addrs addr live [] = live
Proof
  simp[ml_add_live_addrs_def]
QED

Theorem ml_add_live_addrs_cons:
  ml_add_live_addrs addr live (alloc::rest) =
    ml_add_live_addrs addr (ml_add_live_addr addr live alloc) rest
Proof
  simp[ml_add_live_addrs_def]
QED

Theorem ml_livesets_insts_step:
  ml_livesets_insts bb_label liveat used live ((idx,inst)::rest) =
    let addr = (bb_label,idx) in
    let both = sinter alloc_to (ml_lookup liveat addr) (ml_lookup used addr) in
    let live' = FOLDL (ml_add_live_addr addr) live both in
    ml_livesets_insts bb_label liveat used live' rest
Proof
  simp[Once ml_livesets_insts_def, ml_add_live_addr_eq]
QED

Theorem ml_mark_stores_insts_step:
  ml_mark_stores_insts bpr bb_label live ((idx,inst)::rest) =
    let write_allocas = find_base_allocas_opt bpr (inst_write_op inst) in
    let addr = (bb_label,idx) in
    let live' = FOLDL (ml_add_live_addr addr) live write_allocas in
    ml_mark_stores_insts bpr bb_label live' rest
Proof
  simp[Once ml_mark_stores_insts_def, ml_add_live_addr_eq]
QED

(* Eliminate the continuation's lets while the semantic inputs are symbolic.
   Instantiating these equations then preserves each large map as an argument. *)
Theorem ml_livesets_insts_step_direct:
  ml_livesets_insts bb_label liveat used live ((idx,inst)::rest) =
    ml_livesets_insts bb_label liveat used
      (FOLDL (ml_add_live_addr (bb_label,idx)) live
        (sinter alloc_to (ml_lookup liveat (bb_label,idx))
          (ml_lookup used (bb_label,idx)))) rest
Proof
  simp[ml_livesets_insts_step]
QED

Theorem ml_mark_stores_insts_step_direct:
  ml_mark_stores_insts bpr bb_label live ((idx,inst)::rest) =
    ml_mark_stores_insts bpr bb_label
      (FOLDL (ml_add_live_addr (bb_label,idx)) live
        (find_base_allocas_opt bpr (inst_write_op inst))) rest
Proof
  simp[ml_mark_stores_insts_step]
QED

Theorem ml_livesets_insts_step_fold:
  ml_livesets_insts bb_label liveat used live ((idx,inst)::rest) =
    ml_livesets_insts bb_label liveat used
      (ml_add_live_addrs (bb_label,idx) live
        (sinter alloc_to (ml_lookup liveat (bb_label,idx))
          (ml_lookup used (bb_label,idx)))) rest
Proof
  simp[ml_livesets_insts_step_direct, ml_add_live_addrs_def]
QED

Theorem ml_mark_stores_insts_step_fold:
  ml_mark_stores_insts bpr bb_label live ((idx,inst)::rest) =
    ml_mark_stores_insts bpr bb_label
      (ml_add_live_addrs (bb_label,idx) live
        (find_base_allocas_opt bpr (inst_write_op inst))) rest
Proof
  simp[ml_mark_stores_insts_step_direct, ml_add_live_addrs_def]
QED

Definition ml_livesets_blocks_def:
  ml_livesets_blocks liveat used live blocks =
    FOLDL (\live bb.
      ml_livesets_insts bb.bb_label liveat used live
        (MAPi (\i inst. (i,inst)) bb.bb_instructions)) live blocks
End

Theorem ml_livesets_blocks_nil:
  ml_livesets_blocks liveat used live [] = live
Proof
  simp[ml_livesets_blocks_def]
QED

Theorem ml_livesets_blocks_cons:
  ml_livesets_blocks liveat used live (bb::rest) =
    ml_livesets_blocks liveat used
      (ml_livesets_insts bb.bb_label liveat used live
        (MAPi (\i inst. (i,inst)) bb.bb_instructions)) rest
Proof
  simp[ml_livesets_blocks_def]
QED

Theorem ml_compute_livesets_blocks:
  ml_compute_livesets liveat used func =
    ml_livesets_blocks liveat used FEMPTY func.fn_blocks
Proof
  simp[ml_compute_livesets_def, ml_livesets_blocks_def]
QED

Definition ml_mark_stores_blocks_def:
  ml_mark_stores_blocks bpr live blocks =
    FOLDL (\live bb.
      ml_mark_stores_insts bpr bb.bb_label live
        (MAPi (\i inst. (i,inst)) bb.bb_instructions)) live blocks
End

Theorem ml_mark_stores_blocks_nil:
  ml_mark_stores_blocks bpr live [] = live
Proof
  simp[ml_mark_stores_blocks_def]
QED

Theorem ml_mark_stores_blocks_cons:
  ml_mark_stores_blocks bpr live (bb::rest) =
    ml_mark_stores_blocks bpr
      (ml_mark_stores_insts bpr bb.bb_label live
        (MAPi (\i inst. (i,inst)) bb.bb_instructions)) rest
Proof
  simp[ml_mark_stores_blocks_def]
QED

Theorem ml_mark_stores_live_blocks:
  ml_mark_stores_live bpr func live =
    ml_mark_stores_blocks bpr live func.fn_blocks
Proof
  simp[ml_mark_stores_live_def, ml_mark_stores_blocks_def]
QED

Theorem ml_iterate_fuel_unfold:
  ml_iterate_fuel fuel bpr mems_used alloca_sizes live_pallocas cfg func
    liveat used =
  if fuel = 0 then (liveat,used)
  else
    let (changed,liveat',used') =
      ml_one_pass bpr mems_used alloca_sizes live_pallocas cfg func liveat used in
    if changed then
      ml_iterate_fuel (fuel - 1) bpr mems_used alloca_sizes live_pallocas
        cfg func liveat' used'
    else (liveat',used')
Proof
  Cases_on `fuel` >> simp[Once ml_iterate_fuel_def]
QED

Theorem bp_iterate_fuel_unfold:
  bp_iterate_fuel fuel func order result =
  if fuel = 0 then result
  else
    let (changed,result') = bp_one_pass func order result in
    if changed then bp_iterate_fuel (fuel - 1) func order result'
    else result'
Proof
  Cases_on `fuel` >> simp[Once bp_iterate_fuel_def]
QED
