Theory abiEncodeArgsWindows
Ancestors
  exprSimDefs exprSimProps loweringPosts compileEnv valueEncoding valueEncodingProofs entryDecodeStaticProps
  vyperLookup finite_map

(* A dynamic local's exempt header is fixed by the represented value at
   both endpoints.  The tail frame is over the actual requested window. *)
Theorem dynarray_window_from_header_tail:
  !tv vs off len m0 m1.
    val_in_memory tv (ArrayV (DynArrayV vs)) off m0 /\
    val_in_memory tv (ArrayV (DynArrayV vs)) off m1 /\
    32 <= len /\
    mem_bytes_at (off + 32) (len - 32) m1 =
    mem_bytes_at (off + 32) (len - 32) m0 ==>
    mem_bytes_at off len m1 = mem_bytes_at off len m0
Proof
  rpt strip_tac >>
  `mem_word_at off m1 = mem_word_at off m0`
    by gvs[val_in_memory_def] >>
  `mem_bytes_at off 32 m1 = mem_bytes_at off 32 m0`
    by metis_tac[mem_bytes_at_word_eq] >>
  `len = 32 + (len - 32)` by decide_tac >>
  metis_tac[mem_bytes_at_split_padded]
QED

Theorem local_ptrs_rel_value_at:
  !func ce sc ss name entry p sz w.
    local_ptrs_rel func ce sc ss /\
    lookup_scopes name sc = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p ss = SOME w ==>
    val_in_memory entry.type entry.value (w2n w) ss.vs_memory /\
    type_memory_size entry.type <= sz
Proof
  rpt strip_tac >> gvs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem dynamic_local_window_kept:
  !func ce es es1 ss0 ss1 name entry p sz w etv n vs.
    local_ptrs_rel func ce es.scopes ss0 /\
    local_ptrs_rel func ce es1.scopes ss1 /\
    lookup_scopes name es.scopes = SOME entry /\
    lookup_scopes name es1.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p ss0 = SOME w /\ lookup_var p ss1 = SOME w /\
    entry.type = ArrayTV etv (Dynamic n) /\
    entry.value = ArrayV (DynArrayV vs) /\
    locals_kept ce es es1 ss0 ss1 ==>
    mem_bytes_at (w2n w) (val_footprint entry.type entry.value) ss1.vs_memory =
    mem_bytes_at (w2n w) (val_footprint entry.type entry.value) ss0.vs_memory
Proof
  rpt strip_tac >>
  `type_memory_size entry.type <= sz` by
    metis_tac[local_ptrs_rel_value_at] >>
  `local_region ce es.scopes ss0 name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) sz ss1.vs_memory =
   mem_bytes_at (w2n w) sz ss0.vs_memory` by
    (fs[locals_kept_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  sym_tac >> first_x_assum irule >>
  gvs[val_footprint_def]
QED

Theorem dynamic_local_window_scopes_kept:
  !func ce es es1 ss0 ss1 name entry p sz w etv n vs.
    es1.scopes = es.scopes /\
    local_ptrs_rel func ce es.scopes ss0 /\
    local_ptrs_rel func ce es1.scopes ss1 /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p ss0 = SOME w /\ lookup_var p ss1 = SOME w /\
    entry.type = ArrayTV etv (Dynamic n) /\
    entry.value = ArrayV (DynArrayV vs) /\
    locals_kept ce es es1 ss0 ss1 ==>
    mem_bytes_at (w2n w) (val_footprint entry.type entry.value) ss1.vs_memory =
    mem_bytes_at (w2n w) (val_footprint entry.type entry.value) ss0.vs_memory
Proof
  rpt strip_tac >> irule dynamic_local_window_kept >> metis_tac[]
QED
