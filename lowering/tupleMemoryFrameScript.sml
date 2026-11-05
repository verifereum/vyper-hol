(*
 * A write into a local can overlap a tuple's elements already read, but not
 * the elements after them.
 *
 * TOP-LEVEL:
 *   tuple_in_memory_unread_suffix — the unread elements survive the write
 *   tuple_container_transport — where the tuple lies, after the write
 *)
Theory tupleMemoryFrame
Ancestors
  exprSimProps
  tupleMemoryLayout compileEnv localPtrsProps  valueEncodingProps
  valueEncodingProofs arithmetic venomMemDefs exprSimAggregateChildren
  vyperEvalPreservesScopes

Theorem memory_write_unread_suffix:
  !b sz addr off elem suffix_len dst dsz written mem mem'.
    b <= addr /\ addr + off + elem + suffix_len <= b + sz /\
    written <= elem /\ written <= dsz /\
    (dst <= addr \/ regions_disjoint b sz dst dsz) /\
    (!a len. a + len <= dst \/ dst + written <= a ==>
       mem_bytes_at a len mem' = mem_bytes_at a len mem) ==>
    mem_bytes_at (addr + off + elem) suffix_len mem' =
    mem_bytes_at (addr + off + elem) suffix_len mem
Proof
  cheat
QED

Theorem local_regions_write_position:
  !func cenv scopes s name b sz dest dst dsz addr.
    local_ptrs_rel func cenv scopes s /\
    local_region cenv scopes s name b sz /\
    local_region cenv scopes s dest dst dsz /\ b <= addr ==>
    dst <= addr \/ regions_disjoint b sz dst dsz
Proof
  cheat
QED

Theorem allocation_local_write_position:
  !func cenv scopes s aid b sz dest dst dsz addr.
    alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
    FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
    local_region cenv scopes s dest dst dsz /\ b <= addr ==>
    dst <= addr \/ regions_disjoint b sz dst dsz
Proof
  cheat
QED

(* Both ownership alternatives admit overlap only at or before the tuple. *)
Theorem tuple_container_write_position:
  !func cenv scopes s b sz dest dst dsz addr.
    alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes s name b sz)) /\
    local_region cenv scopes s dest dst dsz /\ b <= addr ==>
    dst <= addr \/ compileEnv$regions_disjoint b sz dst dsz
Proof
  cheat
QED

Theorem tuple_container_unread_suffix:
  !func cenv scopes s b sz dest dst dsz addr off elem suffix_len written mem'.
    alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes s name b sz)) /\
    local_region cenv scopes s dest dst dsz /\
    b <= addr /\ addr + off + elem + suffix_len <= b + sz /\
    written <= elem /\ written <= dsz /\
    (!a len. a + len <= dst \/ dst + written <= a ==>
       mem_bytes_at a len mem' = mem_bytes_at a len s.vs_memory) ==>
    mem_bytes_at (addr + off + elem) suffix_len mem' =
    mem_bytes_at (addr + off + elem) suffix_len s.vs_memory
Proof
  cheat
QED

Theorem tuple_in_memory_unread_suffix:
  !func cenv scopes s b sz dest dst dsz addr off elem vs tvs written mem'.
    alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes s name b sz)) /\
    local_region cenv scopes s dest dst dsz /\
    b <= addr /\
    addr + off + elem + type_memory_size_list tvs <= b + sz /\
    written <= elem /\ written <= dsz /\
    (!a len. a + len <= dst \/ dst + written <= a ==>
       mem_bytes_at a len mem' = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory vs tvs (addr + off + elem) s.vs_memory /\
    tuple_val_wf vs tvs ==>
    tuple_in_memory vs tvs (addr + off + elem) mem'
Proof
  cheat
QED

(* The region depends on whether a name is live, not its current value/type.
   Thus repeated assignment to a containing local does not lose ownership. *)
Theorem local_region_scopes_domain:
  !cenv scopes scopes' s name b sz.
    MAP FDOM scopes = MAP FDOM scopes' ==>
    (local_region cenv scopes s name b sz <=>
     local_region cenv scopes' s name b sz)
Proof
  cheat
QED

Theorem tuple_container_transport:
  !cenv sa scopes scopes' s t b sz.
    MAP FDOM scopes = MAP FDOM scopes' /\ local_ptrs_reserved cenv sa /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
              FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes s name b sz)) ==>
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes' t name b sz))
Proof
  cheat
QED
