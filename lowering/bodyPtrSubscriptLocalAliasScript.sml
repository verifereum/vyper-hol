(* Retained local pointers describe the later value, not a snapshot. *)
Theory bodyPtrSubscriptLocalAlias
Ancestors
  compileEnv loweringStateRelDefs exprLowering finite_map

Theorem local_ptrs_rel_retained_root:
  local_ptrs_rel func cenv scopes' ss' /\
  lookup_scopes name scopes' = SOME entry' /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p ss = SOME w /\
  lookup_var p ss' = lookup_var p ss ==>
  val_in_memory entry'.type entry'.value (w2n w) ss'.vs_memory
Proof
  strip_tac >>
  fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >>
  simp[]
QED

Theorem compile_name_vv_ptr_alias:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar ptr_op sz) ==>
  compile_name_vv cenv ty name =
    comp_return (LocatedValue ty (mk_ptr ptr_op LocMemory))
Proof
  simp[compile_name_vv_def]
QED

(* Captured-base classification diagnostic (execution_closure.alias_values).
   No universal ownership predicate is defined by this table.

   CURRENT MEMORY VIEW: eval_expr Name returns MemoryPlace id [] without a
   source read (vyperInterpreter 1538-1542). compile_name_vv_ptr_alias returns
   the original PtrVar operand. unwrap_value for nonword LocMemory returns
   the same operand (exprLowering 965-977). Neither operation allocates or
   copies. local_ptrs_rel_retained_root describes the endpoint entry.value,
   not the entry.value at capture. Use IndexRefresh's current-root refresh
   boundary and endpoint ghost_inv for robust current data. For a nested
   path, source select_result can switch from current to historical after
   an index effect; root refresh alone does not describe that selection.

   HISTORICAL MEMORY VIEW: MemoryPlace retains id and full typed path, not a
   source value snapshot. read_memory_path first evaluates current value and
   only upon failure uses read_popped. Selection is ordered, not arbitrary
   membership. To designate a historical owner use
     entry.popped = before ++ (prefix,owner)::after,
     read_popped entry.type path before = NONE,
     path=prefix++suffix,
     subscripts_type entry.type prefix=SOME ptv,
     evaluate_subscripts ptv owner suffix=INL observed.
   Its target allocation/address and robust representation must be carried
   with that SAME descriptor. historical_owner_pop_counted now updates this
   owner and source scope on the actual counted header write, given robust
   entry representation and suffix offset to the popped array. It covers
   only a Pop SELECTING that owner. A Pop selecting an owner in before or
   after does not automatically frame the watched owner: typed byte ranges
   must be disjoint or a common-enclosing-owner update must be proved.
   record_pop adds/reorders observations; read_popped on the new list must
   be re-inverted to find the new FIRST success. Preserving every old owner
   is unsound as a general invariant (shadowed histories can overlap).

   CAPTURED VALUE: source Value v is immutable as a source constructor, but
   its compiled operand need not be a fresh allocation. A StackValue already
   unwraps identically. A LocMemory LocatedValue unwraps identically too.
   conditional_result (vyperState 1098-1112) retains memory aggregate views,
   while loading primitive/non-memory places into Value. compile_ifexp_arm
   (2425-2434) copies a nonword ONLY when memory layouts differ; equal-layout
   branches reuse unwrap_value. Thus IfExp must be classified using actual
   source result and layout, not assumed to allocate merely by syntax.
   Existing BranchWitness is a scalar counted assignment/JNZ interface; it
   does not frame aggregate buffers. CallResult identifies call result kind,
   not disjointness from future writes (internal returns may be LocatedValue).

   MATERIALIZED/COPIED VALUE: compile_materialize_vv (2411-2417) allocates a
   type_memory_bytes temporary then unwraps and stores. Non-memory aggregate
   unwrap calls compile_ensure_in_memory; its copy must be counted. Literals,
   aggregate construction and call result buffers have their own allocation
   and copy sequences. To classify one as an independent snapshot requires
   actual allocation identity/base/size, coverage, source representation and
   robust representation after the copy; syntactic fresh variable alone
   proves none of the byte separation. Subsequent ALLOCA can also REUSE a
   site, so the allocation theorem's fresh-site alternative must be proved.
   allocationPtr.fresh_alloca_old_region_disjoint gives, under
     FLOOKUP s.vs_allocas id=NONE /\ n<dimword(:256) /\
     step_inst_base (mk_inst id ALLOCA [Lit(n2w n)] [out]) s=OK s1 /\
     alloca_inv s /\ FLOOKUP s.vs_allocas aid=SOME(b,sz) /\ b<=i /\ i<b+sz,
   that i NOTIN new_site_bytes s s1. It is a single allocation-edge fact,
   not a theorem about all later writes or copy footprints. Reused-site
   facts exist separately in allocationPtr and require their own premises.

   STORAGE/TRANSIENT/MAPPING: these are not caller memory snapshots. Keep
   source place type/location and current taint/dead-byte contract; external
   calls may change storage/transient, so use refreshed storage_read_live
   with stor_taint_ok and actual source read, not memory-allocation framing.

   Required operational rules (not assumed final-state premises):
   (1) same-owner Pop update: established historical_owner_pop_counted;
   (2) disjoint-write framing: establish write ranges outside watched typed
       bytes, transport robust representation and restricted taint on SAME
       run; MemoryRebuild.val_in_memory_outside_frame handles pure memory
       representation for a single range, not taint or counted execution;
   (3) common-owner mutation: update descriptor's value by actual source
       assignment and target store, then derive each selected child;
   (4) reselection: use source current/read_popped order to reidentify owner,
       and a relation to the target captured address, not merely MEM;
   (5) copied snapshot: establish allocation and copy on the base execution,
       retain its typed region through subsequent effects, including calls.
   Existing ordinary ptr_buf_ok/ghost_kept preserve capacity/provenance but
   do not imply (2)-(5). No broad snapshot theorem or falsehood is claimed.
*)
