Theory extRetRecursiveScratchProbePtr
Ancestors
  extRetScratchInitPtr fragGasPathPtr bodyPtrDefs loweringPosts
  compileEnv context codegenRel emitHelper venomState venomInst
  venomMemDefs valueEncoding words finite_map pred_set arithmetic

(* Caller-facing test: a registered ancestor survives a child allocation
   and its initializing store, whether the child site is new or reused.
   The statement deliberately retains the real allocator entry premises.
   In particular, this is not a producer of stmt_state_rel after encoding. *)
Theorem nested_scratch_preserves_registered_parent:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand init s = SOME w /\
  op_taint tn init = {} /\
  (!v. init = Var v ==> not_fresh_at sa v) /\
  FLOOKUP s.vs_allocas parent = SOME (p,32) /\
  parent <> sa.cs_next_id /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    FLOOKUP sf.vs_allocas parent = SOME (p,32) /\
    mload addr sf = w /\ mload p sf = mload p s /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem) /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32}
      sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP sf.vs_allocas aid = SOME site) /\ alloca_inv sf /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all scratch_word_init_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `mload p sf = mload p s /\
   (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem)` by
    (drule_all scratch_word_init_registered_cursor >> simp[]) >>
  qexistsl_tac [`ip`, `addr`, `Gf`, `tnf`, `sf`] >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

(* Interface audit (not an assertion that the frozen theorem is false).

   At extRetAbiChildComposePtr$abi_dynamic_child_compose_counted_ptr's
   callback, the actual child entry is sp and the compiler entry is sc.
   Available projections include memory equality, t_mem equality, clean
   parent cursor, destination coverage, and an old-operand frame. Neither
   stmt_state_rel ctx fn cenv cx es sp nor alloca_room ctx fn sp nor
   alloca_inv sp is in that callback's antecedent. Allocation registration
   and alloca_next are also absent. The outer result drops them too.

   Therefore the exact first unavailable scratch-init premise is:
     stmt_state_rel ctx fn cenv cx es sp
   with a second independent premise:
     not_local_ptr cenv es.scopes
       (STRING #"%" (toString sc.cs_next_var)).
   Robust val_in_memory alone supplies neither assertion.

   Even at the parent-init result, scratch_word_init_ambient_counted_ptr
   exports alloca_inv and registration persistence but not stmt_state_rel
   or alloca_room. Consequently applying the next allocator cannot be
   justified merely by the endpoint of the preceding scratch-init rule.
   The theorem above checks the registered-parent preservation step only;
   it deliberately does not pretend to instantiate a nested allocator.

   The state-independent allocaSiteResource$alloca_site32_execute handles
   first encounter and reuse, using alloca_room, alloca_inv and a reused
   site size of 32. Its alloca_site32_reentry handles the repeated site.
   Neither needs stmt_state_rel or not_local_ptr. For source protection,
   alloca_site_execute_protected additionally requires the live source
   window below alloca_next and disjoint from the reused site. Those are
   genuine threaded resources, absent from the callback above; robust
   source representation does not imply them. Registered parent/dst
   protection instead follows from alloca_site_preserved_protection.

   Before a full nested counted probe can close, a recursive execution
   interface must retain allocation room, registered-site sizes/persistence,
   source-window protection against all child-owned sites, and operand
   placement. A counted allocation boundary based on those resources can
   avoid re-establishing semantic stmt_state_rel after arbitrary children.
   No protected source change is made or required by this audit.
*)
