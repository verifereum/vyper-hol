(* State relations for the Mem2Var simulation. *)
Theory mem2varInvariant
Ancestors
  mem2varDefs mem2varFrame contextCodegenRel venomMemDefs finite_map list

(* Terminal states retain every byte outside an actually promoted site.
   RETURN materialization may change the instruction index, and an aborting
   forwarding copy need not retain the promoted-variable synchronization. *)
Definition m2v_public_rel_def:
  m2v_public_rel fn s1 s2 <=>
    m2v_equiv (m2v_fresh_vars fn) s1 s2 /\
    (!i. ~in_promoted_region fn s1 i ==> mem_byte i s1 = mem_byte i s2)
End

(* Safety of actual accesses left unchanged by promotion. Unreached
   instructions in the same variable environment impose no obligations. *)
Definition m2v_access_safe_def:
  m2v_access_safe fn inst s <=>
    ~(?ao pvar.
      FIND (\(ao, pvar, sz). MEM (Var ao) inst.inst_operands)
        (m2v_promo_list fn) = SOME (ao, pvar, 32)) ==>
    !off len i.
      MEM (off, len)
        (source_memory_read_ranges inst s ++ source_memory_write_ranges inst s) /\
      off <= i /\ i < off + len ==> ~in_promoted_region fn s i
End

(* Allocation-output bridge. The reverse clause also records that a site
   already allocated by this function has its SSA pointer variable bound. *)
Definition alloca_bridge_def:
  alloca_bridge fn s <=>
    (!ao pvar sz inst.
      MEM (ao, pvar, sz) (m2v_promo_list fn) /\
      MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [ao] ==>
      (!addr. lookup_var ao s = SOME addr ==>
        FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n addr, sz)) /\
      (!base sz'. FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz') ==>
        sz' = sz /\
        ?addr. lookup_var ao s = SOME addr /\ w2n addr = base))
End
