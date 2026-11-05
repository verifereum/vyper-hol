(* Bounded shadow-memory experiment, not a counterexample to structlit_expr_ptr_ok.
   The candidate callee relation universally closes every represented value
   under mem_agree_outside tn.t_mem s.vs_memory.  Existing
   normalizationAllocPtr.alloca_step_expr_robust_preserved establishes its
   allocation boundary for OLD represented expressions; it must not require
   a representation for an uninitialized allocation, as shown below.

   S1's same-type return-store boundary is compile_store_memory_run_capacity
   (alan-ref/base/valueCopyScript.sml.txt:665): it consumes a single-memory
   val_in_memory and produces a single-memory val_in_memory.  The local
   robust-copy closure is already robust_val_in_memory_copy_transport; the
   missing premise is closure of expr_val_rel at the ACTUAL return type on
   entry to that store.  Neither single-memory postcondition supplies it.
   No duplicate allocation/copy transport lemmas are introduced here. *)
Theory bodyPtrStructLitShadow
Ancestors
  allocationPtr representationCleanPtr normalizationAllocPtr
  robustCopyTransportPtr bodyPtrDefs ptrDiscipline venomInst finite_map
  pred_set arithmetic

Theorem fresh_alloca_not_shadow_primitive:
  !id n out s s1 tn ty v.
    FLOOKUP s.vs_allocas id = NONE /\ 0 < n /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    ((?b. v = BoolV b) \/ (?k. v = IntV k) \/
     (?k. v = FlagV k) \/ (?k. v = DecimalV k)) ==>
    ~(!mem. mem_agree_outside
       (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
       s1.vs_memory mem ==>
       val_in_memory ty v s.vs_alloca_next mem)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  `!i. s.vs_alloca_next <= i /\ i < s.vs_alloca_next + 32 ==>
    i NOTIN
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_prim_clean >>
     qexistsl [`s.vs_alloca_next`, `s1.vs_memory`, `ty`, `v`] >> simp[]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  qpat_x_assum `!i. _ ==> i NOTIN _`
    (qspec_then `s.vs_alloca_next` mp_tac) >> simp[]
QED
