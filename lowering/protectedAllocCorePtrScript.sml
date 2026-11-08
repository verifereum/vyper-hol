(* Shared implementation of the protected-source allocation boundary. *)
Theory protectedAllocCorePtr
Ancestors protectedAllocExteriorPtr

Theorem alloca_step_endpoint_frame:
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK t ==>
  t.vs_memory = s.vs_memory /\
  (!aid. aid <> id ==> FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  ACCEPT_TAC protectedAllocExteriorPtrTheory.alloca_step_endpoint_frame
QED

Theorem alloca_step_resource_observations:
  alloca_inv s /\ alloca_room ctx func s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==> sz = n) ==>
  ?t b. step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    alloca_inv t /\ alloca_room ctx func t /\
    lookup_var out t = SOME (n2w b) /\ FLOOKUP t.vs_allocas id = SOME (b,n) /\
    b+n <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz))
Proof
  ACCEPT_TAC protectedAllocExteriorPtrTheory.alloca_step_resource_observations
QED

Theorem compile_alloc_buffer_protected_source_core_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf tv v /\ val_footprint tv v <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) ==>
  ?out b G1 tn1 sf.
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==> val_in_memory tv v p mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz)) /\
    sf.vs_memory = s.vs_memory /\
    (!aid. aid <> sa.cs_next_id ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    sf.vs_halted = s.vs_halted /\ sf.vs_current_bb = s.vs_current_bb /\
    sf.vs_inst_idx = SUC s.vs_inst_idx
Proof
  strip_tac >> drule_all compile_alloc_buffer_protected_source_exterior_ptr >>
  disch_then (qspecl_then [`cx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`out`,`b`,`G1`,`tn1`,`sf`] >> asm_rewrite_tac[]
QED
