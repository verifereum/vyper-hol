(* Boundary probe: the live value extent, not its full static capacity,
   is the range available to the bytestring adapter. *)
Theory bodyIfExpMemoryAdapter
Ancestors
  bodyMemoryDefs loweringPosts instMemFrontier compileEnv
  finite_map arithmetic abiBuiltinAllocation exprSimHyps

Theorem ifexp_located_footprint_frontier:
  vv_at ce cx t sa sb es raw (LocatedValue t' p) s /\
  p.ptr_location = LocMemory /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  0 < val_footprint tv v /\
  stmt_state_rel ctx func ce cx es s /\ alloca_next_valid s ==>
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac
  >- (drule_all alloca_region_below_frontier >> simp[]) >>
  drule_all body_local_region_frontier >> decide_tac
QED

(* Falsification of the proposed rounded-copy/live-footprint implication.
   This is an interface counterexample, not yet a counterexample to simulation. *)
Theorem ifexp_rounded_copy_exceeds_live_footprint:
  val_footprint (BaseTV (BytesT (Dynamic 1))) (BytesV [0w]) = 33 /\
  32 + 32 * word_size 1 = 64 /\
  ~(32 + 32 * word_size 1 <=
    val_footprint (BaseTV (BytesT (Dynamic 1))) (BytesV [0w]))
Proof
  EVAL_TAC
QED

Theorem ifexp_copy_frontier_after_growth:
  p + 32 + n <= frontier /\ 32 <= capacity ==>
  p + 32 + 32 * word_size n <= frontier + capacity
Proof
  mp_tac abi_builtin_rounded_padding_bound >> decide_tac
QED

(* Small execution test of the new-allocation branch. *)
Theorem ifexp_fresh_alloc_padding_probe:
  s.vs_alloca_next = 33 /\ FLOOKUP s.vs_allocas 7 = NONE ==>
  ?u. exec_alloca (mk_inst 7 ALLOCA [Lit 64w] ["%probe"]) s (64w:bytes32) = OK u /\
      u.vs_alloca_next = 97 /\
      FLOOKUP u.vs_allocas 7 = SOME (33,64) /\
      32 + 32 * word_size 0 <= u.vs_alloca_next /\
      32 + 32 * word_size 1 <= u.vs_alloca_next /\
      32 + 32 * word_size 32 <= u.vs_alloca_next
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
       venomStateTheory.update_var_def, wordsTheory.dimword_def] >> EVAL_TAC
QED
