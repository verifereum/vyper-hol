(* Boundary probe: the live value extent, not its full static capacity,
   is the range available to the bytestring adapter. *)
Theory bodyIfExpMemoryAdapter
Ancestors
  bodyMemoryDefs loweringPosts instMemFrontier compileEnv
  finite_map arithmetic abiBuiltinAllocation exprSimHyps
  exprLowering fragGasPathMem context vyperAST

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

(* The two no-code unwrap cases share the same checked identity boundary. *)
Theorem ifexp_unwrap_identity_path:
  (vv = StackValue ty op \/
   ?p. vv = LocatedValue ty p /\ ~is_word_type ty /\
       p.ptr_location = LocMemory /\ p.ptr_operand = op) /\
  ~s.vs_halted /\ alloca_history func s ==>
  unwrap_value ce vv sa = (op,sa) /\
  gas_path_mem ctx func s 0 (OK s) /\
  alloca_history func s /\ s.vs_alloca_next <= s.vs_alloca_next
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED

(* Reuse does not provide padding slack for a later, disjoint live source.
   This is only an allocation-interface countermodel, not a simulation one. *)
Theorem ifexp_reused_alloc_padding_probe:
  s.vs_allocas = FEMPTY |+ (7,(0,64)) |+ (8,(64,33)) /\
  s.vs_alloca_next = 97 ==>
  alloca_inv s /\
  ?u. exec_alloca (mk_inst 7 ALLOCA [Lit 64w] ["%probe"]) s (64w:bytes32) = OK u /\
      u.vs_alloca_next = 97 /\
      64 + 32 + 1 <= u.vs_alloca_next /\
      ~(64 + 32 + 32 * word_size 1 <= u.vs_alloca_next) /\
      0 + 32 + 32 * word_size 1 <= u.vs_alloca_next
Proof
  strip_tac >> conj_tac
  >- (simp[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.allocas_non_overlapping_def,
           venomMemDefsTheory.alloca_next_valid_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> decide_tac) >>
  simp[venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
       venomStateTheory.update_var_def, FLOOKUP_UPDATE] >> EVAL_TAC
QED

