(* Counted load boundaries; semantic liveness is supplied separately. *)
Theory augAssignPtrLoad
Ancestors
  augAssignPtrInterfaces typedCopyPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  venomInst venomState venomExecSemantics ptrSafeRun representationCleanPtr
  finite_map vyperValue

Theorem mload_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  ptr_covers G tn src s 32 /\
  step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u)
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MLOAD [Var src] [tmp]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  mp_tac (Q.INST [`lo` |-> `0`,
    `i` |-> `mk_inst id MLOAD [Var src] [tmp]`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[update_var_def] >>
  `step_inst 0 ctx (mk_inst id MLOAD [Var src] [tmp]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_halted >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem ghost_inv_scalar_local_clean:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  ((?b. entry.value = BoolV b) \/ (?n. entry.value = IntV n) \/
   (?k. entry.value = FlagV k) \/ (?n. entry.value = DecimalV n)) ==>
  !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_prim_clean >>
  qexistsl_tac [`w2n a`, `s.vs_memory`, `entry.type`, `entry.value`] >> simp[] >>
  gvs[ghost_inv_def] >> metis_tac[]
QED
