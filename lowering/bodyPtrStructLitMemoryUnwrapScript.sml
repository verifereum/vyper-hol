(* Counted memory-load boundary, separate from source read correspondence. *)
Theory bodyPtrStructLitMemoryUnwrap
Ancestors
  bodyPtrStructLitUnwrap bodyPtrStructLitPostAdd bodyPtrStructLitFieldStore
  fragGasSeqPtr fragGasPathPtr typedCopyPtr ptrSafeRun ptrDiscipline
  bodyPtrDefs venomExecSemantics venomInstProofs venomInst venomState
  contextCodegenRel finite_map representationCleanPtr exprSimProps
  context exprLowering compileEnv emitHelper fragExec exprLoweringProps
  gasSummaryComposePtr exprSimMemorySource decoderGhostFramePtr

Theorem covered_word_load_counted:
  !D ctx fn PG G tn s bb id src out a.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [out]) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MLOAD [Var src] [out])
        (update_var out (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [out]) s
        (update_var out (mload (w2n a) s) s) tn)
      (OK (update_var out (mload (w2n a) s) s with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst id MLOAD [Var src] [out])
       (update_var out (mload (w2n a) s) s))
     (step_taint (mk_inst id MLOAD [Var src] [out]) s
       (update_var out (mload (w2n a) s) s) tn)
     (OK (update_var out (mload (w2n a) s) s with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `~(update_var out (mload (w2n a) s) s with
       vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  drule (cj 1 gas_path_ptr_rules) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_0]
QED

Theorem robust_typed_word_load_clean:
  is_word_type t /\ evaluate_type env t = SOME tv /\
  value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n a) mem) ==>
  !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n a) mem = typed_val_to_w256 tv v` by
    metis_tac[val_in_memory_word_type] >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem memory_word_unwrap_code:
  is_word_type ty /\ p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id MLOAD [p.ptr_operand] [out]] /\
  ~not_fresh_at sa out
Proof
  simp[unwrap_value_def, compile_ptr_load_def] >> strip_tac >>
  gvs[compile_ptr_load_def, emit_op_def, comp_bind_def, comp_return_def, fresh_id_def,
      comp_ignore_bind_def, fresh_var_def, emit_def, not_fresh_at_def]
QED

Theorem memory_word_unwrap_instruction:
  is_word_type ty /\ p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) /\
  fn_has_code sa sb fn ==>
  ~not_fresh_at sa out /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id MLOAD [p.ptr_operand] [out])
Proof
  strip_tac >> drule_all memory_word_unwrap_code >> strip_tac >> simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem memory_word_unwrap_counted:
  is_word_type ty /\ p.ptr_location = LocMemory /\ p.ptr_operand = Var src /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
    (OK (update_var out (mload (w2n a) s) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all memory_word_unwrap_instruction >> strip_tac >>
  irule covered_word_load_counted >> gvs[] >> metis_tac[]
QED

(* The source read is explicit: this wrapper does not infer its value
   correspondence merely from pointer coverage. *)
Theorem mload_output_provenance:
  op_prov (step_prov PG G (mk_inst id MLOAD [src] [out]) s) (Var out) = NONE
Proof
  irule step_prov_out_none >> simp[mk_inst_def] >>
  irule out_prov_other_none >> simp[mk_inst_def]
QED

Theorem word_load_marked_read:
  read_result cx tv ee = (INL v,ee) /\ is_word_type t /\
  eval_operand src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
  G1 = step_prov PG G (mk_inst id MLOAD [src] [out])
          (update_var out (mload (w2n a) s) s) /\
  tn1 = step_taint (mk_inst id MLOAD [src] [out]) s
          (update_var out (mload (w2n a) s) s) tn ==>
  gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
  ptr_val_ok cx t v (Var out) G1 tn1 s1
Proof
  strip_tac >> conj_tac
  >- (simp[gas_marked_exec_ptr_def] >> metis_tac[read_result_gas_obs]) >>
  simp[ptr_val_ok_def, mload_output_provenance] >>
  irule (cj 1 mload_ghost_clean) >> simp[] >> metis_tac[]
QED

Theorem word_load_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ~not_fresh_at sa out /\
  eval_operand src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id MLOAD [src] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [src] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
Proof
  strip_tac >> drule_all mload_ghost_clean >> strip_tac >>
  gvs[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem memory_word_unwrap_endpoint:
  is_word_type ty /\ p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb =
    sb.cs_current_bb /\
  (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx =
    LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all memory_word_unwrap_code >>
  simp[update_var_def]
QED

(* The actual counted endpoint increments PC; old-register coverage does not
   depend on PC, and is kept separately from ghost_kept. *)
Theorem word_load_endpoint_registers:
  x <> out ==>
  lookup_var x (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) =
    lookup_var x s /\
  FLOOKUP (step_prov PG G (mk_inst id MLOAD [src] [out])
    (update_var out w s)) x = FLOOKUP G x /\
  op_taint (step_taint (mk_inst id MLOAD [src] [out]) s
    (update_var out w s) tn) (Var x) = op_taint tn (Var x)
Proof
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
