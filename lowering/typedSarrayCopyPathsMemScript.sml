(* Counted paths for complete fixed-array normalization. *)
Theory typedSarrayCopyPathsMem
Ancestors
  typedArrayCopyPathsMem typedNormalizeLoop typedNormalizeContinuation
  typedArrayLoopLayoutMem typedArrayBoundControlMem typedArrayLoopControlMem
  fragGasPathMem venomExecSemantics venomState venomInst
  emitHelperProps exprLoweringProps compileEnv words arithmetic list

Theorem typed_sarray_compiler_iteration_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  i <= n /\ n < dimword(:256) /\
  a+type_memory_bytes ce st*n <= s.vs_alloca_next /\
  b+type_memory_bytes ce dt*n <= s.vs_alloca_next /\
  (a+type_memory_bytes ce st*n <= b \/ b+type_memory_bytes ce dt*n <= a) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce st) m =
    mem_bytes_at addr (type_memory_bytes ce st) m' ==> (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce dt) m =
    mem_bytes_at addr (type_memory_bytes ce dt) m' ==> (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) s.vs_memory) /\
  (!j. j < i ==> D j (b+type_memory_bytes ce dt*j) s.vs_memory) /\
  (!sc ec. compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+6))) dt
      (Var ("%" ++ toString (sa.cs_next_var+5))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) u =
        SOME (n2w (a+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+6))) u =
        SOME (n2w (b+type_memory_bytes ce dt*j)) /\
      a+type_memory_bytes ce st*n <= u.vs_alloca_next /\
      b+type_memory_bytes ce dt*n <= u.vs_alloca_next /\
      Src j (a+type_memory_bytes ce st*j) u.vs_memory ==>
      ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
        v.vs_current_bb = ec.cs_current_bb /\
        v.vs_inst_idx = LENGTH ec.cs_current_insts /\
        D j (b+type_memory_bytes ce dt*j) v.vs_memory /\
        (!p k. p+k <= b+type_memory_bytes ce dt*j \/
          b+type_memory_bytes ce dt*j+type_memory_bytes ce dt <= p ==>
          mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
        (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
          vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
          vs_prev_bb := u.vs_prev_bb|>) = u /\
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w n) /\
    (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+type_memory_bytes ce dt*j) t.vs_memory) /\
    mem_bytes_at a (type_memory_bytes ce st*n) t.vs_memory =
      mem_bytes_at a (type_memory_bytes ce st*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_bytes ce dt*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_sarray_child_decompose >> strip_tac >>
  `phi_prefix_length sc.cs_current_insts = 0` by
    simp[phi_prefix_length_def, mk_inst_def] >>
  `not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
   not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6))` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0` by
    (drule_all normalize_typed_prefix_zero >> strip_tac >>
     goal_assum (drule_at Any) >>
     Cases_on `ec.cs_current_insts` >>
     fs[phi_prefix_length_def, typed_sa_backedge_insts_def, mk_inst_def] >>
     Cases_on `h.inst_opcode = PHI` >> fs[phi_prefix_length_def]) >>
  qpat_x_assum `!sc ec. _` (qspecl_then [`sc`, `ec`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[])) >>
  disch_then assume_tac >>
  ASM_SIMP_TAC (srw_ss()) [] >>
  irule (GEN_ALL (SIMP_RULE (srw_ss()) [CONJUNCT1 eval_operand_def]
    (Q.INST [`sm` |-> `sa`, `bound` |-> `Lit (n2w n)`,
       `ss` |-> `type_memory_bytes ce st`, `ds` |-> `type_memory_bytes ce dt`]
      (SPEC_ALL typed_dynarray_header_iteration_path_mem)))) >>
  asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `i` >> gvs[]) >>
  qexistsl_tac [`body_bb`, `dst`, `ec`,
    `fresh_label_output "typed_sa_exit" (sa.cs_next_label+2)`,
    `sa.cs_next_id+2`, `sa.cs_next_id+5`, `sc`, `src`] >>
  ASM_SIMP_TAC (srw_ss()) [typed_sa_header_insts_def] >>
  gvs[] >> metis_tac[]
QED
