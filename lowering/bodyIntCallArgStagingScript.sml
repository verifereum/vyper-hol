(* Capacity-sized views of fresh internal-call argument buffers. *)
Theory bodyIntCallArgStaging
Ancestors
  intCallArgs compileEnv valueEncoding venomState arithmetic words exprSim context emitHelper

Theorem stage_mem_arg_capacity_frame:
  type_memory_size tv <= sz /\ sz <= MAX 32 (type_memory_size tv) /\
  initial.vs_alloca_next + MAX 32 (type_memory_size tv) + 64 < dimword (:256) /\
  allocated.vs_alloca_next =
    initial.vs_alloca_next + MAX 32 (type_memory_size tv) /\
  (final with <|vs_vars := allocated.vs_vars;
               vs_memory := allocated.vs_memory;
               vs_inst_idx := allocated.vs_inst_idx|>) = allocated /\
  val_in_memory tv v initial.vs_alloca_next final.vs_memory /\
  (!a len. a + len <= initial.vs_alloca_next \/
           initial.vs_alloca_next + MAX 32 (type_memory_size tv) <= a ==>
     mem_bytes_at a len final.vs_memory = mem_bytes_at a len initial.vs_memory) ==>
  ?w:bytes32.
    w2n w = initial.vs_alloca_next /\
    val_in_memory tv v (w2n w) final.vs_memory /\
    w2n w + sz <= final.vs_alloca_next /\
    (!a len. a + len <= initial.vs_alloca_next ==>
       mem_bytes_at a len final.vs_memory = mem_bytes_at a len initial.vs_memory /\
       regions_disjoint a len (w2n w) sz)
Proof
  strip_tac >>
  `final.vs_alloca_next = allocated.vs_alloca_next` by
    (qpat_x_assum `_ = allocated`
       (mp_tac o Q.AP_TERM `\s. s.vs_alloca_next`) >> simp[]) >>
  qexists_tac `n2w initial.vs_alloca_next` >>
  `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
  simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem stage_mem_arg_capacity_frag:
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa = (buf,sm) /\
  (if is_word_type ty then emit_void MSTORE [buf.buf_operand; val_op]
   else if is_bytestring_type ty then
     do compile_store_bytestring val_op buf.buf_operand; return () od
   else emit_void MCOPY [buf.buf_operand; val_op;
                         Lit (n2w (type_memory_bytes cenv ty))]) sm = ((),sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv <= sz /\ sz <= MAX 32 (type_memory_size tv) /\
  (!s. P s ==>
     FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
     s.vs_alloca_next + MAX 32 (type_memory_size tv) + 64 < dimword (:256) /\
     ?sw. eval_operand val_op s = SOME sw /\
          if is_word_type ty then sw = typed_val_to_w256 tv v
          else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!s s1 t.
     P s /\
     s1 = update_var (STRING #"%" (toString sa.cs_next_var))
            (n2w s.vs_alloca_next)
            (s with <|vs_allocas := s.vs_allocas |+
                         (sa.cs_next_id,
                          (s.vs_alloca_next, MAX 32 (type_memory_size tv)));
                      vs_alloca_next :=
                         s.vs_alloca_next + MAX 32 (type_memory_size tv)|>) /\
     (t with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory;
               vs_inst_idx := s1.vs_inst_idx|>) = s1 /\
     (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s1) /\
     val_in_memory tv v s.vs_alloca_next t.vs_memory /\
     (!a len. a + len <= s.vs_alloca_next \/
              s.vs_alloca_next + MAX 32 (type_memory_size tv) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
     (?w:bytes32.
        w2n w = s.vs_alloca_next /\
        val_in_memory tv v (w2n w) t.vs_memory /\
        w2n w + sz <= t.vs_alloca_next /\
        (!a len. a + len <= s.vs_alloca_next ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory /\
           regions_disjoint a len (w2n w) sz)) ==> Q t) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> drule stage_mem_arg_frag >> disch_then irule >>
  qexistsl_tac [`tenv`, `tv`, `v`, `val_op`] >>
  pure_asm_rewrite_tac[REFL_CLAUSE, FORALL_SIMP, AND_CLAUSES, IMP_CLAUSES] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  qexists_tac `s1` >>
  pure_asm_rewrite_tac[REFL_CLAUSE, FORALL_SIMP, AND_CLAUSES] >>
  `s1.vs_alloca_next = s.vs_alloca_next + MAX 32 (type_memory_size tv)` by
    gvs[update_var_def] >>
  irule stage_mem_arg_capacity_frame >> metis_tac[]
QED

(* A staged prefix survives any later allocation above its frontier. *)
Theorem staged_prefix_memory_frame:
  (!a len. a + len <= frontier ==>
     mem_bytes_at a len final = mem_bytes_at a len initial) /\
  (!i. i < n ==>
     val_in_memory (tvs i) (vs i) (ptrs i) initial /\
     val_wf (tvs i) (vs i) /\
     val_footprint (tvs i) (vs i) <= sizes i /\
     ptrs i + sizes i <= frontier) ==>
  !i. i < n ==>
    val_in_memory (tvs i) (vs i) (ptrs i) final /\
    regions_disjoint (ptrs i) (sizes i) frontier sz
Proof
  strip_tac >> gen_tac >> disch_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (irule val_in_memory_footprint_agree >>
      goal_assum (drule_at Any) >> simp[] >>
      `ptrs i + val_footprint (tvs i) (vs i) <= frontier` by decide_tac >>
      metis_tac[]) >>
  simp[regions_disjoint_def]
QED

Theorem stage_mem_arg_buffer_operand:
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa = (buf,sm) /\
  allocated = update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w initial.vs_alloca_next)
    (initial with <|vs_allocas := initial.vs_allocas |+
       (sa.cs_next_id, (initial.vs_alloca_next, MAX 32 (type_memory_bytes cenv ty)));
       vs_alloca_next := initial.vs_alloca_next + MAX 32 (type_memory_bytes cenv ty)|>) /\
  initial.vs_alloca_next < dimword (:256) /\
  (!x. not_fresh_at sm x ==> lookup_var x final = lookup_var x allocated) ==>
  eval_operand buf.buf_operand final = SOME (n2w initial.vs_alloca_next : bytes32)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[eval_operand_def] >>
  first_x_assum (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
  simp[not_fresh_at_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem stage_mem_arg_operand_capacity_frag:
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa = (buf,sm) /\
  (if is_word_type ty then emit_void MSTORE [buf.buf_operand; val_op]
   else if is_bytestring_type ty then
     do compile_store_bytestring val_op buf.buf_operand; return () od
   else emit_void MCOPY [buf.buf_operand; val_op;
                         Lit (n2w (type_memory_bytes cenv ty))]) sm = ((),sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv <= sz /\ sz <= MAX 32 (type_memory_size tv) /\
  (!s. P s ==>
     FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
     s.vs_alloca_next + MAX 32 (type_memory_size tv) + 64 < dimword (:256) /\
     ?sw. eval_operand val_op s = SOME sw /\
          if is_word_type ty then sw = typed_val_to_w256 tv v
          else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!s s1 t.
     P s /\
     s1 = update_var (STRING #"%" (toString sa.cs_next_var))
            (n2w s.vs_alloca_next)
            (s with <|vs_allocas := s.vs_allocas |+
                         (sa.cs_next_id,
                          (s.vs_alloca_next, MAX 32 (type_memory_size tv)));
                      vs_alloca_next :=
                         s.vs_alloca_next + MAX 32 (type_memory_size tv)|>) /\
     (t with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory;
               vs_inst_idx := s1.vs_inst_idx|>) = s1 /\
     (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s1) /\
     val_in_memory tv v s.vs_alloca_next t.vs_memory /\
     (!a len. a + len <= s.vs_alloca_next \/
              s.vs_alloca_next + MAX 32 (type_memory_size tv) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
     (?w:bytes32.
        eval_operand buf.buf_operand t = SOME w /\
        w2n w = s.vs_alloca_next /\
        val_in_memory tv v (w2n w) t.vs_memory /\
        w2n w + sz <= t.vs_alloca_next /\
        (!a len. a + len <= s.vs_alloca_next ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory /\
           regions_disjoint a len (w2n w) sz)) ==> Q t) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> drule stage_mem_arg_capacity_frag >> disch_then irule >>
  qexistsl_tac [`sz`, `tenv`, `tv`, `v`, `val_op`] >>
  pure_asm_rewrite_tac[REFL_CLAUSE, FORALL_SIMP, AND_CLAUSES, IMP_CLAUSES] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_x_assum `!s. P s ==> _` drule >> strip_tac >> decide_tac) >>
  `eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next : bytes32)` by
    (irule stage_mem_arg_buffer_operand >> goal_assum (drule_at Any) >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> qexists_tac `s1` >>
  pure_asm_rewrite_tac[REFL_CLAUSE, FORALL_SIMP, AND_CLAUSES] >>
  goal_assum (drule_at Any) >>
  `n2w s.vs_alloca_next = w` by metis_tac[n2w_w2n] >>
  metis_tac[]
QED
