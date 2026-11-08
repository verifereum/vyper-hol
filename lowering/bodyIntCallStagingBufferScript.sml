(* Ownership at the actual endpoint of one fresh staging buffer.
   This is an uncounted boundary; its resource premise is explicit. *)
Theory bodyIntCallStagingBuffer
Ancestors
  intCallArgs loweringHalt actualAllocExec context freshWrites
  compileEnv venomState venomInst finite_map words arithmetic
Libs
  monadsyntax

Theorem staging_buffer_endpoint:
  compile_alloc_buffer n sa = (buf,sm) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
  allocated = update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
       (sa.cs_next_id,(s.vs_alloca_next,n));
       vs_alloca_next := s.vs_alloca_next + n|>) /\
  (t with <|vs_memory := allocated.vs_memory; vs_vars := allocated.vs_vars;
            vs_inst_idx := allocated.vs_inst_idx|>) = allocated /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x allocated) ==>
  eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (s.vs_alloca_next,n) /\
  t.vs_alloca_next = s.vs_alloca_next + n /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!psz b sz. psz <= n /\ b + sz <= s.vs_alloca_next ==>
     regions_disjoint b sz s.vs_alloca_next psz /\
     s.vs_alloca_next + psz <= t.vs_alloca_next)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `t.vs_allocas = allocated.vs_allocas` by
    (qpat_x_assum `_ = allocated`
       (mp_tac o Q.AP_TERM `\u. u.vs_allocas`) >> simp[]) >>
  `t.vs_alloca_next = allocated.vs_alloca_next` by
    (qpat_x_assum `_ = allocated`
       (mp_tac o Q.AP_TERM `\u. u.vs_alloca_next`) >> simp[]) >>
  gvs[update_var_def] >>
  simp[eval_operand_def] >>
  first_x_assum (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
  simp[lookup_var_def, FLOOKUP_UPDATE, regions_disjoint_def] >>
  rpt strip_tac >> simp[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* A callback at the very endpoint chosen by stage_mem_arg_frag, with
   no allocation-state implementation exposed to the consumer. *)
Theorem stage_mem_arg_owned_frag:
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa = (buf,sm) /\
  (if is_word_type ty then emit_void MSTORE [buf.buf_operand; val_op]
   else if is_bytestring_type ty then
     do compile_store_bytestring val_op buf.buf_operand; return () od
   else emit_void MCOPY [buf.buf_operand; val_op;
                         Lit (n2w (type_memory_bytes cenv ty))]) sm = ((),sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (!s. P s ==>
     FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
     s.vs_alloca_next + MAX 32 (type_memory_size tv) + 64 < dimword (:256) /\
     ?sw. eval_operand val_op s = SOME sw /\
          if is_word_type ty then sw = typed_val_to_w256 tv v
          else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!s t. P s /\
     eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
     FLOOKUP t.vs_allocas sa.cs_next_id =
       SOME (s.vs_alloca_next,MAX 32 (type_memory_size tv)) /\
     t.vs_alloca_next = s.vs_alloca_next + MAX 32 (type_memory_size tv) /\
     (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
     val_in_memory tv v s.vs_alloca_next t.vs_memory /\
     (!a len. a + len <= s.vs_alloca_next \/
              s.vs_alloca_next + MAX 32 (type_memory_size tv) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
     (!psz b sz. psz <= MAX 32 (type_memory_size tv) /\
                 b + sz <= s.vs_alloca_next ==>
        regions_disjoint b sz s.vs_alloca_next psz /\
        s.vs_alloca_next + psz <= t.vs_alloca_next) ==>
     Q t) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> irule stage_mem_arg_frag >>
  qexistsl_tac [`buf`, `cenv`, `sm`, `tenv`, `tv`, `ty`, `v`, `val_op`] >>
  simp[] >> rpt strip_tac >>
  `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` by metis_tac[] >>
  `compile_alloc_buffer (MAX 32 (type_memory_size tv)) sa = (buf,sm)` by
    metis_tac[] >>
  qmatch_asmsub_abbrev_tac
    `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x allocated` >>
  `allocated = update_var (STRING #"%" (toString sa.cs_next_var))
     (n2w s.vs_alloca_next)
     (s with <|vs_allocas := s.vs_allocas |+
       (sa.cs_next_id,(s.vs_alloca_next,MAX 32 (type_memory_size tv)));
       vs_alloca_next := s.vs_alloca_next + MAX 32 (type_memory_size tv)|>)`
    by simp[Abbr `allocated`] >>
  drule_all staging_buffer_endpoint >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (drule compile_alloc_buffer_parts >> strip_tac >> rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[] >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
     simp[Abbr `allocated`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  first_x_assum irule >> qexists_tac `s` >> simp[] >>
  conj_tac >- (rpt strip_tac >> simp[MAX_DEF] >> decide_tac) >> metis_tac[]
QED
