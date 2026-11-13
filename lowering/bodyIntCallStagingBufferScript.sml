(* Ownership at the actual endpoint of one fresh staging buffer.
   This is an uncounted boundary; its resource premise is explicit. *)
Theory bodyIntCallStagingBuffer
Ancestors
  intCallArgs loweringHalt actualAllocExec context freshWrites
  memoryReadProps fragExec valueCopy exprLoweringProps emitHelper
  venomExecSemantics
  compileEnv loweringStateRelDefs venomState venomInst finite_map words arithmetic
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

Theorem zero_size_memory_relocate[local]:
  val_wf tv v /\ type_memory_size tv = 0 /\
  val_in_memory tv v src mem ==> val_in_memory tv v dst mem'
Proof
  strip_tac >> irule valueEncodingPropsTheory.val_in_memory_relocate >>
  simp[] >> qexistsl_tac [`mem`, `0`, `src`] >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem zero_mcopy_callback[local]:
  emit_void MCOPY [dst;src;Lit 0w] sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  Q ((mcopy (w2n d) (w2n a) 0 s0) with
       vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  frag_exec ctx sa sb (\s. s = s0) Q R
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0`,
    `\t. t = ((mcopy (w2n d) (w2n a) 0 s0) with
       vs_inst_idx := LENGTH sb.cs_current_insts)`, `\r. F`] >>
  simp[] >>
  `0 < dimword (:256)` by simp[] >>
  drule_all emit_mcopy_run >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
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
  strip_tac >>
  Cases_on `~is_word_type ty /\ ~is_bytestring_type ty /\
            type_memory_bytes cenv ty = 0`
  >- suspend "zero_copy" >>
  `(if is_word_type ty then emit_void MSTORE [buf.buf_operand; val_op]
    else if is_bytestring_type ty then
      do compile_store_bytestring val_op buf.buf_operand; return () od
    else compile_store_memory cenv val_op buf.buf_operand ty ty) sm = ((),sb)` by
    (Cases_on `is_word_type ty` >>
     Cases_on `is_bytestring_type ty` >>
     gvs[compile_store_memory_def] >>
     Cases_on `type_memory_size tv` >>
     gvs[compile_copy_memory_def]) >>
  irule stage_mem_arg_frag >>
  qexistsl_tac [`buf`, `cenv`, `sm`, `ty`, `tenv`, `tv`, `ty`, `v`, `val_op`] >>
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

Resume stage_mem_arg_owned_frag[zero_copy]:
  gvs[] >>
  qabbrev_tac `alloc = \s:venom_state.
    update_var (STRING #"%" (toString sa.cs_next_var)) (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                  (sa.cs_next_id,(s.vs_alloca_next,32));
                vs_alloca_next := s.vs_alloca_next + 32|>)` >>
  `cs_extends sa sm` by suspend "alloc_extends" >>
  `cs_extends sm sb` by suspend "copy_extends" >>
  irule frag_exec_seq_pointwise >>
  qexistsl_tac [`\u. ?s. P s /\
    u = alloc s with vs_inst_idx := LENGTH sm.cs_current_insts`, `sm`] >>
  simp[] >> reverse conj_tac
  >- (irule compile_alloc_buffer_fresh_frag >>
      qexistsl_tac [`buf`, `32`] >> simp[] >>
      reverse conj_tac >- simp[wordsTheory.dimword_def] >>
      gen_tac >> strip_tac >> qexists_tac `s` >> simp[]) >>
  gen_tac >> strip_tac >> gvs[] >>
  `?sw. eval_operand val_op s = SOME sw` by metis_tac[] >>
  `eval_operand buf.buf_operand
     (alloc s with vs_inst_idx := LENGTH sm.cs_current_insts) =
     SOME (n2w s.vs_alloca_next) /\
   eval_operand val_op
     (alloc s with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME sw`
    by suspend "alloc_operands" >>
  irule zero_mcopy_callback >>
  qexistsl_tac [`sw`, `n2w s.vs_alloca_next`, `buf.buf_operand`, `val_op`] >>
  simp[] >> suspend "zero_endpoint"
QED

Resume stage_mem_arg_owned_frag[alloc_extends]:
  drule compile_alloc_buffer_insts >> strip_tac >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Resume stage_mem_arg_owned_frag[copy_extends]:
  gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, emit_def] >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Resume stage_mem_arg_owned_frag[alloc_operands]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  conj_tac
  >- simp[Abbr `alloc`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE] >>
  Cases_on `val_op` >>
  gvs[Abbr `alloc`, eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

Resume stage_mem_arg_owned_frag[zero_endpoint]:
  qmatch_goalsub_abbrev_tac `Q final` >>
  `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` by metis_tac[] >>
  qpat_assum `!s. P s ==> FLOOKUP _ _ = NONE /\ _`
    (drule_then strip_assume_tac) >>
  `val_in_memory tv v s.vs_alloca_next final.vs_memory` by
    (irule zero_size_memory_relocate >> simp[] >> metis_tac[]) >>
  `(final with <|vs_memory := (alloc s).vs_memory;
                vs_vars := (alloc s).vs_vars;
                vs_inst_idx := (alloc s).vs_inst_idx|>) = alloc s /\
   (!x. lookup_var x final = lookup_var x (alloc s))`
    by (simp[Abbr `final`, mcopy_def, write_memory_with_expansion_def,
             lookup_var_def]) >>
  `eval_operand buf.buf_operand final = SOME (n2w s.vs_alloca_next) /\
   FLOOKUP final.vs_allocas sa.cs_next_id = SOME (s.vs_alloca_next,32) /\
   final.vs_alloca_next = s.vs_alloca_next + 32 /\
   (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP final.vs_allocas aid = SOME b) /\
   (!psz b sz. psz <= 32 /\ b + sz <= s.vs_alloca_next ==>
     regions_disjoint b sz s.vs_alloca_next psz /\
     s.vs_alloca_next + psz <= final.vs_alloca_next)` by
    (irule staging_buffer_endpoint >>
     simp[] >> qexistsl_tac [`alloc s`, `sm`] >> simp[Abbr `alloc`]) >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s` by
    (drule compile_alloc_buffer_parts >> strip_tac >> rpt strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
     simp[Abbr `alloc`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!a len. mem_bytes_at a len final.vs_memory = mem_bytes_at a len s.vs_memory`
    by suspend "zero_reads" >>
  first_x_assum irule >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume stage_mem_arg_owned_frag[zero_reads]:
  rpt gen_tac >>
  qspecl_then [`a`, `len`, `s.vs_alloca_next MOD dimword (:256)`, `w2n sw`,
               `alloc s with vs_inst_idx := LENGTH sm.cs_current_insts`]
    mp_tac read_memory_mcopy_zero >>
  simp[read_memory_eq_mem_bytes_at, Abbr `final`, Abbr `alloc`, update_var_def]
QED

Finalise stage_mem_arg_owned_frag
