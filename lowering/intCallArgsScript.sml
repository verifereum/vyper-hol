(*
 * Internal calls: staging a memory-passed argument (#638)
 *
 * compile_stage_intcall_args gives each memory-passed argument a buffer
 * of its own, MAX 32 (type_memory_bytes cenv ty) bytes from a fresh
 * ALLOCA, and stores the unwrapped value there; the callee gets the
 * buffer's address.
 *
 * TOP-LEVEL:
 *   stage_mem_arg_frag — the ALLOCA and the store: the buffer, at the old
 *                        allocation frontier, holds the value, and memory
 *                        changes only there
 *)

Theory intCallArgs
Ancestors
  list rich_list arithmetic finite_map
  fragExec loweringHalt valueCopy freshWrites context
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperTyping vyperValue venomExecSemantics venomState

(* One memory-passed argument of compile_stage_intcall_args, after its
   value is unwrapped into val_op (a word type's typed word, any other
   type's value in memory at val_op): the ALLOCA of its buffer, then the
   store.  From a state s in P, the ALLOCA leaves s1, which binds the
   buffer operand to s.vs_alloca_next, and the store leaves t, which
   differs from s1 only in variables fresh at sm and in memory, where it
   holds the value at the buffer and keeps the bytes outside the buffer. *)
Theorem stage_mem_arg_frag:
  !ctx cenv ty tenv tv v val_op sa sm sb buf P Q R.
    compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa =
      (buf, sm) /\
    (if is_word_type ty then emit_void MSTORE [buf.buf_operand; val_op]
     else if is_bytestring_type ty then
       do compile_store_bytestring val_op buf.buf_operand; return () od
     else emit_void MCOPY [buf.buf_operand; val_op;
                           Lit (n2w (type_memory_bytes cenv ty))]) sm =
      ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
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
              (s with <| vs_allocas := s.vs_allocas |+
                           (sa.cs_next_id,
                            (s.vs_alloca_next, MAX 32 (type_memory_size tv)));
                         vs_alloca_next :=
                           s.vs_alloca_next + MAX 32 (type_memory_size tv) |>) /\
       (t with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory;
                 vs_inst_idx := s1.vs_inst_idx|>) = s1 /\
       (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s1) /\
       val_in_memory tv v s.vs_alloca_next t.vs_memory /\
       (!a len. a + len <= s.vs_alloca_next \/
                s.vs_alloca_next + MAX 32 (type_memory_size tv) <= a ==>
          mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
       Q t) ==>
    frag_exec ctx sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `type_memory_size tv <= MAX 32 (type_memory_size tv)` by simp[] >>
  qabbrev_tac `alloc = \s:venom_state.
    update_var (STRING #"%" (toString sa.cs_next_var)) (n2w s.vs_alloca_next)
      (s with <| vs_allocas := s.vs_allocas |+
                   (sa.cs_next_id,
                    (s.vs_alloca_next, MAX 32 (type_memory_size tv)));
                 vs_alloca_next :=
                   s.vs_alloca_next + MAX 32 (type_memory_size tv) |>)` >>
  qabbrev_tac `L = LENGTH sm.cs_current_insts` >>
  `sa.cs_next_var < sm.cs_next_var` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
        emit_def] >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `!s. P s ==>
     (!x. val_op = Var x ==> not_fresh_at sm x) /\
     (!x. buf.buf_operand = Var x ==> not_fresh_at sm x) /\
     eval_operand buf.buf_operand (alloc s with vs_inst_idx := L) =
       SOME (n2w s.vs_alloca_next) /\
     w2n (n2w s.vs_alloca_next : bytes32) = s.vs_alloca_next /\
     ?sw. eval_operand val_op (alloc s with vs_inst_idx := L) = SOME sw /\
          if is_word_type ty then sw = typed_val_to_w256 tv v
          else val_in_memory tv v (w2n sw)
                 (alloc s with vs_inst_idx := L).vs_memory` by
    suspend "store_pre" >>
  (* the shape of the store needs one state to run it from *)
  reverse (Cases_on `?s. P s`)
  >- (simp[frag_exec_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `!s. P s ==> FLOOKUP _ _ = NONE /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!s. P s ==> (!x. val_op = Var x ==> _) /\ _`
    (drule_then strip_assume_tac) >>
  `s.vs_alloca_next + (type_memory_size tv + 64) < dimword (:256)` by
    decide_tac >>
  qspecl_then [`cenv`, `val_op`, `buf.buf_operand`, `ty`, `sm`, `sb`,
               `alloc s with vs_inst_idx := L`, `tenv`, `tv`, `v`,
               `THE (eval_operand val_op (alloc s with vs_inst_idx := L))`,
               `n2w s.vs_alloca_next`] mp_tac stage_store_run >>
  impl_tac >- fs[] >>
  (* the shape only: the run from s is the store resume's business *)
  disch_then (fn th => let val cs = CONJUNCTS th
                       in MAP_EVERY assume_tac (List.take (cs, length cs - 1))
                       end) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s1. ?s. P s /\ s1 = alloc s with vs_inst_idx := L`, `sm`] >>
  simp[] >> conj_tac
  >- (irule compile_alloc_buffer_fresh_frag >>
      qexistsl_tac [`buf`, `MAX 32 (type_memory_bytes cenv ty)`] >>
      `MAX 32 (type_memory_bytes cenv ty) < dimword (:256)` by
        (asm_rewrite_tac[] >> decide_tac) >>
      fs[] >> rpt strip_tac >> metis_tac[]) >>
  suspend "store"
QED

Resume stage_mem_arg_frag[store_pre]:
  gen_tac >> strip_tac >>
  qpat_assum `!s. P s ==> FLOOKUP _ _ = NONE /\ _`
    (drule_then strip_assume_tac) >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[])
  >- (rw[not_fresh_at_def, ASCIInumbersTheory.toString_11] >> decide_tac)
  >- simp[Abbr `alloc`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE]
  >- fs[wordsTheory.w2n_n2w, LESS_MOD] >>
  qexists_tac `sw` >>
  `eval_operand val_op (alloc s with vs_inst_idx := L) = SOME sw` by
    (Cases_on `val_op` >>
     gvs[Abbr `alloc`, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE] >>
     rw[] >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `alloc`, update_var_def]
QED

Resume stage_mem_arg_frag[store]:
  irule frag_exec_run_inst_seq >>
  `sb.cs_blocks = sm.cs_blocks /\ sb.cs_current_bb = sm.cs_current_bb` by
    fs[same_blocks_def] >>
  asm_simp_tac (srw_ss()) [IS_PREFIX_APPEND] >>
  rpt strip_tac >> disj1_tac >> rename1 `P s2` >>
  qpat_assum `!s. P s ==> FLOOKUP _ _ = NONE /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!s. P s ==> (!x. val_op = Var x ==> _) /\ _`
    (drule_then strip_assume_tac) >>
  qspecl_then [`cenv`, `val_op`, `buf.buf_operand`, `ty`, `sm`, `sb`,
               `alloc s2 with vs_inst_idx := L`, `tenv`, `tv`, `v`,
               `THE (eval_operand val_op (alloc s2 with vs_inst_idx := L))`,
               `n2w s2.vs_alloca_next`] mp_tac stage_store_run >>
  `s2.vs_alloca_next + (type_memory_size tv + 64) < dimword (:256)` by
    decide_tac >>
  impl_tac >- fs[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `!s s1 t. P s /\ _ ==> Q t`
    (qspecl_then [`s2`, `alloc s2`,
                  `t with vs_inst_idx := LENGTH sb.cs_current_insts`]
       mp_tac) >>
  `(alloc s2 with vs_inst_idx := L).vs_memory = s2.vs_memory` by
    simp[Abbr `alloc`, update_var_def] >>
  impl_tac >> simp[] >>
  simp[Abbr `alloc`] >> rpt conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
      simp[venom_state_component_equality, update_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x t = _` drule >>
      simp[lookup_var_def, update_var_def])
  >- gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
    (qspecl_then [`a`, `len`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

Finalise stage_mem_arg_frag
