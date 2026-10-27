(*
 * Internal calls: the caller's side of the result (#638)
 *
 * After INVOKE, compile_call's IntCall case stores the callee's stack
 * results into the return buffer (store_multi_results) and hands out the
 * buffer as a LocatedValue.  This theory proves that the stored words hold
 * the source's return value in memory, for every value intret_vals_match
 * relates to the words the callee returned.
 *
 * TOP-LEVEL:
 *   store_multi_results_shape — straight-line code, no INVOKE or terminator
 *   store_multi_results_run — the stores write each result word at its
 *     slot of the buffer and leave everything else alone
 *   stack_results_val_in_memory — the words of a stack-returned value,
 *     laid out 32 bytes apart, hold the value in memory (val_in_memory)
 *)

Theory intCallResult
Ancestors
  list rich_list arithmetic
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  freshWrites valueEncoding valueEncodingProps entryDecodeProps
  exprSim fragExec localPtrsProps context
  vyperTyping vyperValue vyperState venomExecSemantics venomState

(* ===== Storing the results ===== *)

Theorem store_result_head_run[local]:
  !buf_op off op sa dst sm sb s w x.
    emit_op ADD [buf_op; Lit off] sa = (dst,sm) /\
    emit_void MSTORE [dst; op] sm = ((),sb) /\
    (!y. op = Var y ==> not_fresh_at sa y) /\
    eval_operand buf_op s = SOME w /\ eval_operand op s = SOME x ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory = (mstore (w2n (w + off)) x s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op (update_var (STRING #"%" (toString sa.cs_next_var))
     (w + off) s) = SOME x` by
    (Cases_on `op` >> gvs[eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def, update_var_def]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1, run_inst_seq_def,
       step_inst_base_def, exec_pure2_def, exec_write2_def, eval_operand_def,
       bind_outputs_def, lookup_var_update_var] >>
  simp[mstore_def, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem store_result_head_shape[local]:
  !buf_op off op sa dst sm sb.
    emit_op ADD [buf_op; Lit off] sa = (dst,sm) /\
    emit_void MSTORE [dst; op] sm = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem store_multi_results_shape:
  !ops buf_op off sa sb.
    store_multi_results buf_op ops off sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  Induct
  >- simp[store_multi_results_def, comp_return_def, emitted_insts_def,
          same_blocks_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (u,post)` >> Cases_on `u` >>
  drule_all store_result_head_shape >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  asm_rewrite_tac[EVERY_APPEND, APPEND_ASSOC] >>
  rpt conj_tac >> TRY decide_tac >> simp[] >>
  metis_tac[same_blocks_trans]
QED

Theorem store_result_operand_frame:
  !op sa s t.
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  Cases_on `op` >> simp[eval_operand_def]
QED

(* store_multi_results buf ops off stores the i-th operand at buf + off +
   32 * i, with an ADD for each address.  The operands are the INVOKE's
   outputs, older than the ADDs' fresh variables, so the ADDs do not
   change them. *)
Theorem store_multi_results_run:
  !ops buf_op off sa sb s b ws.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (!i. i < LENGTH ws ==>
           mem_word_at (b + off + 32 * i) t.vs_memory = EL i ws) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/ b + off + 32 * LENGTH ops <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[store_multi_results_def, comp_return_def, emitted_insts_def,
          same_blocks_def, run_inst_seq_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `store_multi_results _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (u,post)` >> Cases_on `u` >>
  Cases_on `ws` >> gvs[] >>
  rename1 `MAP (\op. eval_operand op s) ops = MAP SOME rest` >>
  rename1 `eval_operand h s = SOME x` >>
  `!y. h = Var y ==> not_fresh_at sa y` by metis_tac[] >>
  drule_all store_result_head_run >> strip_tac >>
  suspend "tail"
QED

Resume store_multi_results_run[tail]:
  `(!x. buf_op = Var x ==> not_fresh_at post x) /\
   (!x. MEM (Var x) ops ==> not_fresh_at post x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand buf_op t = SOME (n2w b)` by
    metis_tac[store_result_operand_frame] >>
  `MAP (\op. eval_operand op t) ops = MAP SOME rest` by
    (qpat_x_assum `MAP _ ops = MAP SOME _` (SUBST1_TAC o SYM) >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule store_result_operand_frame >> simp[] >> qexists_tac `sa` >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  first_x_assum (qspecl_then [`buf_op`, `off + 32`, `post`, `sb`, `t`, `b`, `rest`]
    mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- metis_tac[same_blocks_trans] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  rename1 `run_inst_seq (emitted_insts post sb) t = OK final` >>
  qexists_tac `final` >>
  `w2n ((n2w b:bytes32) + n2w off) = b + off` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >> decide_tac) >>
  `!a len. a + len <= b + off \/ b + off + 32 <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> asm_simp_tac bool_ss [] >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  rpt conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_x_assum `run_inst_seq (emitted_insts sa post) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >> simp[])
  >- (Cases >> simp[]
      >- (`mem_bytes_at (b + off) 32 final.vs_memory =
           mem_bytes_at (b + off) 32 t.vs_memory` by
            (first_assum irule >> simp[]) >>
          `mem_word_at (b + off) final.vs_memory =
           mem_word_at (b + off) t.vs_memory` by
            gvs[mem_word_at_def, mem_bytes_at_def] >>
          simp[mstore_mem_word_at_same]) >>
      strip_tac >>
      qpat_x_assum `!i. i < LENGTH _ ==> _` (qspec_then `n` mp_tac) >>
      simp[MULT_SUC, ADD1])
  >- fs[venom_state_component_equality]
  >- (rpt strip_tac >> rename1 `not_fresh_at sa y` >>
      `not_fresh_at post y` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at a len t.vs_memory` >>
  conj_tac >> first_x_assum irule >> decide_tac
QED

Finalise store_multi_results_run

(* ===== The stored words hold the value ===== *)

Theorem word_tv_memory_size[local]:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    type_memory_size tv = 32
Proof
  Cases_on `t` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_word_type_def]) >>
      simp[evaluate_type_def, type_memory_size_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rw[] >>
  simp[type_memory_size_def]
QED

Theorem word_tuple_in_memory[local]:
  !tvs vs tenv off mem.
    values_have_types tvs vs /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv) tvs /\
    (!i. i < LENGTH tvs ==>
         mem_word_at (off + 32 * i) mem =
         typed_val_to_w256 (EL i tvs) (EL i vs)) ==>
    tuple_in_memory vs tvs off mem
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def, val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  conj_tac
  >- (drule_all val_in_memory_word >> disch_then (fn th => rewrite_tac[th]) >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`t`, `tenv`, `off + 32`, `mem`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      simp[MULT_SUC, ADD1]) >>
  simp[]
QED

Theorem word_fields_in_memory[local]:
  !ftvs fields tenv off mem.
    struct_has_type ftvs fields /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
      (MAP SND ftvs) /\
    (!i. i < LENGTH ftvs ==>
         mem_word_at (off + 32 * i) mem =
         typed_val_to_w256 (SND (EL i ftvs)) (SND (EL i fields))) ==>
    fields_in_memory fields ftvs off mem
Proof
  Induct >> Cases_on `fields` >> simp[value_has_type_def, val_in_memory_def] >>
  TRY (Cases_on `h` >> simp[value_has_type_def]) >>
  Cases_on `h'` >> TRY (Cases_on `h`) >>
  simp[value_has_type_def, val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  conj_tac
  >- (drule_all val_in_memory_word >> disch_then (fn th => rewrite_tac[th]) >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`t`, `tenv`, `off + 32`, `mem`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      simp[MULT_SUC, ADD1]) >>
  simp[]
QED

(* A word type's value returns as one word, its typed encoding. *)
Theorem intret_vals_match_word_eq:
  !tenv t tv v ws.
    is_word_type t /\ evaluate_type tenv t = SOME tv /\
    intret_vals_match tv v ws /\ ws <> [] ==>
    ws = [typed_val_to_w256 tv v]
Proof
  rpt strip_tac >>
  `(!tvs. tv <> TupleTV tvs) /\ (!ftvs. tv <> StructTV ftvs)` by
    (Cases_on `t` >> gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[evaluate_type_def]) >>
  gvs[intret_vals_match_def] >> Cases_on `tv` >> gvs[] >>
  Cases_on `v` >> gvs[] >> rename1 `ArrayV av` >> Cases_on `av` >> gvs[]
QED

(* The words a callee returns on the stack (intret_vals_match: one word
   for a word type, one per member for a tuple or struct of words), each
   at its 32-byte slot from off, hold the return value in memory. *)
Theorem stack_results_val_in_memory:
  !tenv tv v ws off mem.
    value_has_type tv v /\ intret_vals_match tv v ws /\ ws <> [] /\
    ((?t. is_word_type t /\ evaluate_type tenv t = SOME tv) \/
     (?tvs. tv = TupleTV tvs /\
        EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
          tvs) \/
     (?ftvs. tv = StructTV ftvs /\
        EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
          (MAP SND ftvs))) /\
    (!i. i < LENGTH ws ==> mem_word_at (off + 32 * i) mem = EL i ws) ==>
    val_in_memory tv v off mem
Proof
  rpt gen_tac >> strip_tac
  >- (drule_all intret_vals_match_word_eq >> strip_tac >> gvs[] >>
      drule_all val_in_memory_word >> disch_then (fn th => rewrite_tac[th]) >>
      simp[])
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
      simp[val_in_memory_def] >>
      match_mp_tac word_tuple_in_memory >> qexists_tac `tenv` >> simp[] >>
      `LENGTH l = LENGTH tvs` by suspend "tuple_len" >>
      gvs[intret_vals_match_def, EL_MAP, EL_ZIP]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  simp[val_in_memory_def] >>
  match_mp_tac word_fields_in_memory >> qexists_tac `tenv` >> simp[] >>
  `LENGTH l = LENGTH ftvs` by suspend "struct_len" >>
  gvs[intret_vals_match_def, EL_MAP, EL_ZIP]
QED

Resume stack_results_val_in_memory[tuple_len]:
  qpat_x_assum `values_have_types _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> qid_spec_tac `l` >>
  Induct_on `tvs` >> Cases_on `l` >> simp[value_has_type_def]
QED

Resume stack_results_val_in_memory[struct_len]:
  qpat_x_assum `struct_has_type _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> qid_spec_tac `l` >>
  Induct_on `ftvs` >> Cases_on `l` >> simp[value_has_type_def] >>
  Cases_on `h` >> TRY (Cases_on `h'`) >> simp[value_has_type_def]
QED

Finalise stack_results_val_in_memory

(* ===== The result in the return buffer ===== *)

(* stmt_state_rel survives code that changes only variables and memory,
   keeping the live locals' pointer variables and the bytes of their
   regions (as literal_state_memory_frame in exprSimLiteralBuffer). *)
Theorem result_state_memory_frame:
  !func cenv cx es s t.
    stmt_state_rel func cenv cx es s /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p t = lookup_var p s) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
    stmt_state_rel func cenv cx es t
Proof
  rpt strip_tac >>
  `t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars;
                                        vs_memory := t.vs_memory|>``) >>
     simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
       (fn th => once_rewrite_tac[th]) >>
     gvs[stmt_state_rel_def, state_rel_def, lookup_var_def] >>
     rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `alloca_inv t` by
    (irule alloca_inv_fields >> qexists_tac `s` >> gvs[stmt_state_rel_def]) >>
  `alloca_room func t` by
    (irule alloca_room_fields >> qexists_tac `s` >> gvs[stmt_state_rel_def]) >>
  rewrite_tac[stmt_state_rel_def] >>
  conj_tac
  >- (irule state_rel_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >>
      qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
        (fn th => once_rewrite_tac[th]) >>
      gvs[stmt_state_rel_def]) >>
  gvs[stmt_state_rel_def] >> first_assum ACCEPT_TAC
QED

(* A buffer holding v in memory is a pointer to v: the caller's view of a
   return buffer, filled by the stack results (store_multi_results_frag)
   or by the callee's memory return (intCallReturnMem). *)
Theorem buffer_vv_holds:
  !cenv cx t tv v rbuf es s w.
    eval_operand rbuf.buf_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
    val_in_memory tv v (w2n w) s.vs_memory ==>
    vv_holds cenv cx t (Value v) (LocatedValue t (base_ptr rbuf)) es s
Proof
  rw[vv_holds_def, base_ptr_def, materialise_def, return_def] >>
  drule_all val_in_memory_word >> disch_then (fn th => fs[th])
QED

(* After INVOKE, storing the callee's stack results (ws, related to the
   return value v by intret_vals_match) into the return buffer, whose
   result slots miss every live local, leaves the buffer holding v as
   #636's vv_holds says for compile_call's LocatedValue, keeps
   stmt_state_rel, and changes memory only in those slots. *)
Theorem store_multi_results_frag:
  !ctx func cenv cx es t tv v rbuf results sa sb s0 w ws.
    store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
    local_ptrs_reserved cenv sa /\
    (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) results ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
    ((?t'. is_word_type t' /\ evaluate_type (get_tenv cx) t' = SOME tv) \/
     (?tvs. tv = TupleTV tvs /\
        EVERY (\etv. ?t'. is_word_type t' /\
                          evaluate_type (get_tenv cx) t' = SOME etv) tvs) \/
     (?ftvs. tv = StructTV ftvs /\
        EVERY (\etv. ?t'. is_word_type t' /\
                          evaluate_type (get_tenv cx) t' = SOME etv)
          (MAP SND ftvs))) /\
    intret_vals_match tv v ws /\ ws <> [] /\
    stmt_state_rel func cenv cx es s0 /\
    eval_operand rbuf.buf_operand s0 = SOME w /\
    MAP (\op. eval_operand op s0) results = MAP SOME ws /\
    w2n w + 32 * LENGTH results < dimword (:256) /\
    (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) ==>
    frag_exec ctx sa sb (\s. s = s0)
      (\s. stmt_state_rel func cenv cx es s /\
           vv_holds cenv cx t (Value v) (LocatedValue t (base_ptr rbuf)) es s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
           s.vs_allocas = s0.vs_allocas /\
           (!a len. a + len <= w2n w \/ w2n w + 32 * LENGTH results <= a ==>
              mem_bytes_at a len s.vs_memory = mem_bytes_at a len s0.vs_memory))
      (\r. F)
Proof
  rpt gen_tac >> DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule store_multi_results_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    fs[same_blocks_def] >>
  asm_simp_tac (srw_ss()) [IS_PREFIX_APPEND] >>
  rpt strip_tac >>
  qspecl_then [`results`, `rbuf.buf_operand`, `0`, `sa`, `sb`, `s0`, `w2n w`,
               `ws`] mp_tac store_multi_results_run >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq _ s0 = OK s1` >>
  qexists_tac `s1` >> simp[stmt_state_rel_inst_idx] >>
  `LENGTH ws = LENGTH results` by
    metis_tac[LENGTH_MAP] >>
  `s1.vs_allocas = s0.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `eval_operand rbuf.buf_operand s1 = SOME w` by
    metis_tac[store_result_operand_frame] >>
  suspend "post"
QED

Resume store_multi_results_frag[post]:
  rpt conj_tac
  >- (irule result_state_memory_frame >> qexists_tac `s0` >> simp[] >>
      rpt strip_tac
      >~ [`lookup_var p _ = _`]
      >- (first_x_assum irule >> gvs[local_ptrs_reserved_def] >> metis_tac[])
      >> first_x_assum irule >> first_x_assum drule >> simp[])
  >- (match_mp_tac buffer_vv_holds >> qexistsl_tac [`tv`, `w`] >> simp[] >>
      conj_tac
      >- (Cases_on `rbuf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
      match_mp_tac stack_results_val_in_memory >>
      qexistsl_tac [`get_tenv cx`, `ws`] >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH ws ==> _` (qspec_then `i` mp_tac) >>
      simp[])
  >> simp[lookup_var_def] >> rpt strip_tac >> gvs[lookup_var_def] >>
  metis_tac[]
QED

Finalise store_multi_results_frag
