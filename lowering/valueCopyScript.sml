(*
 * Copying a value held in memory (#638)
 *
 * val_in_memory lays a value out relative to its address, so the bytes of
 * its footprint, copied anywhere, hold the value there.  The internal call
 * copies values this way: the caller stages a memory-passed argument in a
 * buffer of its own, and the callee copies a memory return into the
 * caller's buffer.
 *
 * TOP-LEVEL:
 *   val_in_memory_drop     — val_in_memory at k + off of mem is
 *                            val_in_memory at off of DROP k mem
 *   val_in_memory_relocate — a value's footprint bytes (val_footprint,
 *                            exprSim), copied to another address, hold the
 *                            value there
 *   mcopy_val_in_memory    — MCOPY of at least the footprint does that
 *   mem_bytes_at_mcopy_disjoint — and leaves the bytes outside its
 *                            destination alone
 *   word_tv_memory_size    — a word type's value takes 32 bytes
 *   compile_store_memory_run_size_bound — compile_store_memory at one type puts the
 *                            value at the destination and changes memory
 *                            only there
 *   stage_store_run        — and so does compile_stage_intcall_args's
 *                            store of a memory-passed argument
 *)

Theory valueCopy
Ancestors
  list rich_list arithmetic
  valueEncoding valueEncodingProps valueEncodingProofs exprSim valueCopyBytes
  compileEnv context exprLoweringProps emitHelper emitHelperProps
  entryDecodeProps vyperValue vyperTyping vfmConstants immutableMemoryFrame
  venomInst venomState venomExecSemantics venomMemProps
Libs
  blastLib

Theorem mem_word_at_drop[local]:
  !k off mem. mem_word_at (k + off) mem = mem_word_at off (DROP k mem)
Proof
  simp[mem_word_at_def, DROP_DROP_T]
QED

Theorem mem_bytes_at_drop[local]:
  !k off len mem.
    mem_bytes_at (k + off) len mem = mem_bytes_at off len (DROP k mem)
Proof
  simp[mem_bytes_at_def, DROP_DROP_T]
QED

val drop_rws = [val_in_memory_def, LET_THM, GSYM mem_word_at_drop,
                GSYM mem_bytes_at_drop, AC ADD_ASSOC ADD_COMM];

Theorem val_in_memory_drop:
  (!ty v off mem k.
     val_in_memory ty v (k + off) mem <=>
     val_in_memory ty v off (DROP k mem)) /\
  (!fields field_tvs off mem k.
     fields_in_memory fields field_tvs (k + off) mem <=>
     fields_in_memory fields field_tvs off (DROP k mem)) /\
  (!vs off tv mem k.
     elems_in_memory vs (k + off) tv mem <=>
     elems_in_memory vs off tv (DROP k mem)) /\
  (!(kvs : (num # value) list) off tv mem k.
     kvs_in_memory kvs (k + off) tv mem <=>
     kvs_in_memory kvs off tv (DROP k mem)) /\
  (!vs tvs off mem k.
     tuple_in_memory vs tvs (k + off) mem <=>
     tuple_in_memory vs tvs off (DROP k mem))
Proof
  ho_match_mp_tac val_in_memory_ind >> rpt conj_tac >> rpt strip_tac
  >~ [`val_in_memory ty (StructV fields)`] >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (DynArrayV vs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (SArrayV kvs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (TupleV vs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`fields_in_memory ((name,v)::rest) field_tvs`]
  >- (Cases_on `field_tvs` >- fs drop_rws >> PairCases_on `h` >> fs drop_rws)
  >~ [`tuple_in_memory (v::vs) tvs`] >- (Cases_on `tvs` >> fs drop_rws) >>
  fs drop_rws
QED

(* The footprint bytes of a value, wherever they are copied, hold it. *)
Theorem val_in_memory_relocate:
  !tv v a b len mem mem'.
    val_in_memory tv v a mem /\ val_wf tv v /\ val_footprint tv v <= len /\
    mem_bytes_at b len mem' = mem_bytes_at a len mem ==>
    val_in_memory tv v b mem'
Proof
  rpt strip_tac >>
  `val_in_memory tv v 0 (DROP a mem)` by
    metis_tac[CONJUNCT1 val_in_memory_drop, ADD_CLAUSES] >>
  `mem_bytes_at 0 len (DROP b mem') = mem_bytes_at 0 len (DROP a mem)` by
    metis_tac[mem_bytes_at_drop, ADD_CLAUSES] >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `val_footprint tv v`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_in_memory tv v 0 (DROP b mem')` by
    (irule val_in_memory_footprint_agree >> simp[] >> metis_tac[]) >>
  metis_tac[CONJUNCT1 val_in_memory_drop, ADD_CLAUSES]
QED

Theorem mcopy_val_in_memory:
  !tv v dst src n s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    val_in_memory tv v dst (mcopy dst src n s).vs_memory
Proof
  rpt strip_tac >> match_mp_tac val_in_memory_relocate >>
  qexistsl_tac [`src`, `n`, `s.vs_memory`] >>
  simp[mem_bytes_at_def, mcopy_padded_read]
QED

Theorem mem_bytes_at_write_disjoint:
  !a len d bytes s.
    a + len <= d \/ d + LENGTH bytes <= a ==>
    mem_bytes_at a len (write_memory_with_expansion d bytes s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < d + LENGTH bytes - LENGTH s.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE d exp` >>
      `d + LENGTH bytes <= LENGTH exp` by simp[Abbr `exp`] >>
      `mem_bytes_at a len
         (TAKE d exp ++ bytes ++ DROP (d + LENGTH bytes) exp) =
       mem_bytes_at a len exp` by
        (simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >>
         simp[]) >>
      simp[Abbr `exp`, mem_bytes_at_append_zero]) >>
  `d + LENGTH bytes <= LENGTH s.vs_memory` by simp[] >>
  simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >> simp[]
QED

Theorem mem_bytes_at_mcopy_disjoint:
  !a len dst src n s.
    a + len <= dst \/ dst + n <= a ==>
    mem_bytes_at a len (mcopy dst src n s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  rpt strip_tac >> simp[mcopy_def, LET_THM] >>
  irule mem_bytes_at_write_disjoint >> simp[LENGTH_TAKE_EQ]
QED


(* ===== Storing a value into memory ===== *)

Theorem word_tv_memory_size:
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

Theorem eval_operand_update_not_fresh[local]:
  !op sa n w s.
    (!x. op = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= n ==>
    eval_operand op (update_var (STRING #"%" (toString n)) w s) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> TRY (simp[update_var_def] >> NO_TAC) >>
  gvs[not_fresh_at_def] >> rw[] >> metis_tac[]
QED

(* The copy length compile_bytestring_copy_len computes from the length
   word: the length word and the data rounded up to whole words. *)
Theorem bytestring_copy_len_word[local]:
  !L. L + 64 < dimword (:256) ==>
      w2n (((n2w L + 31w) && i2w (-32)) + 32w : bytes32) =
      32 + 32 * word_size L
Proof
  rpt strip_tac >>
  `(i2w (-32) : bytes32) = -32w` by simp[integer_wordTheory.i2w_def] >>
  `!w:bytes32. w && -32w = (w >>> 5) << 5` by blastLib.BBLAST_TAC >>
  `(L + 31) DIV 32 * 32 <= L + 31` by
    (qspec_then `32` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `L + 31` mp_tac) >> decide_tac) >>
  `(n2w (L + 31) : bytes32) >>> 5 << 5 = n2w ((L + 31) DIV 32 * 32)` by
    (qmatch_goalsub_abbrev_tac `q << 5` >>
     `q = n2w (w2n q)` by simp[] >> pop_assum SUBST1_TAC >>
     `L + 31 < dimword (:256) /\ (L + 31) DIV 32 * 32 < dimword (:256)` by
       decide_tac >>
     fs[Abbr `q`, wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr, LESS_MOD]) >>
  `(n2w L + 31w : bytes32) = n2w (L + 31)` by
    simp[wordsTheory.word_add_n2w] >>
  asm_rewrite_tac[] >>
  `(L + 31) DIV 32 * 32 + 32 < dimword (:256)` by decide_tac >>
  fs[wordsTheory.word_add_n2w, word_size_def, LESS_MOD]
QED

(* The steps of the copy, as rewrites: the operands' values are THE of
   their evaluation, so simp can chain them. *)
Theorem step_MLOAD_some[local]:
  !op1 id out ss.
    IS_SOME (eval_operand op1 ss) ==>
    step_inst_base (mk_inst id MLOAD [op1] [out]) ss =
      OK (update_var out (mload (w2n (THE (eval_operand op1 ss))) ss) ss)
Proof
  rpt strip_tac >> Cases_on `eval_operand op1 ss` >> gvs[] >>
  irule step_MLOAD >> simp[]
QED

Theorem step_ADD_some[local]:
  !op1 op2 id out ss.
    IS_SOME (eval_operand op1 ss) /\ IS_SOME (eval_operand op2 ss) ==>
    step_inst_base (mk_inst id ADD [op1; op2] [out]) ss =
      OK (update_var out
            (THE (eval_operand op1 ss) + THE (eval_operand op2 ss)) ss)
Proof
  rpt strip_tac >> Cases_on `eval_operand op1 ss` >>
  Cases_on `eval_operand op2 ss` >> gvs[] >> irule step_ADD >> simp[]
QED

Theorem step_AND_some[local]:
  !op1 op2 id out ss.
    IS_SOME (eval_operand op1 ss) /\ IS_SOME (eval_operand op2 ss) ==>
    step_inst_base (mk_inst id AND [op1; op2] [out]) ss =
      OK (update_var out
            (word_and (THE (eval_operand op1 ss)) (THE (eval_operand op2 ss)))
            ss)
Proof
  rpt strip_tac >> Cases_on `eval_operand op1 ss` >>
  Cases_on `eval_operand op2 ss` >> gvs[] >> irule step_AND >> simp[]
QED

Theorem step_MCOPY_some[local]:
  !d a n id s.
    IS_SOME (eval_operand d s) /\ IS_SOME (eval_operand a s) /\
    IS_SOME (eval_operand n s) ==>
    step_inst_base (mk_inst id MCOPY [d; a; n] []) s =
      OK (mcopy (w2n (THE (eval_operand d s))) (w2n (THE (eval_operand a s)))
            (w2n (THE (eval_operand n s))) s)
Proof
  rpt strip_tac >> Cases_on `eval_operand d s` >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand n s` >> gvs[] >>
  simp[step_inst_base_def]
QED

Theorem store_bytestring_run[local]:
  !val_op dst_op sa sb s src dst L.
    compile_store_bytestring val_op dst_op sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    eval_operand val_op s = SOME src /\ eval_operand dst_op s = SOME dst /\
    mem_word_at (w2n src) s.vs_memory = n2w L /\ L + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory =
        (mcopy (w2n dst) (w2n src) (32 + 32 * word_size L) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac bytestring_copy_len_word >>
  `!n w s'. sa.cs_next_var <= n ==>
     eval_operand dst_op (update_var (STRING #"%" (toString n)) w s') =
       eval_operand dst_op s' /\
     eval_operand val_op (update_var (STRING #"%" (toString n)) w s') =
       eval_operand val_op s'` by
    (rpt gen_tac >> strip_tac >> conj_tac >>
     irule eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def, LET_THM] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       venomInstTheory.is_terminator_def] >>
  simp[run_inst_seq_def, step_MLOAD_some, step_ADD_some, step_AND_some,
       step_MCOPY_some, eval_operand_def, lookup_var_update_var,
       GSYM mem_word_at_eq_mload] >>
  simp[update_var_def, mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def, update_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Theorem emit_mstore_run[local]:
  !sa sb dst src s d w.
    emit_void MSTORE [dst; src] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n d) w s)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[same_blocks_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, run_inst_seq_def] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_ignore_bind_def, comp_return_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [dst; src] []) s =
     OK (mstore (w2n d) w s)` by (irule step_MSTORE >> simp[]) >>
  fs[venomInstTheory.mk_inst_def]
QED

Theorem emit_mcopy_run:
  !sa sb dst src n s d a.
    emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    n < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n d) (w2n a) n s)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[same_blocks_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, run_inst_seq_def] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[step_inst_base_def, venomInstTheory.mk_inst_def, eval_operand_def]
QED

(* compile_store_memory at one type ty: a word type's value, held by src
   as its typed word, or any other type's value, held in memory at src,
   ends up in memory at dst, and memory changes only in the
   type_memory_size bytes from dst.  type_memory_bytes, the size the
   lowering copies, is the compile environment's account of that size
   (build_compile_env_type_memory_bytes). *)
Theorem compile_store_memory_run_size_bound_capacity[local]:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ty` >> gvs[compile_store_memory_def]
  >- (drule_all emit_mstore_run >> strip_tac >> simp[] >>
      drule_all word_tv_memory_size >> strip_tac >>
      drule_all val_in_memory_word >> strip_tac >>
      simp[mstore_mem_word_at_same] >> rpt conj_tac
      >~ [`LENGTH _ <= LENGTH _`]
      >- simp[immutable_mstore_capacity, MAX_DEF]
      >~ [`mem_bytes_at`]
      >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
      simp[mstore_def, LET_THM, venom_state_component_equality]) >>
  Cases_on `is_bytestring_type ty` >> gvs[]
  >- suspend "bytestring" >>
  suspend "copy"
QED

Resume compile_store_memory_run_size_bound_capacity[bytestring]:
  `?L. mem_word_at (w2n sw) s.vs_memory = n2w L /\
       val_footprint tv v = 32 + 32 * word_size L` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_bytestring_type_def, evaluate_type_def] >> Cases_on `v` >>
         gvs[value_has_type_def, val_in_memory_def, val_footprint_def] >>
         qmatch_asmsub_abbrev_tac `mem_word_at _ _ = n2w LL` >>
         `LL < dimword (:256)` by (fs[Abbr `LL`] >> decide_tac) >>
         qexists_tac `LL` >> fs[LESS_MOD]) >>
     gvs[evaluate_type_def] >> Cases_on `v` >>
     gvs[value_has_type_def, val_in_memory_def, val_footprint_def] >>
     qmatch_asmsub_abbrev_tac `mem_word_at _ _ = n2w LL` >>
     `LL < dimword (:256)` by (fs[Abbr `LL`] >> decide_tac) >>
     qexists_tac `LL` >> fs[LESS_MOD]) >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  qspecl_then [`src`, `dst`, `sa`, `sb`, `s`, `sw`, `dw`, `L`] mp_tac
    store_bytestring_run >>
  `L <= 32 * word_size L` by
    (rewrite_tac[word_size_def] >> qspec_then `32` mp_tac DIVISION >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `L + 31` strip_assume_tac) >> decide_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >> simp[] >>
  rpt conj_tac
  >- (irule mcopy_val_in_memory >> simp[])
  >- (qpat_x_assum `_ with <| vs_vars := _; vs_memory := _ |> = s` mp_tac >>
      simp[venom_state_component_equality])
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF]
QED

Resume compile_store_memory_run_size_bound_capacity[copy]:
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  Cases_on `type_memory_size tv` >> gvs[compile_copy_memory_def]
  >- (gvs[comp_return_def] >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def] >>
      match_mp_tac val_in_memory_relocate >>
      qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >>
      simp[mem_bytes_at_def]) >>
  rename1 `SUC n` >>
  qspecl_then [`sa`, `sb`, `dst`, `src`, `SUC n`, `s`, `dw`, `sw`] mp_tac
    emit_mcopy_run >>
  impl_tac >- simp[] >> strip_tac >> simp[] >> rpt conj_tac
  >~ [`val_in_memory`] >- (irule mcopy_val_in_memory >> simp[])
  >~ [`lookup_var`]
  >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
  >~ [`mem_bytes_at`]
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac)
  >~ [`LENGTH _ <= LENGTH _`]
  >- simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF] >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED

Finalise compile_store_memory_run_size_bound_capacity

Theorem compile_store_memory_run_size_bound_with_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  ACCEPT_TAC compile_store_memory_run_size_bound_capacity
QED

Theorem compile_store_memory_run_frame:
  !cenv src dst ty sa sb s tenv tv v sw dw bound.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\
    (if is_bytestring_type ty then val_footprint tv v <= bound
     else type_memory_size tv <= bound) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + bound <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ty` >> gvs[compile_store_memory_def]
  >- (`~is_bytestring_type ty` by metis_tac[is_bytestring_word_type] >>
      gvs[] >> drule_all emit_mstore_run >> strip_tac >> simp[] >>
      drule_all word_tv_memory_size >> strip_tac >>
      drule_all val_in_memory_word >> strip_tac >>
      simp[mstore_mem_word_at_same] >> rpt conj_tac
      >~ [`mem_bytes_at`]
      >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
      simp[mstore_def, LET_THM, venom_state_component_equality]) >>
  Cases_on `is_bytestring_type ty` >> gvs[]
  >- suspend "bytestring" >>
  suspend "copy"
QED

Resume compile_store_memory_run_frame[bytestring]:
  `?L. mem_word_at (w2n sw) s.vs_memory = n2w L /\
       val_footprint tv v = 32 + 32 * word_size L` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_bytestring_type_def, evaluate_type_def] >> Cases_on `v` >>
         gvs[value_has_type_def, val_in_memory_def, val_footprint_def] >>
         qmatch_asmsub_abbrev_tac `mem_word_at _ _ = n2w LL` >>
         `LL < dimword (:256)` by (fs[Abbr `LL`] >> decide_tac) >>
         qexists_tac `LL` >> fs[LESS_MOD]) >>
     gvs[evaluate_type_def] >> Cases_on `v` >>
     gvs[value_has_type_def, val_in_memory_def, val_footprint_def] >>
     qmatch_asmsub_abbrev_tac `mem_word_at _ _ = n2w LL` >>
     `LL < dimword (:256)` by (fs[Abbr `LL`] >> decide_tac) >>
     qexists_tac `LL` >> fs[LESS_MOD]) >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  qspecl_then [`src`, `dst`, `sa`, `sb`, `s`, `sw`, `dw`, `L`] mp_tac
    store_bytestring_run >>
  `L <= 32 * word_size L` by
    (rewrite_tac[word_size_def] >> qspec_then `32` mp_tac DIVISION >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `L + 31` strip_assume_tac) >> decide_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >> simp[] >>
  rpt conj_tac
  >- (irule mcopy_val_in_memory >> simp[])
  >- (qpat_x_assum `_ with <| vs_vars := _; vs_memory := _ |> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac
QED

Resume compile_store_memory_run_frame[copy]:
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  Cases_on `type_memory_size tv` >> gvs[compile_copy_memory_def]
  >- (gvs[comp_return_def] >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def] >>
      match_mp_tac val_in_memory_relocate >>
      qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >>
      simp[mem_bytes_at_def]) >>
  rename1 `SUC n` >>
  qspecl_then [`sa`, `sb`, `dst`, `src`, `SUC n`, `s`, `dw`, `sw`] mp_tac
    emit_mcopy_run >>
  impl_tac >- simp[] >> strip_tac >> simp[] >> rpt conj_tac
  >~ [`val_in_memory`] >- (irule mcopy_val_in_memory >> simp[])
  >~ [`lookup_var`]
  >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
  >~ [`mem_bytes_at`]
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED

Finalise compile_store_memory_run_frame

Theorem compile_store_memory_run_size_bound:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_store_memory_run_frame >>
  simp[] >>
  qexistsl_tac [`cenv`, `dst`, `src`, `sw`, `tenv`, `ty`] >>
  simp[] >> metis_tac[val_footprint_le]
QED

Theorem compile_store_memory_run_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  drule_all compile_store_memory_run_size_bound_capacity >> simp[]
QED
Theorem compile_store_memory_run:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  drule_all compile_store_memory_run_size_bound >> simp[]
QED

(* The store compile_stage_intcall_args emits for a memory-passed argument
   into its buffer dst: compile_store_memory at one type, except that it
   copies with MCOPY whatever type_memory_bytes is. *)
Theorem stage_store_run:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    (if is_word_type ty then emit_void MSTORE [dst; src]
     else if is_bytestring_type ty then
       do compile_store_bytestring src dst; return () od
     else emit_void MCOPY [dst; src; Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ty \/ is_bytestring_type ty`
  >- (`compile_store_memory cenv src dst ty ty sa = ((),sb)` by
        (qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
         Cases_on `is_word_type ty` >> fs[compile_store_memory_def] >>
         Cases_on `compile_store_bytestring src dst sa` >>
         simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
      qspecl_then [`cenv`, `src`, `dst`, `ty`, `sa`, `sb`, `s`, `tenv`, `tv`,
                   `v`, `sw`, `dw`] mp_tac compile_store_memory_run >>
      impl_tac >- simp[] >> simp[]) >>
  gvs[] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  qspecl_then [`sa`, `sb`, `dst`, `src`, `type_memory_size tv`, `s`, `dw`,
               `sw`] mp_tac emit_mcopy_run >>
  impl_tac >- simp[] >> strip_tac >> simp[] >> rpt conj_tac
  >~ [`val_in_memory`] >- (irule mcopy_val_in_memory >> simp[])
  >~ [`lookup_var`]
  >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
  >~ [`mem_bytes_at`]
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED
