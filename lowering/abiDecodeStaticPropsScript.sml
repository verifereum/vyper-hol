(*
 * ABI decoding of static values from calldata (#639)
 *
 * TOP-LEVEL:
 *   compile_abi_decode_static_run — compile_abi_decode_static (load, clamp,
 *     MSTORE) with the clamp compile_abi_clamp_basetype emits: it stores
 *     the loaded word when the clamp accepts it and reverts otherwise
 *   compile_abi_decode_static_correct — a word value's word, loaded and
 *     stored by it, is the value in memory at the destination
 *     (val_in_memory)
 *   compile_abi_decode_static_buf_frag — compile_abi_decode_to_buf from
 *     calldata, for a static decode info (static_dec): it copies the
 *     calldata window to the destination when every clamp accepts its word
 *     (dec_ok) and reverts otherwise
 *
 * Also used by entryDecodeStaticProps: static_dec (the static decode
 *   infos), dec_ok (every clamp accepts), dec_frame (what the decode
 *   changes), dec_run (copy or revert), dec_straight (straight-line
 *   code) and their lemmas, and decode_static_buf_run (the induction
 *   behind compile_abi_decode_static_buf_frag).
 *
 * Helpers: the memory-window lemmas.
 *
 * The decode of a static value from calldata (hi_op = Lit 0w, the bound
 * pinned Vyper omits for calldata) runs straight-line code: a word is
 * loaded, clamped and stored, and a tuple, struct or static array
 * decodes its elements at their head offsets.  For a static value the ABI
 * layout and the memory layout coincide (static_dec: each element's ABI
 * size is its memory size), so the decode copies the calldata window
 * word by word, checking each word against its clamp.
 *)
Theory abiDecodeStaticProps
Ancestors
  arithmetic list rich_list words finite_map
  entryDecodeProps moduleLoweringProps
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  valueEncoding valueEncodingProps valueEncodingProofs fragExec
  venomState venomInst
Libs
  wordsLib

(* ===== Straight-line fragments ===== *)

(* Code from st to st' in the current block, with no terminator or call. *)
Definition dec_straight_def:
  dec_straight st st' <=>
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
End

Theorem dec_straight_trans:
  !st st1 st2.
    dec_straight st st1 /\ dec_straight st1 st2 ==> dec_straight st st2
Proof
  rw[dec_straight_def]
  >- metis_tac[inst_extends_trans] >>
  fs[inst_extends_def] >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  simp[]
QED

Theorem dec_straight_emit_op:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') /\ opc <> INVOKE /\ ~is_terminator opc ==>
    dec_straight st st'
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  gvs[dec_straight_def, mk_inst_def] >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def] >>
  rw[] >> simp[]
QED

Theorem dec_straight_emit_add:
  !ops st v st'. emit_op ADD ops st = (v, st') ==> dec_straight st st'
Proof
  rpt strip_tac >> drule dec_straight_emit_op >> simp[is_terminator_def]
QED

Theorem dec_straight_emit_void:
  !opc ops st st'.
    emit_void opc ops st = ((), st') /\ opc <> INVOKE /\ ~is_terminator opc ==>
    dec_straight st st'
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  gvs[dec_straight_def, mk_inst_def] >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def] >>
  rw[] >> simp[]
QED

Theorem dec_straight_clamp:
  !op cl st st'.
    compile_abi_clamp_basetype op cl st = ((), st') ==> dec_straight st st'
Proof
  rpt strip_tac >> drule compile_abi_clamp_structure >>
  simp[dec_straight_def]
QED

(* ===== Static word decode ===== *)

(* compile_abi_decode_static with the basetype clamp: the load gives w (any
   load opcode, as its step says), then the clamp checks w, then w is
   stored at the destination. *)
Theorem compile_abi_decode_static_run:
  !src_op dst_op load_opc cl st st' s p w.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op cl) st = ((), st') /\
    (!id out. step_inst_base (mk_inst id load_opc [src_op] [out]) s =
              OK (update_var out w s)) /\
    eval_operand dst_op s = SOME p /\ fresh_vars_wrt st s ==>
    if abi_clamp_ok cl w then
      ?t. run_inst_seq (emitted_insts st st') s = OK t /\
          vars_pc_only (mstore (w2n p) w s) t /\ fresh_vars_wrt st' t /\
          (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
    else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op load_opc [src_op] st = (val_op, st1)` >>
  rename1 `compile_abi_clamp_basetype val_op cl st1 = (_, st2)` >>
  `compile_abi_clamp_basetype val_op cl st1 = ((), st2)` by
    metis_tac[oneTheory.one] >>
  qspecl_then [`load_opc`, `[src_op]`, `st`, `val_op`, `st1`, `s`, `w`]
    mp_tac decode_emit_update_frame >>
  simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK s1` >>
  drule inst_extends_emit_op >> strip_tac >>
  `inst_extends st1 st2` by
    (drule compile_abi_clamp_structure >> simp[]) >>
  `inst_extends st2 st'` by metis_tac[inst_extends_emit_void] >>
  `inst_extends st1 st'` by metis_tac[inst_extends_trans] >>
  qspecl_then [`st`, `st1`, `st'`, `s`, `s1`] mp_tac run_inst_seq_emit_extend >>
  impl_tac >- simp[] >> disch_then SUBST1_TAC >>
  drule_all decode_clamp_frame >>
  Cases_on `abi_clamp_ok cl w` >> simp[] >> strip_tac
  >- (rename1 `run_inst_seq (emitted_insts st1 st2) s1 = OK s2` >>
      qspecl_then [`st1`, `st2`, `st'`, `s1`, `s2`] mp_tac
        run_inst_seq_emit_extend >>
      impl_tac >- simp[] >> disch_then SUBST1_TAC >>
      `eval_operand dst_op s2 = SOME p /\ eval_operand val_op s2 = SOME w` by
        metis_tac[] >>
      drule_all decode_emit_mstore_frame >> strip_tac >> simp[] >>
      `vars_pc_only s s2 /\
       (!x. not_fresh_at st x ==> lookup_var x s2 = lookup_var x s)` by
        (irule decode_frame_compose >> qexistsl [`st1`, `s1`] >>
         qpat_x_assum `emit_op _ _ st = _`
           (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
         simp[]) >>
      simp[] >> irule decode_mstore_frame >> simp[]) >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >> metis_tac[]
QED

Theorem dec_straight_decode_static:
  !src_op dst_op load_opc cl st st'.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op cl) st = ((), st') /\
    load_opc <> INVOKE /\ ~is_terminator load_opc ==>
    dec_straight st st'
Proof
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op load_opc [src_op] st = (val_op, st1)` >>
  rename1 `compile_abi_clamp_basetype val_op cl st1 = (_, st2)` >>
  `compile_abi_clamp_basetype val_op cl st1 = ((), st2)` by
    metis_tac[oneTheory.one] >>
  `dec_straight st st1` by (drule dec_straight_emit_op >> simp[]) >>
  `dec_straight st1 st2` by metis_tac[dec_straight_clamp] >>
  `dec_straight st2 st'` by
    (drule dec_straight_emit_void >> simp[is_terminator_def]) >>
  metis_tac[dec_straight_trans]
QED

(* A word value's word, loaded by compile_abi_decode_static and checked by
   the clamp type_to_abi_dec_info gives its type, ends as the value in
   memory at the destination.  The load step says which word is loaded:
   CALLDATALOAD at a gives mem_word_at (w2n a) of the calldata
   (step_CALLDATALOAD).  The int-width and flag premises are those of
   word_arg_clamp_ok. *)
Theorem compile_abi_decode_static_correct:
  !src_op dst_op load_opc sfields cenv st st' s p tenv ty tv v.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op
         (case type_to_abi_dec_info sfields cenv ty of
            DecPrimWord c => c
          | _ => NoClamp)) st = ((), st') /\
    (!id out. step_inst_base (mk_inst id load_opc [src_op] [out]) s =
              OK (update_var out (typed_val_to_w256 tv v) s)) /\
    eval_operand dst_op s = SOME p /\ fresh_vars_wrt st s /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!m. ty = BaseT (IntT m) ==> m MOD 8 = 0) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv v) s) t /\
        fresh_vars_wrt st' t /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        val_in_memory tv v (w2n p) t.vs_memory
Proof
  rpt strip_tac >>
  drule_all word_arg_clamp_ok >>
  disch_then (qspec_then `sfields` assume_tac) >>
  drule_all compile_abi_decode_static_run >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `t.vs_memory = (mstore (w2n p) (typed_val_to_w256 tv v) s).vs_memory` by
    metis_tac[vars_pc_only_memory] >>
  drule_all val_in_memory_word >>
  disch_then (qspecl_then [`w2n p`, `t.vs_memory`] SUBST1_TAC) >>
  pop_assum SUBST1_TAC >> rewrite_tac[mstore_mem_word_at_same]
QED

(* ===== Static decode infos ===== *)

(* static_dec info n: info decodes a static value of n bytes whose ABI
   layout is its memory layout: a word, or a static tuple (struct, static
   array) whose elements each take as many bytes in the ABI head as in
   memory.  type_to_abi_dec_info builds DecComplex F for those. *)
Inductive static_dec:
[~prim:]
  static_dec (DecPrimWord c) 32
[~complex:]
  static_decs elems n ==> static_dec (DecComplex F elems) n
[~nil:]
  static_decs [] 0
[~cons:]
  static_dec ei m /\ static_decs elems n ==>
  static_decs ((ei, m, m)::elems) (m + n)
End

Theorem static_dec_shape:
  !ei m. static_dec ei m ==>
         (?c. ei = DecPrimWord c) \/ (?elems. ei = DecComplex F elems)
Proof
  simp[Once static_dec_cases] >> rpt strip_tac >> simp[]
QED

(* dec_ok info cd off: each clamp of info accepts its word of cd, for a
   value encoded at off. *)
Definition dec_ok_def:
  dec_ok (DecPrimWord c) cd off = abi_clamp_ok c (mem_word_at off cd) /\
  dec_ok (DecComplex d elems) cd off = decs_ok elems cd off /\
  dec_ok (DecBytestring _) cd off = F /\
  dec_ok (DecDynArray _ _ _ _ _) cd off = F /\
  decs_ok [] cd off = T /\
  decs_ok ((ei, asz, msz)::elems) cd off =
    (dec_ok ei cd off /\ decs_ok elems cd (off + asz))
Termination
  WF_REL_TAC `measure (\x. case x of
       INL (ei, cd, off) => abi_dec_info_size ei
     | INR (elems, cd, off) =>
         list_size (pair_size abi_dec_info_size
           (pair_size (\x. x) (\(x:num). x))) elems)`
End

(* ===== Frames ===== *)

(* What decoding code from st changes from s to t: the variables past st,
   the pc, and the memory in [q, q + n) only. *)
Definition dec_frame_def:
  dec_frame st q n s t <=>
    vars_pc_only (s with vs_memory := t.vs_memory) t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!i. i < q \/ q + n <= i ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory)
End

(* Decoding n static bytes from calldata at b to memory at q: when ok
   (every clamp accepts), the window is copied and nothing else changes;
   otherwise a revert. *)
Definition dec_run_def:
  dec_run st st' s q b n ok <=>
    if ok then
      ?t. run_inst_seq (emitted_insts st st') s = OK t /\
          fresh_vars_wrt st' t /\ dec_frame st q n s t /\
          mem_bytes_at q n t.vs_memory =
            mem_bytes_at b n s.vs_call_ctx.cc_calldata
    else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
End

Theorem dec_frame_call_ctx:
  !st q n s t. dec_frame st q n s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  rw[dec_frame_def] >> drule vars_pc_only_fields >> simp[]
QED

Theorem dec_frame_eval:
  !st q n s t op w.
    dec_frame st q n s t /\ fresh_vars_wrt st s /\
    eval_operand op s = SOME w ==> eval_operand op t = SOME w
Proof
  rw[dec_frame_def] >> Cases_on `op` >> gvs[eval_operand_def]
  >- (rename1 `lookup_var x s = SOME w` >>
      `not_fresh_at st x` by
        (rw[not_fresh_at_def] >> strip_tac >>
         gvs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >>
         metis_tac[GREATER_EQ]) >>
      metis_tac[]) >>
  drule vars_pc_only_fields >> simp[]
QED

Theorem dec_frame_inst_idx:
  !st q n s t k. dec_frame st q n s t ==>
                 dec_frame st q n s (t with vs_inst_idx := k)
Proof
  rw[dec_frame_def, lookup_var_def] >>
  drule vars_pc_only_inst_idx >> simp[]
QED

Theorem dec_frame_of_vars:
  !st q n s t.
    vars_pc_only s t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    dec_frame st q n s t
Proof
  rw[dec_frame_def] >>
  `t.vs_memory = s.vs_memory` by metis_tac[vars_pc_only_memory] >>
  simp[]
QED

Theorem dec_frame_trans:
  !st q n s t st1 q1 n1 q2 n2 u.
    dec_frame st q1 n1 s t /\ dec_frame st1 q2 n2 t u /\
    st.cs_next_var <= st1.cs_next_var /\
    q <= q1 /\ q1 + n1 <= q + n /\ q <= q2 /\ q2 + n2 <= q + n ==>
    dec_frame st q n s u
Proof
  rw[dec_frame_def]
  >- fs[vars_pc_only_def, venom_state_component_equality]
  >- (`not_fresh_at st1 x` by
        (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >>
         decide_tac) >> metis_tac[]) >>
  `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 t.vs_memory /\
   mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (conj_tac >> first_x_assum irule >> decide_tac) >>
  simp[]
QED

(* ===== Memory windows ===== *)

Theorem mem_bytes_at_bytewise:
  !q n m1 m2.
    (!i. q <= i /\ i < q + n ==> mem_bytes_at i 1 m1 = mem_bytes_at i 1 m2) ==>
    mem_bytes_at q n m1 = mem_bytes_at q n m2
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `q + x` mp_tac) >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem window_concat:
  !q b m n cd mem1 mem2.
    mem_bytes_at q m mem1 = mem_bytes_at b m cd /\
    mem_bytes_at (q + m) n mem2 = mem_bytes_at (b + m) n cd /\
    (!i. i < q + m ==> mem_bytes_at i 1 mem2 = mem_bytes_at i 1 mem1) ==>
    mem_bytes_at q (m + n) mem2 = mem_bytes_at b (m + n) cd
Proof
  rpt strip_tac >> rewrite_tac[mem_bytes_at_split_padded] >>
  `mem_bytes_at q m mem2 = mem_bytes_at q m mem1` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[]
QED

Theorem mem_bytes_at_mstore_outside:
  !i q w s. i < q \/ q + 32 <= i ==>
    mem_bytes_at i 1 (mstore q w s).vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem w2n_add_n2w_lt:
  !(p : bytes32) k. w2n p + k < dimword (:256) ==> w2n (p + n2w k) = w2n p + k
Proof
  Cases >> simp[word_add_n2w]
QED

(* ===== Decoding a static value from calldata ===== *)

Theorem mstore_with_memory:
  !q w s. mstore q w s = s with vs_memory := (mstore q w s).vs_memory
Proof
  simp[mstore_def]
QED

(* A word: compile_abi_decode_static with CALLDATALOAD. *)
Theorem decode_prim_buf_run:
  !dst src c st st' s p a.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord c) st =
      ((), st') /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s ==>
    dec_straight st st' /\
    dec_run st st' s (w2n p) (w2n a) 32
      (dec_ok (DecPrimWord c) s.vs_call_ctx.cc_calldata (w2n a))
Proof
  rpt gen_tac >> strip_tac >> fs[compile_abi_decode_to_buf_def] >>
  conj_tac
  >- (drule dec_straight_decode_static >> simp[is_terminator_def]) >>
  drule compile_abi_decode_static_run >>
  disch_then (qspecl_then [`s`, `p`,
    `mem_word_at (w2n a) s.vs_call_ctx.cc_calldata`] mp_tac) >>
  impl_tac
  >- (simp[mem_word_at_def] >> rpt gen_tac >>
      qspecl_then [`src`, `a`] mp_tac step_CALLDATALOAD >> simp[]) >>
  simp[dec_run_def, dec_ok_def] >>
  qmatch_goalsub_abbrev_tac `abi_clamp_ok c w` >>
  Cases_on `abi_clamp_ok c w` >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `t.vs_memory = (mstore (w2n p) w s).vs_memory` by
    metis_tac[vars_pc_only_memory] >>
  simp[dec_frame_def] >> rpt conj_tac
  >- (qpat_x_assum `vars_pc_only _ t` mp_tac >>
      once_rewrite_tac[mstore_with_memory] >> simp[])
  >- (rpt strip_tac >> irule mem_bytes_at_mstore_outside >> simp[]) >>
  simp[mem_bytes_at_mstore_same, mem_bytes_at_word, Abbr `w`]
QED

Theorem getelemptr_static_emit:
  !src k opc st es st1.
    compile_getelemptr_abi src F k opc st = (es, st1) ==>
    emit_op ADD [src; Lit (n2w k)] st = (es, st1)
Proof
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[])
QED

(* The element pointers of a static element at head offset k. *)
Theorem decode_elem_ptrs:
  !src dst k st es st1 ed st2 s a p.
    compile_getelemptr_abi src F k CALLDATALOAD st = (es, st1) /\
    emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME p /\
    fresh_vars_wrt st s ==>
    ?t. run_inst_seq (emitted_insts st st2) s = OK t /\
        eval_operand es t = SOME (a + n2w k) /\
        eval_operand ed t = SOME (p + n2w k) /\
        fresh_vars_wrt st2 t /\ vars_pc_only s t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        dec_straight st st2
Proof
  rpt gen_tac >> strip_tac >>
  drule getelemptr_static_emit >> strip_tac >>
  `dec_straight st st2` by
    metis_tac[dec_straight_trans, dec_straight_emit_add] >>
  qspecl_then [`ADD`, `[src; Lit (n2w k)]`, `st`, `es`, `st1`, `s`,
               `a + n2w k`] mp_tac decode_emit_update_frame >>
  impl_tac >- (simp[] >> irule step_ADD >> simp[eval_operand_def]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK t1` >>
  `eval_operand dst t1 = SOME p` by metis_tac[] >>
  qspecl_then [`ADD`, `[dst; Lit (n2w k)]`, `st1`, `ed`, `st2`, `t1`,
               `p + n2w k`] mp_tac decode_emit_update_frame >>
  impl_tac >- (simp[] >> irule step_ADD >> simp[eval_operand_def]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) t1 = OK t2` >>
  qexists_tac `t2` >>
  `inst_extends st st1 /\ inst_extends st1 st2` by
    metis_tac[inst_extends_emit_op] >>
  `st.cs_next_var <= st1.cs_next_var` by
    (qpat_x_assum `emit_op _ [src; _] st = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `vars_pc_only s t2 /\
   (!x. not_fresh_at st x ==> lookup_var x t2 = lookup_var x s)` by
    (irule decode_frame_compose >> qexistsl [`st1`, `t1`] >> simp[]) >>
  simp[] >> rpt conj_tac
  >- (irule run_emitted_compose2 >> fs[inst_extends_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* The instructions of a static element: its two pointers, its decode,
   then the remaining elements. *)
Theorem decode_elems_cons_phases:
  !ei m elems dst src k st st'.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      ((ei, m, m)::elems) k k st = ((), st') /\
    static_dec ei m ==>
    ?es st1 ed st2 st3.
      compile_getelemptr_abi src F k CALLDATALOAD st = (es, st1) /\
      emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
      compile_abi_decode_to_buf ed es CALLDATALOAD (Lit 0w) ei st2 =
        ((), st3) /\
      compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
        elems (k + m) (k + m) st3 = ((), st')
Proof
  rpt gen_tac >> strip_tac >> drule static_dec_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = ((), st')` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

Theorem static_dec_straight:
  (!info n. static_dec info n ==>
     !dst src st st'.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
         ((), st') ==> dec_straight st st') /\
  (!elems n. static_decs elems n ==>
     !dst src k st st'.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') ==> dec_straight st st')
Proof
  ho_match_mp_tac static_dec_strongind >> rpt conj_tac
  >- (rpt strip_tac >> fs[compile_abi_decode_to_buf_def] >>
      drule dec_straight_decode_static >> simp[is_terminator_def])
  >- (rpt strip_tac >> fs[compile_abi_decode_to_buf_def] >> metis_tac[])
  >- (rpt strip_tac >>
      fs[compile_abi_decode_to_buf_def, comp_return_def, dec_straight_def,
         inst_extends_def, exprLoweringPropsTheory.emitted_insts_def]) >>
  rpt strip_tac >> rename1 `static_dec ei m` >>
  drule_all decode_elems_cons_phases >> strip_tac >>
  drule getelemptr_static_emit >> strip_tac >>
  `dec_straight st st1 /\ dec_straight st1 st2` by
    metis_tac[dec_straight_emit_add] >>
  `dec_straight st2 st3 /\ dec_straight st3 st'` by metis_tac[] >>
  metis_tac[dec_straight_trans]
QED

(* One static element at head offset k: its pointers and its decode. *)
Theorem decode_elem_step:
  !ei m es st1 ed st2 st3 src dst k st s p a.
    static_dec ei m /\
    compile_getelemptr_abi src F k CALLDATALOAD st = (es, st1) /\
    emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
    compile_abi_decode_to_buf ed es CALLDATALOAD (Lit 0w) ei st2 =
      ((), st3) /\
    (!dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) ei st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + m < dimword (:256) /\ w2n a + m < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) m
         (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a))) /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s /\
    w2n p + k + m < dimword (:256) /\ w2n a + k + m < dimword (:256) ==>
    dec_straight st st3 /\
    dec_run st st3 s (w2n p + k) (w2n a + k) m
      (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a + k))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all decode_elem_ptrs >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st2) s = OK t2` >>
  `w2n (p + n2w k) = w2n p + k /\ w2n (a + n2w k) = w2n a + k` by
    (conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  `t2.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  `dec_straight st2 st3` by metis_tac[static_dec_straight] >>
  conj_tac >- metis_tac[dec_straight_trans] >>
  first_x_assum (qspecl_then [`ed`, `es`, `st2`, `st3`, `t2`, `p + n2w k`,
                              `a + n2w k`] mp_tac) >>
  impl_tac >- (gvs[] >> decide_tac) >>
  `inst_extends st st2 /\ inst_extends st2 st3` by fs[dec_straight_def] >>
  `run_inst_seq (emitted_insts st st3) s =
   run_inst_seq (emitted_insts st2 st3) t2` by
    metis_tac[run_inst_seq_emit_extend] >>
  simp[dec_run_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule dec_frame_trans >>
  qexistsl [`0`, `m`, `w2n p + k`, `w2n p + k`, `st2`, `t2`] >>
  fs[dec_straight_def] >> irule dec_frame_of_vars >> simp[]
QED

(* A static element followed by the remaining ones. *)
Theorem decode_elems_cons_run:
  !ei m elems n dst src k st st' s p a.
    static_dec ei m /\ static_decs elems n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      ((ei, m, m)::elems) k k st = ((), st') /\
    (!dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) ei st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + m < dimword (:256) /\ w2n a + m < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) m
         (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a))) /\
    (!dst src k st st' s p a.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + k + n < dimword (:256) /\ w2n a + k + n < dimword (:256) ==>
       dec_run st st' s (w2n p + k) (w2n a + k) n
         (decs_ok elems s.vs_call_ctx.cc_calldata (w2n a + k))) /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s /\
    w2n p + k + (m + n) < dimword (:256) /\
    w2n a + k + (m + n) < dimword (:256) ==>
    dec_run st st' s (w2n p + k) (w2n a + k) (m + n)
      (decs_ok ((ei, m, m)::elems) s.vs_call_ctx.cc_calldata (w2n a + k))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all decode_elems_cons_phases >> strip_tac >>
  `w2n p + k + m < dimword (:256) /\ w2n a + k + m < dimword (:256)` by
    decide_tac >>
  qspecl_then [`ei`, `m`, `es`, `st1`, `ed`, `st2`, `st3`, `src`, `dst`, `k`,
               `st`, `s`, `p`, `a`] mp_tac decode_elem_step >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `dec_straight st3 st'` by metis_tac[static_dec_straight] >>
  simp[dec_ok_def] >>
  Cases_on `dec_ok ei s.vs_call_ctx.cc_calldata (w2n a + k)` >>
  fs[dec_run_def, dec_straight_def]
  >- (rename1 `run_inst_seq (emitted_insts st st3) s = OK t3` >>
      `eval_operand dst t3 = SOME p /\ eval_operand src t3 = SOME a` by
        metis_tac[dec_frame_eval] >>
      `t3.vs_call_ctx = s.vs_call_ctx` by metis_tac[dec_frame_call_ctx] >>
      first_x_assum (qspecl_then [`dst`, `src`, `k + m`, `st3`, `st'`, `t3`,
                                  `p`, `a`] mp_tac) >>
      impl_tac >- (gvs[] >> decide_tac) >>
      `run_inst_seq (emitted_insts st st') s =
       run_inst_seq (emitted_insts st3 st') t3` by
        metis_tac[run_inst_seq_emit_extend] >>
      simp[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
      qexists_tac `t` >> simp[] >> conj_tac
      >- (irule dec_frame_trans >>
          qexistsl [`m`, `n`, `w2n p + k`, `w2n p + (k + m)`, `st3`, `t3`] >>
          simp[]) >>
      irule window_concat >> conj_tac
      >- (qexists_tac `t3.vs_memory` >> simp[] >> rpt strip_tac >>
          qpat_x_assum `dec_frame st3 _ _ t3 t` mp_tac >>
          simp[dec_frame_def] >> rpt strip_tac >>
          first_x_assum irule >> decide_tac) >>
      `k + w2n p + m = k + (m + w2n p) /\ k + w2n a + m = k + (m + w2n a)` by
        decide_tac >>
      asm_rewrite_tac[]) >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >> metis_tac[]
QED

Theorem decode_static_buf_run:
  (!info n. static_dec info n ==>
     !dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + n < dimword (:256) /\ w2n a + n < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) n
         (dec_ok info s.vs_call_ctx.cc_calldata (w2n a))) /\
  (!elems n. static_decs elems n ==>
     !dst src k st st' s p a.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + k + n < dimword (:256) /\ w2n a + k + n < dimword (:256) ==>
       dec_run st st' s (w2n p + k) (w2n a + k) n
         (decs_ok elems s.vs_call_ctx.cc_calldata (w2n a + k)))
Proof
  ho_match_mp_tac static_dec_strongind >> rpt conj_tac
  >- (rpt strip_tac >> drule_all decode_prim_buf_run >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      fs[compile_abi_decode_to_buf_def, dec_ok_def] >>
      first_x_assum (qspecl_then [`dst`, `src`, `0`, `st`, `st'`, `s`, `p`,
                                  `a`] mp_tac) >> simp[])
  >- (rpt strip_tac >>
      gvs[compile_abi_decode_to_buf_def, comp_return_def, dec_run_def,
          dec_ok_def] >>
      qexists_tac `s` >>
      simp[exprLoweringPropsTheory.emitted_insts_def,
           exprLoweringPropsTheory.run_inst_seq_def, dec_frame_def,
           vars_pc_only_refl, mem_bytes_at_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `static_dec ei m` >> rename1 `static_decs elems n` >>
  qspecl_then [`ei`, `m`, `elems`, `n`, `dst`, `src`, `k`, `st`, `st'`, `s`,
               `p`, `a`] mp_tac decode_elems_cons_run >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* A static value decoded from calldata at a to memory at p: the calldata
   window is copied when every clamp accepts its word, and the decode
   reverts otherwise. *)
Theorem compile_abi_decode_static_buf_frag:
  !info n dst src st st' ctx s0 p a.
    static_dec info n /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
      ((), st') /\
    eval_operand dst s0 = SOME p /\ eval_operand src s0 = SOME a /\
    fresh_vars_wrt st s0 /\
    w2n p + n < dimword (:256) /\ w2n a + n < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) n s0 t /\ fresh_vars_wrt st' t /\
           mem_bytes_at (w2n p) n t.vs_memory =
             mem_bytes_at (w2n a) n s0.vs_call_ctx.cc_calldata /\
           dec_ok info s0.vs_call_ctx.cc_calldata (w2n a))
      (\r. ?t. r = Abort Revert_abort t /\
               ~dec_ok info s0.vs_call_ctx.cc_calldata (w2n a))
Proof
  rpt gen_tac >> strip_tac >>
  `dec_straight st st'` by metis_tac[static_dec_straight] >>
  `dec_run st st' s0 (w2n p) (w2n a) n
     (dec_ok info s0.vs_call_ctx.cc_calldata (w2n a))` by
    (drule (CONJUNCT1 decode_static_buf_run) >> disch_then irule >>
     simp[] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >>
  fs[dec_straight_def, inst_extends_def, IS_PREFIX_APPEND] >>
  qpat_x_assum `dec_run _ _ _ _ _ _ _` mp_tac >> simp[dec_run_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> qexists_tac `t` >>
  simp[dec_frame_inst_idx] >> fs[fresh_vars_wrt_def]
QED
