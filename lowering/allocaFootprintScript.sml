(*
 * Memory footprints of the lowering's leaf helpers
 *
 * Every instruction a leaf helper emits reads and writes memory below the
 * allocation frontier (run_inst_seq_mem_ok), given the helper's own
 * precondition.  A scratch buffer is the ALLOCA the helper itself emits:
 * its base p is the frontier when the site is fresh, or the site's earlier
 * allocation when the ALLOCA runs again (a loop), and either way
 * [p, p + size) lies below the frontier after it (alloca_site_frontier);
 * a local variable's pointer lies below the frontier by local_ptrs_rel.
 *
 * TOP-LEVEL:
 *   emit_op_mem_ok, emit_void_mem_ok, emit_inst_mem_ok
 *                             — one emitted instruction
 *   emit_mstore_mem_ok, emit_mload_mem_ok, emit_mcopy_mem_ok,
 *   emit_calldatacopy_mem_ok, emit_return_mem_ok
 *                             — one memory instruction on a region below
 *                               the frontier
 *   return_buffer_mem_safe    — a RETURN of such a region is a memory-safe
 *                               end of the run
 *   compile_alloc_buffer_mem_ok
 *                             — the ALLOCA, with the state after it
 *   compile_alloc_buffer_frag_mem
 *                             — the same as a frag_exec_mem fragment
 *   compile_keccak256_word_mem_ok, compile_keccak256_bytesm_mem_ok,
 *   compile_mapping_subscript_mem_ok
 *                             — scratch-buffer helpers
 *   local_ptr_below_frontier, local_ptr_field_below_frontier
 *                             — local variable pointers
 *
 * Helpers:
 *   alloca_site_cases, step_alloca_site, alloca_site_frontier
 *                             — the ALLOCA at a site: where its buffer is,
 *                               the state after it, the buffer's bound
 *   scratch_mstore_mem_ok     — an MSTORE at a known offset below the
 *                               frontier
 *   eval_operand_update_unbound
 *                             — an operand survives binding an unbound
 *                               variable
 *   fresh_vars_wrt_next       — the next variables are unbound
 *   emitted_insts_three, emitted_insts_five
 *                             — the instructions of a helper, by its states
 *)

Theory allocaFootprint
Ancestors
  fragExecMem instMemFrontier loweringHalt abiBuiltinAllocation
  abiEncoderWrites builtinHashing exprLowering
  context emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomInst venomExecSemantics venomMemDefs memSafeRun
  finite_map list rich_list words arithmetic abiDecoderIndexInit

(* ===== State facts ===== *)

Theorem update_var_fields[simp]:
  (update_var x v s).vs_alloca_next = s.vs_alloca_next /\
  (update_var x v s).vs_allocas = s.vs_allocas /\
  (update_var x v s).vs_labels = s.vs_labels /\
  (update_var x v s).vs_vars = s.vs_vars |+ (x, v)
Proof
  simp[update_var_def]
QED

Theorem mstore_fields[simp]:
  (mstore p w s).vs_vars = s.vs_vars /\
  (mstore p w s).vs_labels = s.vs_labels
Proof
  simp[mstore_def]
QED

Theorem eval_operand_same_vars:
  !op s s'.
    s'.vs_vars = s.vs_vars /\ s'.vs_labels = s.vs_labels ==>
    eval_operand op s' = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem allocate_state_fields[simp]:
  (abi_builtin_allocate_state id n s).vs_vars = s.vs_vars /\
  (abi_builtin_allocate_state id n s).vs_labels = s.vs_labels /\
  (abi_builtin_allocate_state id n s).vs_memory = s.vs_memory
Proof
  Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
  simp[abi_builtin_allocate_state_def]
QED

Theorem eval_operand_allocate_state[simp]:
  eval_operand op (abi_builtin_allocate_state id n s) = eval_operand op s
Proof
  irule eval_operand_same_vars >> simp[]
QED

Theorem fresh_vars_wrt_next:
  !st s n.
    fresh_vars_wrt st s /\ st.cs_next_var <= n ==>
    STRING #"%" (toString n) NOTIN FDOM s.vs_vars
Proof
  rw[fresh_vars_wrt_def]
QED

(* Binding a variable that is unbound in s leaves every operand that
   evaluates in s as it was. *)
Theorem eval_operand_update_unbound:
  !op s x v w.
    eval_operand op s = SOME w /\ x NOTIN FDOM s.vs_vars ==>
    eval_operand op (update_var x v s) = SOME w
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[FLOOKUP_DEF]
QED

(* ===== The instructions a helper emits, by its states ===== *)

Theorem emitted_insts_three:
  !st st1 st2 st3 i1 i2 i3.
    st1.cs_current_insts = st.cs_current_insts ++ [i1] /\
    st2.cs_current_insts = st1.cs_current_insts ++ [i2] /\
    st3.cs_current_insts = st2.cs_current_insts ++ [i3] ==>
    emitted_insts st st3 = [i1; i2; i3]
Proof
  rpt gen_tac >> strip_tac >> simp[emitted_insts_def] >>
  ntac 3 (pop_assum SUBST1_TAC) >>
  simp[DROP_APPEND, DROP_LENGTH_NIL]
QED

Theorem emitted_insts_five:
  !st st1 st2 st3 st4 st5 i1 i2 i3 i4 i5.
    st1.cs_current_insts = st.cs_current_insts ++ [i1] /\
    st2.cs_current_insts = st1.cs_current_insts ++ [i2] /\
    st3.cs_current_insts = st2.cs_current_insts ++ [i3] /\
    st4.cs_current_insts = st3.cs_current_insts ++ [i4] /\
    st5.cs_current_insts = st4.cs_current_insts ++ [i5] ==>
    emitted_insts st st5 = [i1; i2; i3; i4; i5]
Proof
  rpt gen_tac >> strip_tac >> simp[emitted_insts_def] >>
  ntac 5 (pop_assum SUBST1_TAC) >>
  simp[DROP_APPEND, DROP_LENGTH_NIL]
QED

(* ===== One emitted instruction ===== *)

Theorem emit_op_mem_ok:
  !opc ops st v st' s.
    emit_op opc ops st = (v, st') /\
    inst_mem_below_frontier
      (mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)])
      s /\
    inst_dload_in_section
      (mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)])
      s ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_mem_ok_last]
QED

Theorem emit_void_mem_ok:
  !opc ops st st' s.
    emit_void opc ops st = ((), st') /\
    inst_mem_below_frontier (mk_inst st.cs_next_id opc ops []) s /\
    inst_dload_in_section (mk_inst st.cs_next_id opc ops []) s ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_mem_ok_last]
QED

Theorem emit_inst_mem_ok:
  !opc ops outs st st' s.
    emit_inst opc ops outs st = ((), st') /\
    inst_mem_below_frontier (mk_inst st.cs_next_id opc ops outs) s /\
    inst_dload_in_section (mk_inst st.cs_next_id opc ops outs) s ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_mem_ok_last]
QED

(* ===== One memory instruction on a region below the frontier ===== *)

Theorem emit_mstore_mem_ok:
  !dst v st st' s d.
    emit_void MSTORE [dst; v] st = ((), st') /\
    eval_operand dst s = SOME d /\ w2n d + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_void_mem_ok >> disch_then irule >>
  simp[below_frontier_MSTORE] >> rpt strip_tac >> gvs[]
QED

Theorem emit_mload_mem_ok:
  !ptr st v st' s p.
    emit_op MLOAD [ptr] st = (v, st') /\
    eval_operand ptr s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_op_mem_ok >> disch_then irule >>
  simp[below_frontier_MLOAD] >> rpt strip_tac >> gvs[]
QED

Theorem emit_mcopy_mem_ok:
  !dst src len st st' s d a n.
    emit_void MCOPY [dst; src; len] st = ((), st') /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand len s = SOME n /\
    (w2n n = 0 \/ w2n a + w2n n <= s.vs_alloca_next) /\
    (w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_void_mem_ok >> disch_then irule >>
  simp[below_frontier_MCOPY] >> rpt strip_tac >> gvs[]
QED

Theorem emit_calldatacopy_mem_ok:
  !dst src len st st' s d a n.
    emit_void CALLDATACOPY [dst; src; len] st = ((), st') /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand len s = SOME n /\
    (w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_void_mem_ok >> disch_then irule >>
  simp[below_frontier_CALLDATACOPY] >> rpt strip_tac >> gvs[]
QED

Theorem emit_return_mem_ok:
  !buf len st st' s b l.
    emit_inst RETURN [buf; len] [] st = ((), st') /\
    eval_operand buf s = SOME b /\ eval_operand len s = SOME l /\
    (w2n l = 0 \/ w2n b + w2n l <= s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> drule emit_inst_mem_ok >> disch_then irule >>
  simp[below_frontier_RETURN] >> rpt strip_tac >> gvs[]
QED

(* A RETURN of a region below the frontier is a memory-safe end of the run:
   the run from the RETURN's own state is memory-safe. *)
Theorem return_buffer_mem_safe:
  !fuel ctx fn s bb id buf len b l.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id RETURN [buf; len] []) /\
    eval_operand buf s = SOME b /\ eval_operand len s = SOME l /\
    (w2n l = 0 \/ w2n b + w2n l <= s.vs_alloca_next) ==>
    mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `(mk_inst id RETURN [buf; len] []).inst_opcode = RETURN` by
    simp[mk_inst_def] >>
  `?h. step_inst fuel ctx (mk_inst id RETURN [buf; len] []) s = Halt h` by
    (fs[step_inst_non_invoke] >> irule_at Any step_RETURN >> gs[]) >>
  `inst_mem_below_frontier (mk_inst id RETURN [buf; len] []) s` by
    (simp[below_frontier_RETURN] >> rpt strip_tac >> gvs[]) >>
  `mem_safe_step fuel ctx (mk_inst id RETURN [buf; len] []) s` by
    gs[mem_safe_step_non_invoke] >>
  qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`, `mk_inst id RETURN [buf; len] []`,
               `Halt h`] mp_tac run_from_step_exit >>
  gs[]
QED

(* ===== The scratch buffer's ALLOCA ===== *)

(* The ALLOCA at site id, of size n, places its buffer at p: the frontier
   when the site is fresh, else the site's earlier allocation.  The state
   after it is abi_builtin_allocate_state's, which records the fresh
   allocation and is the identity otherwise. *)
Theorem alloca_site_cases:
  !id n s p.
    FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (p, n) <=>
    (FLOOKUP s.vs_allocas id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas id = SOME (p, n)
Proof
  rpt gen_tac >> Cases_on `FLOOKUP s.vs_allocas id` >>
  simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem step_alloca_site:
  !id n out s p.
    FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (p, n) /\
    n < dimword (:256) ==>
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s =
      OK (update_var out (n2w p) (abi_builtin_allocate_state id n s))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE, step_alloca_fresh]
  >> gvs[abi_builtin_allocate_state_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def]
QED

Theorem alloca_site_frontier:
  !id n s p.
    FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (p, n) /\
    alloca_next_valid s ==>
    p + n <= (abi_builtin_allocate_state id n s).vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE, alloca_next_valid_def] >>
  res_tac >> simp[]
QED

(* An MSTORE at a known offset below the frontier steps, and passes the
   check. *)
Theorem scratch_mstore_mem_ok:
  !id dst v s q w.
    eval_operand dst s = SOME (n2w q) /\ eval_operand v s = SOME w /\
    q + 32 <= s.vs_alloca_next /\ q < dimword (:256) ==>
    step_inst_base (mk_inst id MSTORE [dst; v] []) s = OK (mstore q w s) /\
    inst_mem_below_frontier (mk_inst id MSTORE [dst; v] []) s
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (n2w q : bytes32) = q` by simp[LESS_MOD] >>
  qspecl_then [`dst`, `v`, `n2w q`, `w`, `id`, `s`] mp_tac step_MSTORE >>
  simp[below_frontier_MSTORE] >> rpt strip_tac >> gvs[]
QED

Theorem compile_alloc_buffer_mem_ok:
  !n st buf st' s p.
    compile_alloc_buffer n st = (buf, st') /\ fresh_vars_wrt st s /\
    alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id n s).vs_allocas
      st.cs_next_id = SOME (p, n) /\
    n < dimword (:256) ==>
    buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
    buf.buf_size = n /\
    emitted_insts st st' =
      [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString st.cs_next_var)]] /\
    st'.cs_current_insts =
      st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString st.cs_next_var)]] /\
    st'.cs_next_id = st.cs_next_id + 1 /\
    st'.cs_next_var = st.cs_next_var + 1 /\
    run_inst_seq_mem_ok (emitted_insts st st') s /\
    step_inst_base
      (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString st.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) (n2w p)
            (abi_builtin_allocate_state st.cs_next_id n s)) /\
    p + n <= (abi_builtin_allocate_state st.cs_next_id n s).vs_alloca_next /\
    fresh_vars_wrt st'
      (update_var (STRING #"%" (toString st.cs_next_var)) (n2w p)
         (abi_builtin_allocate_state st.cs_next_id n s))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  drule_all step_alloca_site >>
  disch_then (qspec_then `STRING #"%" (toString st.cs_next_var)` assume_tac) >>
  drule_all alloca_site_frontier >> strip_tac >>
  gs[run_inst_seq_mem_ok_last] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  irule fresh_vars_wrt_advance >> simp[] >> qexists_tac `st` >>
  fs[fresh_vars_wrt_def]
QED

(* ===== ALLOCA template ===== *)

(* compile_alloc_buffer's ALLOCA touches no source memory. *)
Theorem compile_alloc_buffer_frag_mem:
  !ctx n st buf st' P Q R.
    compile_alloc_buffer n st = (buf,st') /\
    (!s. P s ==> ?s1.
      step_inst_base
        (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
          [STRING #"%" (toString st.cs_next_var)]) s = OK s1 /\
      Q (s1 with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  irule frag_exec_mem_step >> simp[mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[]) >>
  disj1_tac >> qexists_tac `s1` >> gvs[mk_inst_def]
QED

(* ===== Scratch-buffer helpers ===== *)


(* ALLOCA 32; MSTORE [buf; val]; SHA3 [buf; m] with m <= 32 *)
Theorem compile_keccak256_bytesm_mem_ok:
  !val_op m st op st' s w p.
    compile_keccak256_bytesm val_op m st = (op, st') /\ m <= 32 /\
    eval_operand val_op s = SOME w /\ fresh_vars_wrt st s /\
    alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
      st.cs_next_id = SOME (p, 32) /\
    p + 32 < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 32 st = (buf, st1)` >>
  rename1 `emit_void MSTORE _ st1 = ((), st2)` >>
  drule compile_alloc_buffer_mem_ok >>
  disch_then (qspecl_then [`s`, `p`] mp_tac) >>
  impl_tac >- fs[dimword_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK s1` >>
  `STRING #"%" (toString st.cs_next_var) NOTIN FDOM s.vs_vars` by
    (irule fresh_vars_wrt_next >> qexists_tac `st` >> fs[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_mem_ok_last] >>
  qabbrev_tac `x = STRING #"%" (toString st.cs_next_var)` >>
  `p < dimword (:256)` by decide_tac >>
  `w2n (n2w p : bytes32) = p` by simp[LESS_MOD] >>
  `w2n (n2w m : bytes32) = m` by
    (simp[] >> irule LESS_MOD >> decide_tac) >>
  `p + 32 <= s1.vs_alloca_next` by simp[Abbr `s1`] >>
  `eval_operand (Var x) s1 = SOME (n2w p)` by
    simp[Abbr `s1`, eval_operand_update_var] >>
  `eval_operand val_op s1 = SOME w` by
    (simp[Abbr `s1`] >> irule eval_operand_update_unbound >> fs[]) >>
  `!id. step_inst_base (mk_inst id MSTORE [Var x; val_op] []) s1 =
        OK (mstore p w s1) /\
        inst_mem_below_frontier (mk_inst id MSTORE [Var x; val_op] []) s1` by
    (gen_tac >> irule scratch_mstore_mem_ok >> simp[]) >>
  `!id out. inst_mem_below_frontier (mk_inst id SHA3 [Var x; Lit (n2w m)] out)
              (mstore p w s1)` by
    (simp[below_frontier_SHA3, eval_operand_lit] >> rpt strip_tac >> gvs[]) >>
  qspecl_then [`st`, `st1`, `st2`, `st'`] mp_tac emitted_insts_three >>
  gs[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last]
QED

(* ALLOCA 32; MSTORE [buf; val]; SHA3 [buf; 32], as the m = 32 case *)
Theorem compile_keccak256_word_bytesm:
  !val_op. compile_keccak256_word val_op = compile_keccak256_bytesm val_op 32
Proof
  simp[compile_keccak256_word_def, compile_keccak256_bytesm_def]
QED

Theorem compile_keccak256_word_mem_ok:
  !val_op st op st' s w p.
    compile_keccak256_word val_op st = (op, st') /\
    eval_operand val_op s = SOME w /\ fresh_vars_wrt st s /\
    alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
      st.cs_next_id = SOME (p, 32) /\
    p + 32 < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt gen_tac >> strip_tac >> fs[compile_keccak256_word_bytesm] >>
  drule compile_keccak256_bytesm_mem_ok >> disch_then irule >> simp[] >>
  metis_tac[]
QED

(* ALLOCA 64; MSTORE [buf; slot]; ADD [buf; 32]; MSTORE [buf + 32; key];
   SHA3 [buf; 64] *)
Theorem compile_mapping_subscript_mem_ok:
  !base_slot key_op st op st' s b k p.
    compile_mapping_subscript base_slot key_op st = (op, st') /\
    eval_operand base_slot s = SOME b /\ eval_operand key_op s = SOME k /\
    fresh_vars_wrt st s /\ alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id 64 s).vs_allocas
      st.cs_next_id = SOME (p, 64) /\
    p + 64 < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 64 st = (buf, st1)` >>
  rename1 `emit_void MSTORE [_; base_slot] st1 = ((), st2)` >>
  rename1 `emit_op ADD _ st2 = (key_ptr, st3)` >>
  rename1 `emit_void MSTORE [key_ptr; key_op] st3 = ((), st4)` >>
  drule compile_alloc_buffer_mem_ok >>
  disch_then (qspecl_then [`s`, `p`] mp_tac) >>
  impl_tac >- fs[dimword_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK s1` >>
  `STRING #"%" (toString st.cs_next_var) NOTIN FDOM s.vs_vars` by
    (irule fresh_vars_wrt_next >> qexists_tac `st` >> fs[]) >>
  `STRING #"%" (toString (st.cs_next_var + 1)) NOTIN FDOM s1.vs_vars` by
    (irule fresh_vars_wrt_next >> qexists_tac `st1` >> fs[]) >>
  qpat_x_assum `emit_void MSTORE [_; base_slot] st1 = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_x_assum `emit_op ADD _ st2 = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `emit_void MSTORE [_; key_op] st3 = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_x_assum `emit_op SHA3 _ st4 = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  gvs[run_inst_seq_mem_ok_last] >>
  qabbrev_tac `x = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `y = STRING #"%" (toString (st.cs_next_var + 1))` >>
  `p < dimword (:256) /\ p + 32 < dimword (:256)` by decide_tac >>
  `w2n (n2w p : bytes32) = p` by simp[LESS_MOD] >>
  `w2n (n2w (p + 32) : bytes32) = p + 32` by simp[LESS_MOD] >>
  (* s1: after the ALLOCA *)
  `p + 64 <= s1.vs_alloca_next` by simp[Abbr `s1`] >>
  `eval_operand (Var x) s1 = SOME (n2w p)` by
    simp[Abbr `s1`, eval_operand_update_var] >>
  `eval_operand base_slot s1 = SOME b /\ eval_operand key_op s1 = SOME k` by
    (simp[Abbr `s1`] >> conj_tac >> irule eval_operand_update_unbound >>
     fs[]) >>
  (* s2: after MSTORE [buf; slot] *)
  qabbrev_tac `s2 = mstore p b s1` >>
  `!id. step_inst_base (mk_inst id MSTORE [Var x; base_slot] []) s1 = OK s2 /\
        inst_mem_below_frontier (mk_inst id MSTORE [Var x; base_slot] []) s1` by
    (gen_tac >> simp[Abbr `s2`] >> irule scratch_mstore_mem_ok >> simp[]) >>
  `s2.vs_alloca_next = s1.vs_alloca_next /\ s2.vs_vars = s1.vs_vars /\
   eval_operand (Var x) s2 = SOME (n2w p) /\
   eval_operand key_op s2 = SOME k` by simp[Abbr `s2`] >>
  (* s3: after ADD [buf; 32] *)
  qabbrev_tac `s3 = update_var y (n2w (p + 32)) s2` >>
  `!id. step_inst_base (mk_inst id ADD [Var x; Lit 32w] [y]) s2 = OK s3` by
    (gen_tac >>
     qspecl_then [`Var x`, `Lit 32w`, `n2w p`, `32w`, `id`, `y`, `s2`]
       mp_tac step_ADD >>
     gs[Abbr `s3`, eval_operand_lit, word_add_n2w]) >>
  `!id. inst_mem_below_frontier (mk_inst id ADD [Var x; Lit 32w] [y]) s2` by
    (gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `s3.vs_alloca_next = s1.vs_alloca_next /\
   eval_operand (Var y) s3 = SOME (n2w (p + 32)) /\
   eval_operand (Var x) s3 = SOME (n2w p) /\
   eval_operand key_op s3 = SOME k` by
    (simp[Abbr `s3`, eval_operand_update_var] >> conj_tac >>
     irule eval_operand_update_unbound >> fs[]) >>
  (* s4: after MSTORE [buf + 32; key] *)
  qabbrev_tac `s4 = mstore (p + 32) k s3` >>
  `!id. step_inst_base (mk_inst id MSTORE [Var y; key_op] []) s3 = OK s4 /\
        inst_mem_below_frontier (mk_inst id MSTORE [Var y; key_op] []) s3` by
    (gen_tac >> simp[Abbr `s4`] >> irule scratch_mstore_mem_ok >> simp[]) >>
  `s4.vs_alloca_next = s1.vs_alloca_next /\
   eval_operand (Var x) s4 = SOME (n2w p)` by simp[Abbr `s4`] >>
  `!id out. inst_mem_below_frontier (mk_inst id SHA3 [Var x; Lit 64w] out) s4` by
    (simp[below_frontier_SHA3, eval_operand_lit] >> rpt strip_tac >>
     gvs[dimword_def]) >>
  qspecl_then [`st`, `st1`, `st2`, `st3`, `st4`, `st'`] mp_tac
    emitted_insts_five >>
  gs[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last]
QED

(* ===== Local variable pointers ===== *)

Theorem local_ptr_below_frontier:
  !func cenv scopes ss name entry p sz.
    local_ptrs_rel func cenv scopes ss /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ?w. lookup_var p ss = SOME w /\ w2n w + sz <= ss.vs_alloca_next
Proof
  rw[local_ptrs_rel_def] >> res_tac >> metis_tac[]
QED

(* A field at offset off of size len inside a region of size sz *)
Theorem local_ptr_field_below_frontier:
  !w sz off len next.
    w2n w + sz <= next /\ off + len <= sz ==>
    w2n (w + n2w off) + len <= next
Proof
  rpt strip_tac >>
  `w2n (w + n2w off) <= w2n w + w2n (n2w off : 'a word)` by
    simp[word_add_le] >>
  `w2n (n2w off : 'a word) <= off` by simp[MOD_LESS_EQ] >>
  decide_tac
QED
