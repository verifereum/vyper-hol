(* Pointer-safe body judgments: the ptr twins of S1's expression and
 * statement simulations (exprSim, stmtSim, bodySim).  A run is
 * pointer-safe when ptrSafeRun's ptr_safe_run holds of it, with the ghost
 * provenance G and taint tn threaded as frame_reachable threads them.
 *
 * The judgments take the dead bytes D and the bound lo the check runs
 * under (ptrSafeRun's ptr_safe_run D lo): a runtime frame's are
 * (cx_dead cx, 0), a constructor's (deploy's dead bytes, imm_len tops),
 * whose immutables fixed region [0, imm_len) the lowering addresses by
 * literal offsets.  dead_lo_ok ties D and lo to the frame.
 *
 * TOP-LEVEL:
 *   dead_sub, dead_lo_ok -- D holds cx's dead bytes, lo is the frame's
 *   ghost_inv_at, ghost_kept_at -- what the ghost owes the source state
 *     at a statement boundary, and what an expression's run keeps
 *   frag_exec_ptr_at -- frag_exec with the ghost and pointer safety, for
 *     fixed runs
 *   expr_sim_ptr_at, expr_vv_sim_ptr_at, stmt_frag_ptr_at,
 *     frame_ret_ok_ptr_at -- the twins of expr_sim, expr_vv_sim,
 *     stmt_frag, frame_ret_ok, as counted paths (fragGasPathPtr's
 *     gas_outcome_ptr_lo)
 *   ghost_inv, ghost_kept, frag_exec_ptr, expr_sim_ptr, expr_vv_sim_ptr,
 *     stmt_frag_ptr, frame_ret_ok_ptr -- their runtime instances at
 *     (cx_dead cx, 0) with ~cenv.ce_is_ctor; their _def theorems state
 *     them as they read before the generalization
 *)
Theory bodyPtrDefs
Ancestors
  fragGasPathPtr gasContext bodySim immSectionDead stmtSimDefs stmtSimProps exprSimDefs exprSimProps exprSimHyps fragExec ptrSafeRun ptrDiscipline
  compileEnv valueEncoding exprLowering exprLoweringProps context
  venomState venomExecSemantics vyperInterpreter vyperTypeSystem list
  finite_map words

(* The dead bytes the body's run may leave taint in: those storage_dead
   gives in the running contract's storage and transient storage, as
   external_call_dead does for the source call that cx is the context of.
   The return data may hold no taint. *)
Definition cx_dead_def:
  cx_dead cx =
    <| d_stor := (\a st. if a = cx.txn.target
                         then {(k,b) | storage_dead cx F st (w2n k) b}
                         else {});
       d_trans := (\a st. if a = cx.txn.target
                          then {(k,b) | storage_dead cx T st (w2n k) b}
                          else {});
       d_imm := K {}; d_ret := K {} |>
End

(* D holds every dead byte D0 does. *)
Definition dead_sub_def:
  dead_sub (D0 : dead) (D : dead) <=>
    (!a st. D0.d_stor a st SUBSET D.d_stor a st) /\
    (!a st. D0.d_trans a st SUBSET D.d_trans a st) /\
    (!im. D0.d_imm im SUBSET D.d_imm im) /\
    (!r. D0.d_ret r SUBSET D.d_ret r)
End

Theorem dead_sub_refl[simp]:
  dead_sub D D
Proof
  simp[dead_sub_def]
QED

(* The dead bytes and the bound a frame's run is checked under: D holds
   cx's dead storage bytes, and lo is the constructor's immutables fixed
   region, which its code addresses by literal offsets, or 0 in a runtime
   frame, where every access is checked. *)
Definition dead_lo_ok_def:
  dead_lo_ok D lo cenv cx <=>
    dead_sub (cx_dead cx) D /\
    (cenv.ce_is_ctor ==> !im. D.d_imm im = UNIV) /\
    lo = (if cenv.ce_is_ctor then imm_len (cx_tops cx) else 0)
End

(* Two memories agree on every byte outside m. *)
Definition mem_agree_outside_def:
  mem_agree_outside m (mem1 : byte list) mem2 <=>
    !i. i NOTIN m ==> mem_bytes_at i 1 mem1 = mem_bytes_at i 1 mem2
End

(* p is untainted and points at w inside the site G gives it, with sz bytes
   from w inside the site. *)
Definition ptr_covers_def:
  ptr_covers G tn p (s : venom_state) sz <=>
    op_taint tn (Var p) = {} /\
    ?w b sz'. lookup_var p s = SOME w /\ FLOOKUP G p = SOME (b, sz') /\
              b <= w2n w /\ w2n w + sz <= b + sz'
End

(* The caller's return buffer, if any (d: its address and capacity), is
   covered. *)
Definition return_buf_ptr_def:
  (return_buf_ptr NONE (cenv : compile_env) G tn (s : venom_state) <=> T) /\
  (return_buf_ptr (SOME (bw : bytes32, capacity)) cenv G tn s <=>
     ?x slot_size.
       cenv.ce_return_buf = SOME (PtrVar (Var x) slot_size) /\
       lookup_var x s = SOME bw /\ ptr_covers G tn x s capacity)
End

(* Storage, transient storage and the immutables hold taint only in D's
   dead bytes, as ptrSafeRun's ptr_inst_ok checks them at a request or a
   halt. *)
Definition stor_taint_ok_at_def:
  stor_taint_ok_at (D : dead) tn (s : venom_state) <=>
    tn.t_stor SUBSET
      D.d_stor s.vs_call_ctx.cc_address
        (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET
      D.d_trans s.vs_call_ctx.cc_address
        (s.vs_transient s.vs_call_ctx.cc_address) /\
    tn.t_imm SUBSET D.d_imm s.vs_immutables
End

(* The runtime instance: cx's dead storage bytes, and no immutable tainted. *)
Definition stor_taint_ok_cx_dead:
  stor_taint_ok cx tn s <=> stor_taint_ok_at (cx_dead cx) tn s
End

Theorem stor_taint_ok_def:
  stor_taint_ok cx tn (s : venom_state) <=>
    tn.t_stor SUBSET
      (cx_dead cx).d_stor s.vs_call_ctx.cc_address
        (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET
      (cx_dead cx).d_trans s.vs_call_ctx.cc_address
        (s.vs_transient s.vs_call_ctx.cc_address) /\
    tn.t_imm = {}
Proof
  simp[stor_taint_ok_cx_dead, stor_taint_ok_at_def, cx_dead_def]
QED

(* At a statement boundary: each live local's pointer is covered for the
   local's region, and the local's value is in memory whatever its tainted
   bytes hold; the return buffer is covered; the return PC is untainted;
   storage is tainted only in D's dead bytes; the fixed region [0, lo) is
   tainted only on the bytes the immutables section leaves dead; its base
   variable, when there is one, is untainted and no pointer; and every
   ALLOCA site, and the frontier, is at or above lo. *)
Definition ghost_inv_at_def:
  ghost_inv_at D lo d cenv cx (es : evaluation_state) G tn
    (s : venom_state) <=>
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
               mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory entry.type entry.value (w2n w) mem) /\
    return_buf_ptr d cenv G tn s /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            op_taint tn (Var x) = {}) /\
    stor_taint_ok_at D tn s /\
    (!i. i < lo /\ i IN tn.t_mem ==>
         imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) i) /\
    (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
         FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next
End

Definition ghost_inv_cx_dead:
  ghost_inv d cenv cx es G tn s <=>
    ghost_inv_at (cx_dead cx) 0 d cenv cx es G tn s
End

Theorem ghost_inv_def:
  ghost_inv d cenv cx (es : evaluation_state) G tn (s : venom_state) <=>
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
               mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory entry.type entry.value (w2n w) mem) /\
    return_buf_ptr d cenv G tn s /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            op_taint tn (Var x) = {}) /\
    stor_taint_ok cx tn s
Proof
  simp[ghost_inv_cx_dead, ghost_inv_at_def, stor_taint_ok_cx_dead,
       allocas_from_def]
QED

(* Variables older than sa keep their provenance and taint; the bytes of
   the frame's older allocations outside live locals (those expr_post
   keeps) gain no taint, and nor do the live locals' bytes that
   locals_kept keeps (all but the length words of the dynamic arrays
   inside them), nor does the fixed region [0, lo). *)
Definition ghost_kept_at_def:
  ghost_kept_at lo cenv (es : evaluation_state) (sa : compile_state) G0 tn0
    (s0 : venom_state) G tn <=>
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem) /\
    (!n b sz i.
       local_region cenv es.scopes s0 n b sz /\
       b <= i /\ i < b + sz /\
       (!k. dynarray_len_at cenv n k ==> i < b + k \/ b + k + 32 <= i) /\
       i IN tn.t_mem ==>
       i IN tn0.t_mem) /\
    (!i. i < lo /\ i IN tn.t_mem ==> i IN tn0.t_mem)
End

Definition ghost_kept_zero:
  ghost_kept cenv es sa G0 tn0 s0 G tn <=>
    ghost_kept_at 0 cenv es sa G0 tn0 s0 G tn
End

Theorem ghost_kept_def:
  ghost_kept cenv (es : evaluation_state) (sa : compile_state) G0 tn0
    (s0 : venom_state) G tn <=>
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem) /\
    (!n b sz i.
       local_region cenv es.scopes s0 n b sz /\
       b <= i /\ i < b + sz /\
       (!k. dynarray_len_at cenv n k ==> i < b + k \/ b + k + 32 <= i) /\
       i IN tn.t_mem ==>
       i IN tn0.t_mem)
Proof
  simp[ghost_kept_zero, ghost_kept_at_def]
QED

(* v of type t is in memory at op's address whatever the tainted bytes
   hold, and op's pointer is covered for its word-padded footprint,
   val_store_size: copies of a bytestring read whole words. *)
Definition ptr_mem_ok_def:
  ptr_mem_ok cx t v op G tn (s : venom_state) <=>
    !tv w. evaluate_type (get_tenv cx) t = SOME tv /\
           eval_operand op s = SOME w ==>
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                  val_in_memory tv v (w2n w) mem) /\
           (val_footprint tv v <> 0 ==>
            ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b, sz) /\
                     b <= w2n w /\ w2n w + val_store_size tv v <= b + sz)
End

(* A lowered value op of type t holding v is untainted, a word value's
   carries no provenance (so access_ok's comparisons can pair it with any
   other clean word), and a memory value's is ptr_mem_ok. *)
Definition ptr_val_ok_def:
  ptr_val_ok cx t v op G tn (s : venom_state) <=>
    op_taint tn op = {} /\
    (is_word_type t ==> op_prov G op = NONE) /\
    (~is_word_type t ==> ptr_mem_ok cx t v op G tn s)
End

Theorem ptr_val_ok_word:
  is_word_type t /\ op_taint tn op = {} /\ op_prov G op = NONE ==>
  ptr_val_ok cx t v op G tn s
Proof
  simp[ptr_val_ok_def]
QED

Theorem op_prov_lit[simp]:
  op_prov G (Lit w) = NONE
Proof
  simp[op_prov_def]
QED

Theorem first_prov_eq_none:
  first_prov G ops = NONE <=> EVERY (\op. op_prov G op = NONE) ops
Proof
  Induct_on `ops` >> simp[first_prov_def] >> rpt strip_tac >>
  CASE_TAC >> simp[]
QED

(* An output of a step whose out_prov is NONE has no provenance after it. *)
Theorem step_prov_out_none:
  MEM out inst.inst_outputs /\ out_prov PG G inst s' = NONE ==>
  op_prov (step_prov PG G inst s') (Var out) = NONE
Proof
  rw[step_prov_def, set_prov_def, op_prov_def] >>
  rpt CASE_TAC >> gvs[FLOOKUP_DRESTRICT]
QED

(* ADD, SUB and ASSIGN of operands with no provenance give none. *)
Theorem out_prov_arith_none:
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
   inst.inst_opcode = ASSIGN) /\
  EVERY (\op. op_prov G op = NONE) inst.inst_operands ==>
  out_prov PG G inst s' = NONE
Proof
  rw[out_prov_def, first_prov_eq_none]
QED

(* Every other opcode but ALLOCA, DALLOCA and PARAM gives none. *)
Theorem out_prov_other_none:
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM /\ inst.inst_opcode <> ADD /\
  inst.inst_opcode <> SUB /\ inst.inst_opcode <> ASSIGN ==>
  out_prov PG G inst s' = NONE
Proof
  rw[out_prov_def]
QED

(* ptr_val_ok for compile_expr's value_vv: a stack value as ptr_val_ok, a
   located one's pointer untainted, a memory place, of any type,
   ptr_mem_ok, and a storage or transient place tainted only in the bytes
   its own type leaves dead (a popped element's slots are dead after the
   pop's length store, so this is stated over the taint, not liveness). *)
Definition ptr_vv_ok_def:
  (ptr_vv_ok cx t tv (StackValue t' op) es G tn s <=>
     ?v. read_result cx tv es = (INL v, es) /\
         ptr_val_ok cx t v op G tn s) /\
  (ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s <=>
     op_taint tn p.ptr_operand = {} /\
     (p.ptr_location = LocCode ==> op_prov G p.ptr_operand = NONE) /\
     (p.ptr_location = LocMemory ==>
      ?v. read_result cx tv es = (INL v, es) /\
          ptr_mem_ok cx t v p.ptr_operand G tn s) /\
     (!w ty k b.
        eval_operand p.ptr_operand s = SOME w /\
        evaluate_type (get_tenv cx) t = SOME ty /\
        w2n w <= w2n k /\ w2n k < w2n w + type_slot_size ty /\ b < 32 ==>
        (p.ptr_location = LocStorage /\ (k, b) IN tn.t_stor ==>
         dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage
           (w2n w) ty (w2n k) b) /\
        (p.ptr_location = LocTransient /\ (k, b) IN tn.t_trans ==>
         dead_bytes (s.vs_transient s.vs_call_ctx.cc_address)
           (w2n w) ty (w2n k) b)))
End

(* A memory value's pointer is covered for the whole buffer of e's lowered
   type, not just the value's footprint: compile_assign_value's
   memory-to-memory staging and its bytestring copies to storage read
   type_memory_bytes of the source's lowered type. *)
Definition ptr_buf_ok_def:
  ptr_buf_ok cenv e op G (s : venom_state) <=>
    !w. eval_operand op s = SOME w /\
        type_memory_bytes cenv (lowered_value_type cenv e) <> 0 ==>
        ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b, sz) /\
                 b <= w2n w /\
                 w2n w + type_memory_bytes cenv (lowered_value_type cenv e)
                   <= b + sz
End

(* frag_exec with the ghost: P, Q over the ghost and the state.  The
   continuing case carries the ghost along the run (ghost_run from s
   reaches what it reaches from s') and pointer safety back to s; an exit
   is pointer-safe from s, and R sees the ghost where the run stops. *)
Definition frag_exec_ptr_at_def:
  frag_exec_ptr_at D lo ctx PG (st : compile_state) (st' : compile_state)
    P Q R <=>
    !fn G tn s.
      fn_has_code st st' fn /\ ~ctx_has_dalloca ctx /\ P G tn s /\
      ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      (?G' tn' s'.
         Q G' tn' s' /\ ~s'.vs_halted /\
         s'.vs_current_bb = st'.cs_current_bb /\
         s'.vs_inst_idx = LENGTH st'.cs_current_insts /\
         !fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
           ?fuel'. run_from fuel' ctx fn s = r /\
             ghost_run fuel' ctx fn PG G tn s =
               ghost_run fuel ctx fn PG G' tn' s' /\
             (ptr_safe_run D lo fuel ctx fn PG G' tn' s' ==>
              ptr_safe_run D lo fuel' ctx fn PG G tn s)) \/
      (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
                R (ghost_run fuel ctx fn PG G tn s) r /\
                ptr_safe_run D lo fuel ctx fn PG G tn s)
End

Definition frag_exec_ptr_cx_dead:
  frag_exec_ptr cx ctx PG st st' P Q R <=>
    frag_exec_ptr_at (cx_dead cx) 0 ctx PG st st' P Q R
End

Theorem frag_exec_ptr_def:
  frag_exec_ptr cx ctx PG (st : compile_state) (st' : compile_state) P Q R <=>
    !fn G tn s.
      fn_has_code st st' fn /\ ~ctx_has_dalloca ctx /\ P G tn s /\
      ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      (?G' tn' s'.
         Q G' tn' s' /\ ~s'.vs_halted /\
         s'.vs_current_bb = st'.cs_current_bb /\
         s'.vs_inst_idx = LENGTH st'.cs_current_insts /\
         !fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
           ?fuel'. run_from fuel' ctx fn s = r /\
             ghost_run fuel' ctx fn PG G tn s =
               ghost_run fuel ctx fn PG G' tn' s' /\
             (ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G' tn' s' ==>
              ptr_safe_run (cx_dead cx) 0 fuel' ctx fn PG G tn s)) \/
      (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
                R (ghost_run fuel ctx fn PG G tn s) r /\
                ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s)
Proof
  simp[frag_exec_ptr_cx_dead, frag_exec_ptr_at_def]
QED

(* expr_sim with the ghost: the ghost invariant at s0 gives a pointer-safe
   counted path whose post keeps the invariant, with the value's pointer
   covered, and leaves older variables' ghost alone.  The return buffer's
   and return PC's variables, which ghost_inv reads, are older than sa, so
   the fragment's fresh variables don't clobber them.  The runtime
   instances (expr_sim_ptr and the others) assume ~cenv.ce_is_ctor: a
   constructor's immutable region is read and written through fixed
   addresses, which only the (D, lo) judgments check. *)
Definition expr_sim_ptr_at_def:
  expr_sim_ptr_at D lo d ctx PG func cenv cx ty e es <=>
    !sa sb op s0 G0 tn0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      dead_lo_ok D lo cenv cx /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr_lo D lo (cx_tops cx) (ctx, func) PG
        (bind (eval_expr cx e) (read_result cx)) (es, s0, G0, tn0)
        (\res ee G tn t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv_at D lo d cenv cx ee G tn t /\
          ptr_val_ok cx (expr_type e) v op G tn t /\
          (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

Definition expr_sim_ptr_cx_dead:
  expr_sim_ptr d ctx PG func cenv cx ty e es <=>
    ~cenv.ce_is_ctor ==>
    expr_sim_ptr_at (cx_dead cx) 0 d ctx PG func cenv cx ty e es
End

Theorem expr_sim_ptr_def:
  expr_sim_ptr d ctx PG func cenv cx ty e es <=>
    !sa sb op s0 G0 tn0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      ~cenv.ce_is_ctor /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
        (bind (eval_expr cx e) (read_result cx)) (es, s0, G0, tn0)
        (\res ee G tn t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv d cenv cx ee G tn t /\
          ptr_val_ok cx (expr_type e) v op G tn t /\
          (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
Proof
  simp[expr_sim_ptr_cx_dead, expr_sim_ptr_at_def, dead_lo_ok_def, ghost_inv_cx_dead,
       ghost_kept_zero, gas_outcome_ptr_zero] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
QED

Definition expr_vv_sim_ptr_at_def:
  expr_vv_sim_ptr_at D lo d ctx PG func cenv cx ty e es <=>
    !sa sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      dead_lo_ok D lo cenv cx /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr_lo D lo (cx_tops cx) (ctx, func) PG
        (eval_expr cx e) (es, s0, G0, tn0)
        (\res ee G tn t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv_at D lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
          (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

Definition expr_vv_sim_ptr_cx_dead:
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es <=>
    ~cenv.ce_is_ctor ==>
    expr_vv_sim_ptr_at (cx_dead cx) 0 d ctx PG func cenv cx ty e es
End

Theorem expr_vv_sim_ptr_def:
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es <=>
    !sa sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      ~cenv.ce_is_ctor /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
        (eval_expr cx e) (es, s0, G0, tn0)
        (\res ee G tn t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv d cenv cx ee G tn t /\
          ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
          (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
Proof
  simp[expr_vv_sim_ptr_cx_dead, expr_vv_sim_ptr_at_def, dead_lo_ok_def, ghost_inv_cx_dead,
       ghost_kept_zero, gas_outcome_ptr_zero] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
QED

(* stmt_exit with the ghost where the run stops: a return's RetQ sees it,
   so an internal frame can say what its caller gets back. *)
Definition stmt_exit_ptr_def:
  stmt_exit_ptr RetQ es' (res : unit + exception) gt r <=>
    expr_exit res r \/
    ?v. res = INR (ReturnException v) /\
        RetQ v (es' with scopes := []) gt r
End

Definition stmt_frag_ptr_at_def:
  stmt_frag_ptr_at D lo d ctx PG func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 G0 tn0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr_lo D lo (cx_tops cx) (ctx, func) PG source
        (es, s0, G0, tn0)
        (\res ee G tn t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel ctx func cenv'' cx ee t /\
          ghost_inv_at D lo d cenv'' cx ee G tn t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G x = FLOOKUP G0 x /\
               op_taint tn (Var x) = op_taint tn0 (Var x)))
        (\res ee gt r.
          !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
End

Definition stmt_frag_ptr_cx_dead:
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    ~cenv.ce_is_ctor ==>
    stmt_frag_ptr_at (cx_dead cx) 0 d ctx PG func cx lctx RetQ cenv m source es
End

Theorem stmt_frag_ptr_def:
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 G0 tn0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG source
        (es, s0, G0, tn0)
        (\res ee G tn t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel ctx func cenv'' cx ee t /\
          ghost_inv d cenv'' cx ee G tn t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G x = FLOOKUP G0 x /\
               op_taint tn (Var x) = op_taint tn0 (Var x)))
        (\res ee gt r.
          !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  simp[stmt_frag_ptr_cx_dead, stmt_frag_ptr_at_def, dead_lo_ok_def, ghost_inv_cx_dead,
       ghost_kept_zero, gas_outcome_ptr_zero] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
QED

Definition frame_ret_ok_ptr_at_def:
  frame_ret_ok_ptr_at D lo d ctx PG func cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_ptr_at D lo d ctx PG func cenv' cx ty e es /\
              expr_vv_sim_ptr_at D lo d ctx PG func cenv' cx ty e es) ==>
      stmt_frag_ptr_at D lo d ctx PG func cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
End

Definition frame_ret_ok_ptr_cx_dead:
  frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty <=>
    ~cenv.ce_is_ctor ==>
    frame_ret_ok_ptr_at (cx_dead cx) 0 d ctx PG func cx RetQ cenv ret_ty
End

Theorem same_frame_is_ctor:
  same_frame cenv cenv' ==> (cenv'.ce_is_ctor <=> cenv.ce_is_ctor)
Proof
  rw[same_frame_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem frame_ret_ok_ptr_def:
  frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_ptr d ctx PG func cenv' cx ty e es /\
              expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) ==>
      stmt_frag_ptr d ctx PG func cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
Proof
  simp[frame_ret_ok_ptr_cx_dead, frame_ret_ok_ptr_at_def] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
  >- (rpt strip_tac >>
      `cenv'.ce_is_ctor` by metis_tac[same_frame_is_ctor] >>
      simp[stmt_frag_ptr_cx_dead]) >>
  eq_tac >> rpt strip_tac >>
  `~cenv'.ce_is_ctor` by metis_tac[same_frame_is_ctor] >>
  first_x_assum (qspecl_then [`cenv'`, `env`, `lctx`, `eo`, `es`] mp_tac) >>
  fs[stmt_frag_ptr_cx_dead, expr_sim_ptr_cx_dead, expr_vv_sim_ptr_cx_dead]
QED
