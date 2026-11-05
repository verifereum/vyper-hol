(*
 * Expression simulation: copying a value out of storage or transient
 * storage into memory is defined (#637)
 *
 * compile_ensure_in_memory, for a pointer into storage or transient
 * storage, allocates a buffer and copies the value's words into it: an
 * SLOAD or TLOAD and an MSTORE for one word, compile_word_copy_loop
 * otherwise.  Every instruction it emits runs with defined operands and
 * the loop's counter runs from 0 until it equals n2w word_count, so the
 * copy ends at the start of its exit block with the buffer's operand
 * defined and the variables handed out before it unchanged, whatever
 * storage holds.  The content boundary additionally records the exact
 * copied words, a frozen non-memory state projection, and preservation
 * of bytes outside the destination buffer, under no-wrap bounds.
 *
 * TOP-LEVEL:
 *   compile_storage_copy_content_capacity_frag — loop contents and full frame
 *   storage_copy_suffix_content_frag  — uniform zero/one/many-word copy
 *   storage_copy_operand_preserved    — recover framed operand values
 *   compile_storage_copy_defined_frag  — the copy loop runs to its exit
 *   ensure_storage_memory_layout       — compile_ensure_in_memory's code
 *                                        for storage and transient storage
 *   ensure_storage_memory_defined_frag — that code runs with its result
 *                                        operand defined
 *   storage_copy_alloc_layout          — compile_alloc_buffer's code
 *
 * Helper: storage_copy_frame, the frame the loop invariant keeps, and the
 *   layout, step and loop lemmas for the copy's blocks.
 *)

Theory exprSimStorageCopy
Ancestors
  list rich_list finite_map pred_set valueEncodingProps
  fragExec localPtrsProps  loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* Storage copies use slot offsets at the source and byte offsets at the
   destination.  Keep the location dispatch outside the loop proofs. *)
Theorem compile_storage_copy_layout[local]:
  !loc src dst n.
    (loc = LocStorage \/ loc = LocTransient) ==>
    compile_word_copy_loop src dst n loc LocMemory F =
    do
      hdr <- fresh_label "wcopy_cond";
      body <- fresh_label "wcopy_body";
      exit <- fresh_label "wcopy_exit";
      counter <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [counter];
      emit_inst JMP [Label hdr] [];
      new_block hdr;
      done_op <- emit_op EQ [Var counter; Lit (n2w n)];
      emit_inst JNZ [done_op; Label exit; Label body] [];
      new_block body;
      src_off <- emit_op ADD [src; Var counter];
      value <- compile_ptr_load F NONE loc src_off;
      dst_off <- (do
        scaled <- emit_op MUL [Var counter; Lit 32w];
        emit_op ADD [dst; scaled]
      od);
      emit_void MSTORE [dst_off; value];
      next <- emit_op ADD [Var counter; Lit 1w];
      emit_inst ASSIGN [next] [counter];
      emit_inst JMP [Label hdr] [];
      new_block exit
    od
Proof
  cheat
QED

Theorem compile_storage_copy_appends[local]:
  !loc src dst n.
    (loc = LocStorage \/ loc = LocTransient) ==>
    cs_appends (compile_word_copy_loop src dst n loc LocMemory F)
Proof
  cheat
QED

Theorem compile_storage_copy_extends[local]:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u, sb) ==>
    cs_extends sa sb
Proof
  cheat
QED

(* Expose compiler boundaries without expanding compile_state records. *)
Theorem storage_copy_bind_eq:
  comp_bind m f s = (u,t) <=>
  ?v s1. m s = (v,s1) /\ f v s1 = (u,t)
Proof
  cheat
QED

Theorem compile_storage_copy_boundaries[local]:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) ==>
    ?hdr body exit cv test so value scaled dest next old0 oldh
     s1 s2 s3 s4 s0 sj sth stj st2 stb s5 s6 s7 s8 s9 s10 ste st3.
      fresh_label "wcopy_cond" sa = (hdr,s1) /\
      fresh_label "wcopy_body" s1 = (body,s2) /\
      fresh_label "wcopy_exit" s2 = (exit,s3) /\
      fresh_var s3 = (cv,s4) /\
      emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) /\
      emit_inst JNZ [test; Label exit; Label body] [] stj = ((),st2) /\
      new_block body st2 = (oldh,stb) /\
      emit_op ADD [src; Var cv] stb = (so,s5) /\
      compile_ptr_load F NONE loc so s5 = (value,s6) /\
      emit_op MUL [Var cv; Lit 32w] s6 = (scaled,s7) /\
      emit_op ADD [dst; scaled] s7 = (dest,s8) /\
      emit_void MSTORE [dest; value] s8 = ((),s9) /\
      emit_op ADD [Var cv; Lit 1w] s9 = (next,s10) /\
      emit_inst ASSIGN [next] [cv] s10 = ((),ste) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb)
Proof
  cheat
QED

Theorem storage_copy_body_layout[local]:
  !loc src dst cv so value scaled dest next stb s1 s2 s3 s4 s5 s6 ste.
    (loc = LocStorage \/ loc = LocTransient) /\
    emit_op ADD [src; Var cv] stb = (so,s1) /\
    compile_ptr_load F NONE loc so s1 = (value,s2) /\
    emit_op MUL [Var cv; Lit 32w] s2 = (scaled,s3) /\
    emit_op ADD [dst; scaled] s3 = (dest,s4) /\
    emit_void MSTORE [dest; value] s4 = ((),s5) /\
    emit_op ADD [Var cv; Lit 1w] s5 = (next,s6) /\
    emit_inst ASSIGN [next] [cv] s6 = ((),ste) ==>
    ?sv vv mv dv nv.
      so = Var sv /\ value = Var vv /\ scaled = Var mv /\
      dest = Var dv /\ next = Var nv /\
      ALL_DISTINCT [sv; vv; mv; dv; nv] /\
      (!x. not_fresh_at stb x ==> ~MEM x [sv; vv; mv; dv; nv]) /\
      same_blocks stb ste /\
      isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      ste.cs_next_var = stb.cs_next_var + 5 /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
        mk_inst (stb.cs_next_id+1)
          (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
        mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]]
Proof
  cheat
QED

Theorem storage_copy_header_layout:
  !cv n sth test stj.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) ==>
    ?tv. test = Var tv /\
      (!x. not_fresh_at sth x ==> x <> tv) /\
      same_blocks sth stj /\
      isPREFIX sth.cs_current_insts stj.cs_current_insts /\
      emitted_insts sth stj =
        [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]]
Proof
  cheat
QED

Theorem storage_copy_init_layout:
  !sa hdr body exit cv tv s1 s2 s3 s4 s0 sj sth stj n old.
    fresh_label "wcopy_cond" sa = (hdr,s1) /\
    fresh_label "wcopy_body" s1 = (body,s2) /\
    fresh_label "wcopy_exit" s2 = (exit,s3) /\
    fresh_var s3 = (cv,s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
    emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
    new_block hdr sj = (old,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) ==>
    cv <> tv /\ same_blocks sa s0 /\
    isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    (!x. not_fresh_at sa x ==> x <> cv /\ x <> tv) /\
    not_fresh_at sth cv
Proof
  cheat
QED

Theorem storage_copy_prefix_freshness:
  !sa hdr body exit cv tv s1 s2 s3 s4 s0 sj sth stj st2 stb n old0 oldh.
    fresh_label "wcopy_cond" sa = (hdr,s1) /\
    fresh_label "wcopy_body" s1 = (body,s2) /\
    fresh_label "wcopy_exit" s2 = (exit,s3) /\
    fresh_var s3 = (cv,s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
    emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
    new_block hdr sj = (old0,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label body] [] stj = ((),st2) /\
    new_block body st2 = (oldh,stb) ==>
    sth.cs_next_var = sa.cs_next_var + 1 /\
    stb.cs_next_var = sa.cs_next_var + 2 /\
    not_fresh_at stb cv /\ not_fresh_at stb tv /\
    (!x. not_fresh_at sa x ==> not_fresh_at stb x)
Proof
  cheat
QED

Theorem compile_storage_copy_certificate:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) ==>
    ?s0 sj sth stj st2 stb ste st3 hdr loop_body exit cv tv sv vv mv dv nv old0 oldh.
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
      emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
      new_block loop_body st2 = (oldh,stb) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb) /\
      same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
      emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
      same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
      emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
      same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
        mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
        mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
      cs_extends sa s0 /\ cs_extends s0 sb /\
      cs_extends sth stj /\ cs_extends stb ste /\
      ALL_DISTINCT [cv;tv;sv;vv;mv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;sv;vv;mv;dv;nv])
Proof
  cheat
QED

(* Freeze every field except registers, memory and execution position. *)
Definition copy_static_def:
  copy_static s = s with <| vs_memory := []; vs_vars := FEMPTY;
    vs_prev_bb := NONE; vs_current_bb := ""; vs_inst_idx := 0 |>
End

Definition copy_runtime_word_def:
  copy_runtime_word loc s a =
    if loc = LocStorage then sload a s else tload a s
End

Theorem copy_static_update_var[local,simp]:
  copy_static (update_var x w s) = copy_static s
Proof
  cheat
QED

Theorem copy_static_jump[local,simp]:
  copy_static (jump_to l s) = copy_static s
Proof
  cheat
QED

Theorem copy_static_idx[local,simp]:
  copy_static (s with vs_inst_idx := i) = copy_static s
Proof
  cheat
QED

Theorem copy_static_mstore:
  copy_static (mstore b w s) = copy_static s
Proof
  cheat
QED

val _ = augment_srw_ss [rewrites [copy_static_mstore]];

Theorem copy_static_fields:
  copy_static s = copy_static t ==>
  s.vs_accounts = t.vs_accounts /\
  s.vs_transient = t.vs_transient /\
  s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_allocas = t.vs_allocas /\
  s.vs_alloca_next = t.vs_alloca_next /\
  s.vs_labels = t.vs_labels /\
  s.vs_halted = t.vs_halted /\
  s.vs_data_section = t.vs_data_section
Proof
  cheat
QED

Theorem copy_runtime_word_static:
  copy_static s = copy_static t ==>
  copy_runtime_word loc s a = copy_runtime_word loc t a
Proof
  cheat
QED

(* Memory observations include zero-extended bytes outside the buffer. *)
Definition copy_prefix_def:
  copy_prefix loc a b n sbase k s <=>
    k <= n /\ copy_static s = copy_static sbase /\
    (!i. i < k ==> mem_word_at (b+32*i) s.vs_memory =
       copy_runtime_word loc sbase (a+n2w i)) /\
    (!off len. off+len <= b \/ b+32*n <= off ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory)
End

Theorem copy_prefix_zero:
  copy_prefix loc a b n s 0 s
Proof
  cheat
QED

Theorem copy_prefix_transfer:
  copy_prefix loc a b n sbase k s /\
  copy_static t = copy_static s /\ t.vs_memory = s.vs_memory ==>
  copy_prefix loc a b n sbase k t
Proof
  cheat
QED

Theorem copy_prefix_update_var:
  copy_prefix loc a b n sbase k (update_var x w s) =
  copy_prefix loc a b n sbase k s
Proof
  cheat
QED

val _ = augment_srw_ss [rewrites [copy_prefix_update_var]];

Theorem copy_prefix_jump:
  copy_prefix loc a b n sbase k (jump_to l s) =
  copy_prefix loc a b n sbase k s
Proof
  cheat
QED

val _ = augment_srw_ss [rewrites [copy_prefix_jump]];

Theorem copy_prefix_idx:
  copy_prefix loc a b n sbase k (s with vs_inst_idx := i) =
  copy_prefix loc a b n sbase k s
Proof
  cheat
QED

val _ = augment_srw_ss [rewrites [copy_prefix_idx]];

Theorem copy_prefix_word:
  copy_prefix loc a b n sbase n s /\ i < n ==>
  mem_word_at (b+32*i) s.vs_memory = copy_runtime_word loc sbase (a+n2w i)
Proof
  cheat
QED

Theorem copy_prefix_bytes:
  copy_prefix loc a b n sbase k s /\
  (off+len <= b \/ b+32*n <= off) ==>
  mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory
Proof
  cheat
QED

Theorem copy_prefix_extend:
  copy_prefix loc a b n sbase k s /\ k < n ==>
  copy_prefix loc a b n sbase (k+1)
    (mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) s)
Proof
  cheat
QED

Theorem copy_destination_no_wrap[local]:
  k < n /\ b+32*n < 2**256 ==>
  w2n (n2w b + n2w k * 32w : bytes32) = b+32*k
Proof
  cheat
QED

Theorem storage_copy_load_exact[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand op s = SOME a ==>
  step_inst_base
    (mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [op] [out]) s =
  OK (update_var out (copy_runtime_word loc s a) s)
Proof
  cheat
QED

Theorem storage_copy_store_exact[local]:
  eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME w ==>
  step_inst_base (mk_inst id MSTORE [op1; op2] []) s =
  OK (mstore (w2n a) w s)
Proof
  cheat
QED

(* Both slot spaces are total reads, independent of the stored contents. *)
Theorem storage_copy_load_step[local]:
  !opc op v id out s.
    (opc = SLOAD \/ opc = TLOAD) /\ eval_operand op s = SOME v ==>
    ?t. step_inst_base (mk_inst id opc [op] [out]) s = OK t /\
        (?w. lookup_var out t = SOME w) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\
        t.vs_labels = s.vs_labels
Proof
  cheat
QED

(* An operand depends only on its register (if any) and the label map. *)
Theorem storage_copy_operand_frame:
  !op ds s t w.
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> ~MEM x ds) /\
    (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
    t.vs_labels = s.vs_labels ==>
    eval_operand op t = SOME w
Proof
  cheat
QED

(* The invariant deliberately ignores position and memory. *)
Definition storage_copy_frame_def:
  storage_copy_frame ds sbase s <=>
    (!x. ~MEM x ds ==> lookup_var x s = lookup_var x sbase) /\
    s.vs_labels = sbase.vs_labels
End

Theorem storage_copy_frame_jump[simp]:
  storage_copy_frame ds sbase (jump_to l s) = storage_copy_frame ds sbase s
Proof
  cheat
QED

Theorem storage_copy_frame_idx[simp]:
  storage_copy_frame ds sbase (s with vs_inst_idx := i) =
  storage_copy_frame ds sbase s
Proof
  cheat
QED

Theorem storage_copy_frame_step[local]:
  storage_copy_frame ds sbase s /\
  (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels ==>
  storage_copy_frame ds sbase t
Proof
  cheat
QED

Theorem storage_copy_eq_step[local]:
  !cv tv k n id s.
    eval_operand (Var cv) s = SOME k ==>
    ?t. step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s = OK t /\
        eval_operand (Var tv) t = SOME (bool_to_word (k = n2w n)) /\
        (!x. x <> tv ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_header_frag[local]:
  !ctx cv tv n sth stj ds sbase k R.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    cv <> tv /\ MEM tv ds ==>
    frag_exec ctx sth stj
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s /\
           eval_operand (Var tv) s = SOME (bool_to_word (k = n2w n))) R
Proof
  cheat
QED

Theorem storage_copy_binary_step[local]:
  !opc op1 op2 a b id out s.
    (opc = ADD \/ opc = MUL) /\
    eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b ==>
    ?t. step_inst_base (mk_inst id opc [op1; op2] [out]) s = OK t /\
        eval_operand (Var out) t =
          SOME (if opc = ADD then a + b else a * b) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_assign_step[local]:
  !op w id out s.
    eval_operand op s = SOME w ==>
    ?t. step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK t /\
        eval_operand (Var out) t = SOME w /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_init_frag[local]:
  !ctx sa s0 cv ds sbase R.
    same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    MEM cv ds ==>
    frag_exec ctx sa s0 (\s. s = sbase)
      (\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s) R
Proof
  cheat
QED

Theorem storage_copy_store_step[local]:
  !op1 op2 a b id s.
    eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b ==>
    ?t. step_inst_base (mk_inst id MSTORE [op1; op2] []) s = OK t /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

(* Exact sequence equations complement the register-frame run boundaries. *)
Theorem storage_copy_source_run_effect:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand (Var cv) s = SOME k /\
  (!x. src = Var x ==> x <> sv) ==>
  run_inst_seq
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]] s =
  OK (update_var vv (copy_runtime_word loc s (a+k))
        (update_var sv (a+k) s))
Proof
  cheat
QED

Theorem storage_copy_source_run[local]:
  !opc src a cv sv vv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv] /\
    (!x. src = Var x ==> ~MEM x [sv; vv]) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv]] s = OK t /\
      (?w. eval_operand (Var vv) t = SOME w) /\
      eval_operand (Var cv) t = SOME k /\ eval_operand src t = SOME a /\
      (!x. ~MEM x [sv; vv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_destination_run_effect:
  eval_operand dst s = SOME b /\ eval_operand (Var cv) s = SOME k /\
  eval_operand (Var vv) s = SOME v /\
  vv <> mv /\ vv <> dv /\
  (!x. dst = Var x ==> x <> mv) ==>
  run_inst_seq
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [dst; Var mv] [dv];
     mk_inst (id+2) MSTORE [Var dv; Var vv] []] s =
  OK (mstore (w2n (b+k*32w)) v
        (update_var dv (b+k*32w) (update_var mv (k*32w) s)))
Proof
  cheat
QED

Theorem storage_copy_destination_run[local]:
  !dst b cv vv mv dv id s k v.
    eval_operand dst s = SOME b /\ eval_operand (Var cv) s = SOME k /\
    eval_operand (Var vv) s = SOME v /\
    ALL_DISTINCT [cv; vv; mv; dv] /\
    (!x. dst = Var x ==> ~MEM x [mv; dv]) ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [dst; Var mv] [dv];
       mk_inst (id+2) MSTORE [Var dv; Var vv] []] s = OK t /\
      (!x. ~MEM x [mv; dv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_increment_run_effect:
  eval_operand (Var cv) s = SOME k ==>
  run_inst_seq
    [mk_inst id ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [cv]] s =
  OK (update_var cv (k+1w) (update_var nv (k+1w) s))
Proof
  cheat
QED

Theorem storage_copy_increment_run[local]:
  !cv nv id s k.
    cv <> nv /\ eval_operand (Var cv) s = SOME k ==>
    ?t. run_inst_seq
      [mk_inst id ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k + 1w) /\
      (!x. ~MEM x [cv; nv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem storage_copy_body_run:
  !opc src dst a b cv sv vv mv dv nv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==>
         ~MEM x [cv; sv; vv; mv; dv; nv]) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+3) ADD [dst; Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k + 1w) /\
      eval_operand src t = SOME a /\ eval_operand dst t = SOME b /\
      (!x. ~MEM x [cv; sv; vv; mv; dv; nv] ==>
           lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

(* Exact observations complement the register-frame existence theorem. *)
Theorem storage_copy_body_run_effect:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand (Var cv) s = SOME k /\
  ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
  (!x. src = Var x \/ dst = Var x ==>
       ~MEM x [cv; sv; vv; mv; dv; nv]) /\
  run_inst_seq
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t ==>
  copy_static t = copy_static s /\
  t.vs_memory =
    (mstore (w2n (b+k*32w)) (copy_runtime_word loc s (a+k)) s).vs_memory
Proof
  cheat
QED

Theorem storage_copy_body_prefix:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
  (!x. src = Var x \/ dst = Var x ==>
       ~MEM x [cv; sv; vv; mv; dv; nv]) /\
  run_inst_seq
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
  copy_prefix loc a b n sbase k s /\ k < n /\ b+32*n < 2**256 ==>
  copy_prefix loc a b n sbase (k+1) t
Proof
  cheat
QED

Theorem storage_copy_body_frag[local]:
  !ctx loc src dst cv sv vv mv dv nv stb ste ds sbase a b k R.
    (loc = LocStorage \/ loc = LocTransient) /\
    same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
    emitted_insts stb ste =
      [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
       mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
       mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv; sv; vv; mv; dv; nv]) /\
    (!x. MEM x [cv; sv; vv; mv; dv; nv] ==> MEM x ds) ==>
    frag_exec ctx stb ste
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R
Proof
  cheat
QED

Theorem storage_copy_body_content_frag[local]:
  !ctx loc src dst cv sv vv mv dv nv stb ste ds sbase a b n k R.
    (loc = LocStorage \/ loc = LocTransient) /\
    same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
    emitted_insts stb ste =
      [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
       mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
       mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x ds) /\
    (!x. MEM x [cv; sv; vv; mv; dv; nv] ==> MEM x ds) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    k < n /\ b+32*n < 2**256 ==>
    frag_exec ctx stb ste
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
           copy_prefix loc a b n sbase k s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory)
      (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\ storage_copy_frame ds sbase s /\
           copy_prefix loc a b n sbase (k+1) s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory) R
Proof
  cheat
QED

Theorem storage_copy_body_frame_frag[local]:
  !ctx stb ste src dst a b cv ds sbase k R.
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x ds) /\
    frag_exec ctx stb ste
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R ==>
    frag_exec ctx stb ste
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R
Proof
  cheat
QED

Theorem storage_copy_init_content_frag[local]:
  !ctx sa s0 cv ds sbase loc a b n R.
    same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    MEM cv ds ==>
    frag_exec ctx sa s0 (\s. s = sbase)
      (\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s /\
           copy_prefix loc a b n sbase 0 s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory) R
Proof
  cheat
QED

Theorem storage_copy_header_content_frag[local]:
  !ctx cv tv n sth stj ds sbase loc a b k R.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    cv <> tv /\ MEM tv ds ==>
    frag_exec ctx sth stj
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
           copy_prefix loc a b n sbase k s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory)
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
           copy_prefix loc a b n sbase k s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory /\
           eval_operand (Var tv) s = SOME (bool_to_word (n2w k = n2w n : bytes32))) R
Proof
  cheat
QED

Theorem storage_copy_loop[local]:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr loop_body exit cv tv n
   x0 x1 x2 x3 x4 x5 ds sbase R.
    emit_inst JMP [Label hdr] [] st0 = (x0,st1) /\
    new_block hdr st1 = (x1,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = (x2,st2) /\
    new_block loop_body st2 = (x3,stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4,st3) /\
    new_block exit st3 = (x5,stx) /\
    cs_extends stb ste /\ cv <> tv /\ MEM tv ds /\
    (!k. k < w2n (n2w n : bytes32) ==>
      frag_exec ctx stb ste
        (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s)
        (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\ storage_copy_frame ds sbase s) R) ==>
    frag_exec ctx st0 stx
      (\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME (n2w n) /\ storage_copy_frame ds sbase s /\
           eval_operand (Var tv) s = SOME 1w) R
Proof
  cheat
QED

Definition storage_copy_inv_def:
  storage_copy_inv cv ds loc a b n sbase k s <=>
    eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
    copy_prefix loc a b n sbase k s /\
    LENGTH sbase.vs_memory <= LENGTH s.vs_memory
End

Theorem storage_copy_inv_eta[local]:
  storage_copy_inv cv ds loc a b n sbase k =
    (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
         copy_prefix loc a b n sbase k s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory)
Proof
  cheat
QED

Definition storage_copy_test_def:
  storage_copy_test cv tv ds loc a b n sbase k s <=>
    storage_copy_inv cv ds loc a b n sbase k s /\
    eval_operand (Var tv) s = SOME (bool_to_word (k = n))
End

Theorem storage_copy_content_loop[local]:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr loop_body exit cv tv n
   x0 x1 x2 x3 x4 x5 ds loc a b sbase R.
    emit_inst JMP [Label hdr] [] st0 = (x0,st1) /\
    new_block hdr st1 = (x1,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = (x2,st2) /\
    new_block loop_body st2 = (x3,stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4,st3) /\
    new_block exit st3 = (x5,stx) /\
    cs_extends stb ste /\ cv <> tv /\ MEM tv ds /\ n < 2**256 /\
    (!k. k < n ==> frag_exec ctx stb ste
      (storage_copy_inv cv ds loc a b n sbase k)
      (storage_copy_inv cv ds loc a b n sbase (k+1)) R) ==>
    frag_exec ctx st0 stx
      (storage_copy_inv cv ds loc a b n sbase 0)
      (storage_copy_test cv tv ds loc a b n sbase n) R
Proof
  cheat
QED

Theorem compile_storage_copy_content_capacity_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. copy_prefix loc a b n sbase n s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R
Proof
  cheat
QED

Theorem compile_storage_copy_content_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. copy_prefix loc a b n sbase n s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R
Proof
  cheat
QED

Theorem compile_storage_copy_defined_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

Theorem storage_copy_alloc_layout:
  !n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) ==>
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]] /\
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    sb.cs_next_var = sa.cs_next_var + 1 /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x)
Proof
  cheat
QED

Theorem storage_copy_alloc_frag[local]:
  !ctx n sa buf sb sbase R.
    compile_alloc_buffer n sa = (buf,sb) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand buf.buf_operand s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

Theorem storage_copy_word_layout:
  !opc src dst sa u sb.
    do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) ==>
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id opc [src] [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) MSTORE
         [dst; Var (STRING #"%" (toString sa.cs_next_var))] []] /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var))
Proof
  cheat
QED

Theorem storage_copy_word_frag[local]:
  !ctx opc src dst sa u sb sbase a b R.
    (opc = SLOAD \/ opc = TLOAD) /\
    do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

Theorem storage_copy_word_content_frag[local]:
  !ctx loc src dst sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
       emit_void MSTORE [dst; v] od sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    b+32 < 2**256 ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. copy_prefix loc a b 1 sbase 1 s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R
Proof
  cheat
QED

(* After rewriting ensure_storage_memory_layout, compose the allocation
   boundary and instantiate sbase with its resulting state.  This suffix
   covers zero words too: no positivity hypothesis is used by the loop. *)
Theorem storage_copy_suffix_extends:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (if n = 1 then
       do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (u,sb) ==>
    cs_extends sa sb
Proof
  cheat
QED

Theorem storage_copy_suffix_content_capacity_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    (if n = 1 then
       do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. copy_prefix loc a b n sbase n s /\
           LENGTH sbase.vs_memory <= LENGTH s.vs_memory /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R
Proof
  cheat
QED

Theorem storage_copy_suffix_content_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    (if n = 1 then
       do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. copy_prefix loc a b n sbase n s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R
Proof
  cheat
QED

Theorem storage_copy_operand_preserved:
  copy_static s = copy_static sbase /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) ==>
  eval_operand op s = eval_operand op sbase
Proof
  cheat
QED

Theorem ensure_storage_memory_layout:
  !loc src nb n ctor imm.
    (loc = LocStorage \/ loc = LocTransient) ==>
    compile_ensure_in_memory src loc nb n ctor imm =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
             emit_void MSTORE [buf.buf_operand; v] od
        else do compile_word_copy_loop src buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand
    od
Proof
  cheat
QED

Theorem ensure_storage_memory_defined_frag:
  !ctx loc src nb n ctor imm sa op sb sbase a R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED
