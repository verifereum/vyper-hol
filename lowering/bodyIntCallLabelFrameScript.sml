(* Completed-block tails are inert compiler history. *)
Theory bodyIntCallLabelFrame
Ancestors
  compileEnv emitHelperProps loweringShapeProps context list pred_set

Theorem fresh_label_block_tail:
  fresh_label suffix (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (fresh_label suffix st),
   (SND (fresh_label suffix st)) with
     cs_blocks := (SND (fresh_label suffix st)).cs_blocks ++ tail)
Proof simp[fresh_label_def]
QED

Theorem fresh_var_block_tail:
  fresh_var (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (fresh_var st),
   (SND (fresh_var st)) with
     cs_blocks := (SND (fresh_var st)).cs_blocks ++ tail)
Proof simp[fresh_var_def]
QED

Theorem fresh_id_block_tail:
  fresh_id (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (fresh_id st),
   (SND (fresh_id st)) with
     cs_blocks := (SND (fresh_id st)).cs_blocks ++ tail)
Proof simp[fresh_id_def]
QED

Theorem emit_block_tail:
  emit inst (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (emit inst st),
   (SND (emit inst st)) with
     cs_blocks := (SND (emit inst st)).cs_blocks ++ tail)
Proof simp[emit_def]
QED

Theorem new_block_block_tail:
  new_block lbl (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (new_block lbl st),
   (SND (new_block lbl st)) with
     cs_blocks := (SND (new_block lbl st)).cs_blocks ++ tail)
Proof simp[new_block_def]
QED

Theorem comp_return_block_tail:
  comp_return x (st with cs_blocks := st.cs_blocks ++ tail) =
  (x,st with cs_blocks := st.cs_blocks ++ tail)
Proof simp[comp_return_def]
QED

Theorem comp_bind_block_tail:
  (!st r out. m st = (r,out) ==>
    m (st with cs_blocks := st.cs_blocks ++ tail) =
      (r,out with cs_blocks := out.cs_blocks ++ tail)) /\
  (!x st r out. k x st = (r,out) ==>
    k x (st with cs_blocks := st.cs_blocks ++ tail) =
      (r,out with cs_blocks := out.cs_blocks ++ tail)) ==>
  !st r out. comp_bind m k st = (r,out) ==>
    comp_bind m k (st with cs_blocks := st.cs_blocks ++ tail) =
      (r,out with cs_blocks := out.cs_blocks ++ tail)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m st` >>
  rename1 `m st = (v,mid)` >>
  qpat_x_assum `!st r out. m st = _ ==> _` drule >>
  disch_then (fn th => simp[comp_bind_def, th]) >> strip_tac >>
  qpat_x_assum `!x st r out. k x st = _ ==> _` drule >> simp[]
QED

Theorem new_block_clean_entry_ok:
  new_block label before = (old,entry) /\ ~compiler_label label ==>
  compile_state_ok (entry with cs_blocks := [])
Proof
  simp[new_block_def, compile_state_ok_def, bound_labels_def,
       loweringShapeDefsTheory.compiler_label_def] >> strip_tac >>
  gvs[compiler_labels_future_def] >> metis_tac[DECIDE ``0 <= n``]
QED

Theorem emit_op_block_tail:
  emit_op opc ops (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (emit_op opc ops st),
   (SND (emit_op opc ops st)) with
     cs_blocks := (SND (emit_op opc ops st)).cs_blocks ++ tail)
Proof
  simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def]
QED

Theorem emit_void_block_tail:
  emit_void opc ops (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (emit_void opc ops st),
   (SND (emit_void opc ops st)) with
     cs_blocks := (SND (emit_void opc ops st)).cs_blocks ++ tail)
Proof
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def]
QED

Theorem emit_inst_block_tail:
  emit_inst opc ops outs (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (emit_inst opc ops outs st),
   (SND (emit_inst opc ops outs st)) with
     cs_blocks := (SND (emit_inst opc ops outs st)).cs_blocks ++ tail)
Proof
  simp[emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def]
QED

Theorem comp_bind_block_tail_eq:
  (!st. m (st with cs_blocks := st.cs_blocks ++ tail) =
    (FST (m st), (SND (m st)) with cs_blocks := (SND (m st)).cs_blocks ++ tail)) /\
  (!x st. k x (st with cs_blocks := st.cs_blocks ++ tail) =
    (FST (k x st), (SND (k x st)) with cs_blocks := (SND (k x st)).cs_blocks ++ tail)) ==>
  comp_bind m k (st with cs_blocks := st.cs_blocks ++ tail) =
    (FST (comp_bind m k st), (SND (comp_bind m k st)) with
       cs_blocks := (SND (comp_bind m k st)).cs_blocks ++ tail)
Proof
  strip_tac >> Cases_on `m st` >>
  simp[comp_bind_def] >> pairarg_tac >> simp[]
QED

Theorem compile_ptr_load_block_tail:
  compile_ptr_load ctor imm loc src (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (compile_ptr_load ctor imm loc src st),
   (SND (compile_ptr_load ctor imm loc src st)) with cs_blocks :=
     (SND (compile_ptr_load ctor imm loc src st)).cs_blocks ++ tail)
Proof
  Cases_on `loc` >> Cases_on `imm` >> Cases_on `ctor` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, comp_ignore_bind_def,
       comp_bind_block_tail_eq, emit_op_block_tail, emit_void_block_tail,
       comp_return_def]
QED

Theorem compile_ptr_store_block_tail:
  compile_ptr_store ctor imm loc dst v (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (compile_ptr_store ctor imm loc dst v st),
   (SND (compile_ptr_store ctor imm loc dst v st)) with cs_blocks :=
     (SND (compile_ptr_store ctor imm loc dst v st)).cs_blocks ++ tail)
Proof
  Cases_on `loc` >> Cases_on `imm` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def, comp_ignore_bind_def,
       comp_bind_block_tail_eq, emit_op_block_tail, emit_void_block_tail,
       comp_return_def]
QED


(* Action-level composition avoids expanding compiler executions. *)
Definition compiler_block_tail_def:
  compiler_block_tail m <=>
  !tail st. m (st with cs_blocks := st.cs_blocks ++ tail) =
    (FST (m st), (SND (m st)) with
      cs_blocks := (SND (m st)).cs_blocks ++ tail)
End

Theorem compiler_block_tail_bind_result:
  compiler_block_tail m /\
  (!st r out. m st = (r,out) ==> A r) /\
  (!r. A r ==> compiler_block_tail (k r)) ==>
  compiler_block_tail (comp_bind m k)
Proof
  simp[compiler_block_tail_def] >> strip_tac >> rpt gen_tac >>
  Cases_on `m st` >> rename1 `m st = (value,mid)` >>
  `A value` by metis_tac[] >>
  `m (st with cs_blocks := st.cs_blocks ++ tail) =
     (value,mid with cs_blocks := mid.cs_blocks ++ tail)` by
    (qpat_x_assum `!tail st. m _ = _` (qspecl_then [`tail`,`st`] mp_tac) >> simp[]) >>
  simp[comp_bind_def] >> first_x_assum drule >> simp[]
QED

Theorem compiler_block_tail_bind:
  compiler_block_tail m /\ (!x. compiler_block_tail (k x)) ==>
  compiler_block_tail (comp_bind m k)
Proof
  rw[compiler_block_tail_def] >> irule comp_bind_block_tail_eq >> simp[]
QED

Theorem compiler_block_tail_ignore_bind:
  compiler_block_tail m /\ compiler_block_tail k ==>
  compiler_block_tail (comp_ignore_bind m k)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_block_tail_bind >> simp[]
QED

Theorem compiler_block_tail_cond:
  compiler_block_tail m /\ compiler_block_tail n ==>
  compiler_block_tail (if b then m else n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem compiler_block_tail_primitives:
  compiler_block_tail (fresh_label suffix) /\
  compiler_block_tail fresh_var /\ compiler_block_tail fresh_id /\
  compiler_block_tail (emit inst) /\ compiler_block_tail (new_block lbl) /\
  compiler_block_tail (comp_return x) /\
  compiler_block_tail (emit_op opc ops) /\
  compiler_block_tail (emit_void opc ops) /\
  compiler_block_tail (emit_inst opc ops outs) /\
  compiler_block_tail (compile_ptr_load ctor imm loc src) /\
  compiler_block_tail (compile_ptr_store ctor imm loc dst v)
Proof
  simp[compiler_block_tail_def, fresh_label_block_tail, fresh_var_block_tail,
       fresh_id_block_tail, emit_block_tail, new_block_block_tail,
       comp_return_def, emit_op_block_tail, emit_void_block_tail,
       emit_inst_block_tail, compile_ptr_load_block_tail, compile_ptr_store_block_tail]
QED

Theorem compiler_block_tail_scaled_offset:
  compiler_block_tail
    (if b then emit_op ADD [baseop; Var ctr]
     else comp_bind (emit_op MUL [Var ctr; Lit scale])
            (\v. emit_op ADD [baseop; v]))
Proof
  irule compiler_block_tail_cond >> conj_tac
  >- simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_word_copy_loop:
  compiler_block_tail
    (compile_word_copy_loop src dst nwords load_loc store_loc ctor)
Proof
  rewrite_tac[compile_word_copy_loop_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_scaled_offset] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compile_word_copy_loop_block_tail:
  compile_word_copy_loop src dst nwords load_loc store_loc ctor
    (st with cs_blocks := st.cs_blocks ++ tail) =
  (FST (compile_word_copy_loop src dst nwords load_loc store_loc ctor st),
   (SND (compile_word_copy_loop src dst nwords load_loc store_loc ctor st)) with
     cs_blocks :=
       (SND (compile_word_copy_loop src dst nwords load_loc store_loc ctor st)).cs_blocks ++ tail)
Proof
  mp_tac compiler_block_tail_word_copy_loop >>
  simp[compiler_block_tail_def]
QED

(* Supported-callee dependency audit (selected internal function only).
   supportedProgram excludes internal calls in an Internal body; it does NOT
   exclude external calls, Send, Pop, ABI encode/decode, or the supported
   builtin forms. Therefore their expression/compiler helper cones remain
   required, including ABI, hashing/system/math, strings, and memory copying.
   Defaults and nonreentrant locks are excluded by supported function headers;
   the runtime callee is not a constructor. Dispatcher/external-entry/fallback
   compilers and vyperCompiler's finalization/package readers are not part of
   this selected action.

   In the definition cone exprLowering, stmtLowering, context, abiEncoder,
   builtin*, emitHelper, and moduleLowering's compile_internal_function,
   the only direct cs_blocks mutation is compileEnv.new_block, which conses
   the former current block. No expression/ABI/builtin helper reads, resets,
   reverses, or reorders completed blocks. The packaging/finalization readers
   in vyperCompiler are outside this action and must be handled separately
   by the already established segment/partition interface.

   IMPORTANT: comp_get itself does NOT satisfy compiler_block_tail: its
   returned value contains the history. Reachable reads are stmtLowering's
   If branch termination checks and compile_stmts, emitHelper's conditional
   jump, and moduleLowering's internal-function fallthrough check. All inspect
   only block_is_terminated (cs_current_insts), never cs_blocks. Downstream
   composition needs a projected-read/continuation boundary, not an assertion
   compiler_block_tail comp_get. Bind closure alone cannot discharge it.

   Downstream framing still needs recursive expression/list/field actions,
   typed memory/storage copies, ABI helpers and supported builtin actions,
   statement/list actions, parameter declaration/materialization, and the
   internal-function wrapper. Clean-state freshness additionally needs the
   three outputs from the PLAN: compile_state_ok, next-label monotonicity,
   and containment of newly bound labels in the old future-label set. Pending
   branch/loop labels require those latter two outputs; clean entry alone
   does not certify any recursive compilation. This file validates framing
   composition and one representative labelled loop, not that preservation. *)
