(* Continuation-style transport in the actual execution semantics. *)
Theory functionInlinerSimulation
Ancestors
  functionInlinerOperational functionInlinerCallBoundary venomExecSemantics
  functionInlinerFrame functionInlinerDefs venomState venomInst venomWf list pred_set

(* The countdown is the number of ordinary instructions still to traverse.
   R owns the program points; Q owns all terminal and continuation results. *)
Theorem inline_exec_block_segment:
  !(n:num) R Q fuel ctx bb fuel' ctx' bb' s t.
    R n s t /\
    (!s t. R 0 s t ==>
      Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)) /\
    (!m s t. 0 < m /\ m <= n /\ R m s t ==>
      ?i j. get_instruction bb s.vs_inst_idx = SOME i /\
        get_instruction bb' t.vs_inst_idx = SOME j /\
        ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode /\
        (case step_inst fuel ctx i s of
           OK u => ?v. step_inst fuel' ctx' j t = OK v /\
             R (m - 1) (u with vs_inst_idx := SUC s.vs_inst_idx)
                       (v with vs_inst_idx := SUC t.vs_inst_idx)
         | IntRet vals u => F
         | Halt u => ?v. step_inst fuel' ctx' j t = Halt v /\
             Q (Halt u) (Halt v)
         | Abort a u => ?v. step_inst fuel' ctx' j t = Abort a v /\
             Q (Abort a u) (Abort a v)
         | Error e => ?e'. step_inst fuel' ctx' j t = Error e' /\
             Q (Error e) (Error e'))) ==>
    Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)
Proof
  Induct_on `n`
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!m s t. _` (qspecl_then [`SUC n`, `s`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx i s` >> gvs[] >>
  qpat_x_assum `!R Q fuel ctx bb fuel' ctx' bb' s t. _` irule >>
  qexists `R` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem inline_opaque_frame_indices[simp]:
  inline_opaque_frame_rel ren V opaque saved P
    (s with vs_inst_idx := i) (t with vs_inst_idx := j) <=>
  inline_opaque_frame_rel ren V opaque saved P s t
Proof
  simp[functionInlinerFrameTheory.inline_opaque_frame_rel_def,
    functionInlinerFrameTheory.inline_frame_rel_def,
    functionInlinerFrameTheory.inline_shared_frame_def,
    stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]
QED

(* Indexed clone consumer. supps records support after each successful prefix;
   terminal observations are deliberately independent of instruction indices.
   For pre ++ body ++ tail and pre' ++ MAP (clone_instruction p labels) body
   ++ tail', take n = LENGTH body, a = LENGTH pre, b = LENGTH pre', and
   instrs m = EL (n - m) body. The tails remain arbitrary continuations. *)
Theorem inline_clone_exec_block_segment:
  !n supps instrs Q ren opaque saved P p labels fuel ctx bb fuel' ctx' bb' a b s t.
    s.vs_inst_idx = a /\ t.vs_inst_idx = b /\
    inline_opaque_frame_rel ren (supps n) opaque saved P s t /\
    (!m. 0 < m /\ m <= n ==>
      get_instruction bb (a + n - m) = SOME (instrs m) /\
      get_instruction bb' (b + n - m) = SOME (clone_instruction p labels (instrs m)) /\
      inst_wf (instrs m) /\ inline_ordinary_opcode (instrs m).inst_opcode /\
      ~is_terminator (instrs m).inst_opcode /\
      supps (m - 1) = supps m UNION set (instrs m).inst_outputs /\
      (!u v. u IN supps m UNION set (instrs m).inst_outputs /\
             v IN supps m UNION set (instrs m).inst_outputs ==> (ren u = ren v <=> u = v)) /\
      (!x. MEM x (instrs m).inst_outputs ==> ren x NOTIN P /\ ren x = STRCAT p x)) /\
    (!m s t. 0 < m /\ m <= n /\
      s.vs_inst_idx = a + n - m /\ t.vs_inst_idx = b + n - m /\
      inline_opaque_frame_rel ren (supps m) opaque saved P s t ==>
      !op. MEM op (instrs m).inst_operands ==>
        eval_operand (clone_operand p labels op) t = eval_operand op s) /\
    (!s t. s.vs_inst_idx = a + n /\ t.vs_inst_idx = b + n /\
      inline_opaque_frame_rel ren (supps 0) opaque saved P s t ==>
      Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)) /\
    (!m s t. m <= n /\ inline_opaque_frame_rel ren (supps m) opaque saved P s t ==>
      Q (Halt s) (Halt t) /\ (!a. Q (Abort a s) (Abort a t))) /\
    (!e e'. Q (Error e) (Error e')) ==>
    Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)
Proof
  rpt gen_tac >> strip_tac >>
  irule inline_exec_block_segment >>
  qexistsl [`\m s t. s.vs_inst_idx = a + n - m /\
    t.vs_inst_idx = b + n - m /\
    inline_opaque_frame_rel ren (supps m) opaque saved P s t`, `n`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `inline_opaque_frame_rel ren (supps m) opaque saved P ss tt` >>
  qpat_assum `!m. 0 < m /\ m <= n ==> _` (qspec_then `m` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac >- simp[clone_instruction_def] >>
  `inline_ordinary_step_result ren (supps m) opaque saved P (instrs m)
    (step_inst fuel ctx (instrs m) ss)
    (step_inst fuel' ctx' (clone_instruction p labels (instrs m)) tt)` by
    (irule inline_ordinary_clone_step_result >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx (instrs m) ss` >>
  gvs[inline_ordinary_step_result_def] >> metis_tac[]
QED
