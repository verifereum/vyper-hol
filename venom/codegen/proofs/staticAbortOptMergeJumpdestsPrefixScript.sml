Theory staticAbortOptMergeJumpdestsPrefix
Ancestors
  asmOptMergeJumpdests codegenSymRel symInstPieces symShuffleSim
  asmSymPc asmSplice asmSymSem asmSem asmOptimizer asmWf list rich_list arithmetic
  symInstPiecesFacts

(* Execute the incoming transfer; the two continuations have related popped
   tails.  In particular the JUMPI condition is the same concrete Val. *)
Theorem redirect_taken_step[local]:
  !q. q = MAP (rename_push_label x y) p ==>
  !I. I = EL a.sym_base.as_pc p ==>
  INDEX_OF (AsmLabel x) p = SOME h /\ rn_rel x y a b /\
  a.sym_base.as_pc < LENGTH p /\
  a.sym_stack = Lab x 0 :: stk /\ b.sym_stack = Lab y 0 :: stk' /\
  (I = AsmOp "JUMP" \/
   (I = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)) ==>
  ?t. sym_steps p env 1 a = SymOK t /\
      t.sym_base.as_pc = h /\ t.sym_base.as_stack = [] /\
      t.sym_base.as_requests = a.sym_base.as_requests /\
      t.sym_base.as_call_ctx = a.sym_base.as_call_ctx /\
      (INDEX_OF (AsmLabel y) p = NONE ==>
       ?msg. sym_steps q env 1 b = SymBad msg) /\
      (!j. INDEX_OF (AsmLabel y) p = SOME j ==>
       ?b'. sym_steps q env 1 b = SymOK b' /\
            b'.sym_base.as_pc = j /\ rn_rel x y (sym_with_pc j t) b')
Proof
  simp[] >> strip_tac >>
  `b.sym_base = a.sym_base /\ a.sym_base.as_stack = [] /\
   LIST_REL (sv_rel x y) stk stk' /\
   ml_rel x y a.sym_mem_labels b.sym_mem_labels /\
   mem_blocks_ok a.sym_mem_labels /\ mem_blocks_ok b.sym_mem_labels`
    by fs[rn_rel_def] >- (
      qexists `sym_with_pc h a with sym_stack := stk` >>
      simp[sym_steps_pos, sym_steps_def, EL_MAP, rename_push_label_def,
           sym_step_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def,
           index_of_label_rename, sym_with_pc_def] >> rpt strip_tac >>
      simp[rn_rel_def]) >>
  `?rest'. stk' = Val c :: rest' /\ LIST_REL (sv_rel x y) rest rest'`
    by gvs[LIST_REL_CONS1, sv_rel_val] >>
  qexists `sym_with_pc h a with sym_stack := rest` >>
  simp[sym_steps_pos, sym_steps_def, EL_MAP, rename_push_label_def,
       sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def,
       index_of_label_rename, sym_with_pc_def] >> rpt strip_tac >>
  simp[rn_rel_def]
QED

(* The prefix may stop within the stub.  Only a successful third source
   step requires y to have a code-label index. *)
Theorem redirect_stub_cut[local]:
  t.sym_base.as_pc = h /\ t.sym_base.as_stack = [] /\
  h+2 < LENGTH p /\ EL h p = AsmLabel x /\
  EL (h+1) p = AsmPushLabel y /\ EL (h+2) p = AsmOp "JUMP" /\
  sym_steps p env r t = SymOK endst ==>
  (r < 3 ==>
   (r = 0 /\ endst = t) \/
   (r = 1 /\ endst = sym_with_pc (h+1) t) \/
   (r = 2 /\ endst = (sym_with_pc (h+2) t with
                         sym_stack := Lab y 0 :: t.sym_stack))) /\
  (3 <= r ==>
    ?j. INDEX_OF (AsmLabel y) p = SOME j /\
        sym_steps p env 3 t = SymOK (sym_with_pc j t) /\
        sym_steps p env (r-3) (sym_with_pc j t) = SymOK endst)
Proof
  strip_tac >>
  qabbrev_tac `t1 = sym_with_pc (h+1) t` >>
  qabbrev_tac `t2 = sym_with_pc (h+2) t with sym_stack := Lab y 0 :: t.sym_stack` >>
  `sym_steps p env 1 t = SymOK t1` by (
    `asm_block_at p t.sym_base.as_pc [AsmLabel x]` by simp[asm_block_at_def] >>
    drule_then (qspec_then `env` mp_tac) sym_steps_label >>
    simp[Abbr `t1`, sym_with_pc_def, asm_next_def,
         sym_state_component_equality, asm_state_component_equality]) >>
  `sym_steps p env 1 t1 = SymOK t2` by (
    `t1.sym_base.as_pc = h+1` by simp[Abbr `t1`, sym_with_pc_def] >>
    `t1.sym_base.as_pc < LENGTH p` by decide_tac >>
    simp[sym_steps_pos, sym_steps_def, sym_step_push_label, Abbr `t1`, Abbr `t2`,
         sym_with_pc_def, asm_next_def, asm_state_component_equality]) >>
  `sym_steps p env 2 t = SymOK t2` by (
    `sym_steps p env (1+1) t = SymOK t2` by (once_rewrite_tac[sym_steps_add] >> simp[]) >>
    pop_assum mp_tac >> simp[]) >>
  conj_tac >- (
    strip_tac >> `r=0 \/ r=1 \/ r=2` by decide_tac >>
    gvs[sym_steps_def, Abbr `t1`, Abbr `t2`]) >>
  strip_tac >>
  `sym_steps p env 3 t =
   case INDEX_OF (AsmLabel y) p of
     NONE => SymBad "jump target"
   | SOME j => SymOK (sym_with_pc j t)` by (
    `sym_steps p env (2+1) t = sym_steps p env 1 t2`
      by (once_rewrite_tac[sym_steps_add] >> simp[]) >>
    `t2.sym_base.as_pc < LENGTH p` by simp[Abbr `t2`, sym_with_pc_def] >>
    `(3:num) = 2+1` by decide_tac >>
    pop_assum (fn th => once_rewrite_tac[th]) >>
    qpat_assum `sym_steps p env (2+1) t = _` (fn th => rewrite_tac[th]) >>
    simp[sym_steps_pos, sym_steps_def, Abbr `t2`, sym_with_pc_def,
         sym_step_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def] >>
    Cases_on `INDEX_OF (AsmLabel y) p` >> simp[asm_state_component_equality]) >>
  `3 + (r-3) = r` by decide_tac >>
  `sym_steps p env (3+(r-3)) t = SymOK endst` by simp[] >>
  pop_assum mp_tac >> once_rewrite_tac[sym_steps_add] >>
  Cases_on `INDEX_OF (AsmLabel y) p` >> simp[]
QED

Theorem merge_rename_protected_redirect_cut:
  !q. q = MAP (rename_push_label x y) p ==>
  !h. h = LENGTH pre ==>
  !d. d = (if next = AsmLabel y then 1 else 3) ==>
  !at. at = sym_with_pc ==>
  !I. I = EL a.sym_base.as_pc p ==>
  asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/
   (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  rn_rel x y a b /\ a.sym_base.as_pc < LENGTH p /\
  a.sym_stack = Lab x 0 :: stk /\ b.sym_stack = Lab y 0 :: stk' /\
  (I = AsmOp "JUMP" \/
   (I = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)) /\
  sym_steps p env (SUC r) a = SymOK endst ==>
  ?t. sym_steps p env 1 a = SymOK t /\ t.sym_base.as_pc = h /\
      sym_steps p env r t = SymOK endst /\
      t.sym_base.as_requests = a.sym_base.as_requests /\
      t.sym_base.as_call_ctx = a.sym_base.as_call_ctx /\
      (INDEX_OF (AsmLabel y) p = NONE ==>
       ?msg. sym_steps q env 1 b = SymBad msg) /\
      (!j. INDEX_OF (AsmLabel y) p = SOME j ==>
       ?b'. sym_steps q env 1 b = SymOK b' /\
            b'.sym_base.as_pc = j /\ rn_rel x y (at j t) b') /\
      (r < d ==>
        (r = 0 /\ endst = t) \/
        (d = 3 /\ r = 1 /\ endst = at (h+1) t) \/
        (d = 3 /\ r = 2 /\ endst = (at (h+2) t with
                                     sym_stack := Lab y 0 :: t.sym_stack))) /\
      (d <= r ==>
       ?j. INDEX_OF (AsmLabel y) p = SOME j /\
           sym_steps p env d t = SymOK (at j t) /\
           sym_steps p env (r-d) (at j t) = SymOK endst)
Proof
  rpt (CHANGED_TAC (CONV_TAC Unwind.UNWIND_FORALL_CONV)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `h = LENGTH pre` >>
  `asm_labels_unique p` by
    (qpat_assum `asm_static_wf p` (mp_tac o REWRITE_RULE [asm_static_wf_def]) >> simp[]) >>
  `h+2 < LENGTH p /\ EL h p = AsmLabel x /\ EL (h+1) p = next /\
   EL (h+2) p = third`
    by (qpat_assum `p = _` (fn th => simp[th, Abbr `h`, APPEND, EL_APPEND_EQN])) >>
  qpat_x_assum `p = _` kall_tac >>
  `INDEX_OF (AsmLabel x) p = SOME h` by (irule symInstPiecesFactsTheory.asm_unique_label_index >> simp[]) >>
  `?t. sym_steps p env 1 a = SymOK t /\ t.sym_base.as_pc = h /\
       t.sym_base.as_stack = [] /\
       t.sym_base.as_requests = a.sym_base.as_requests /\
       t.sym_base.as_call_ctx = a.sym_base.as_call_ctx /\
       (INDEX_OF (AsmLabel y) p = NONE ==>
        ?msg. sym_steps (MAP (rename_push_label x y) p) env 1 b = SymBad msg) /\
       (!j. INDEX_OF (AsmLabel y) p = SOME j ==>
        ?b'. sym_steps (MAP (rename_push_label x y) p) env 1 b = SymOK b' /\
             b'.sym_base.as_pc = j /\ rn_rel x y (sym_with_pc j t) b')`
    by (irule (SIMP_RULE (srw_ss()) [] redirect_taken_step) >> gvs[]) >>
  `sym_steps p env r t = SymOK endst` by (
    `SUC r = 1+r` by decide_tac >>
    qpat_assum `sym_steps p env (SUC r) a = _` mp_tac >>
    qpat_assum `SUC r = _` (fn th => once_rewrite_tac[th]) >>
    once_rewrite_tac[sym_steps_add] >> simp[]) >>
  qexists `t` >> simp[] >>
  `next = AsmLabel y \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")`
    by fs[]
  >- (
    `INDEX_OF (AsmLabel y) p = SOME (h+1)`
      by (irule symInstPiecesFactsTheory.asm_unique_label_index >> simp[]) >>
    `sym_steps p env 1 t = SymOK (sym_with_pc (h+1) t)` by (
      `asm_block_at p t.sym_base.as_pc [AsmLabel x]` by simp[asm_block_at_def] >>
      drule_then (qspec_then `env` mp_tac) sym_steps_label >>
      simp[sym_with_pc_def, asm_next_def,
           sym_state_component_equality, asm_state_component_equality]) >>
    simp[] >> conj_tac
    >- (strip_tac >> `r=0` by decide_tac >> gvs[sym_steps_def]) >>
    strip_tac >>
    `1 + (r-1) = r` by decide_tac >>
    `sym_steps p env (1+(r-1)) t = SymOK endst` by simp[] >>
    pop_assum mp_tac >> once_rewrite_tac[sym_steps_add] >> simp[]) >>
  simp[] >> irule redirect_stub_cut >> metis_tac[]
QED
