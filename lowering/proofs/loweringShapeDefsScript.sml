(*
 * Shape invariant of the raw lowering (S2 of #626).
 *
 * The compile monad only appends code.  These definitions say what the code
 * a compile action appends looks like, so that o1_source_unit_ok of a lowered
 * unit follows from one fact per generator.
 *
 * TOP-LEVEL:
 *   all_blocks, state_insts      — the blocks and instructions of a state
 *   internal_label_ok            — internal entry labels ("internal ..."),
 *                                  which start each internal function
 *   fn_suffix                    — the blocks of the function being
 *                                  compiled
 *   fn_entry_insts, cur_entry_insts
 *                                — the instructions of its entry block
 *   rets_scoped                  — every RET returns to a return PC of its
 *                                  own function's entry block
 *   added_insts, added_labels    — what a compile action appended
 *   opaque_out, opaque_insts_ok  — tracks output provenance; RETPC_PARAM
 *                                  outputs used only where retpc_use_ok
 *                                  allows, while GAS outputs are ordinary values
 *   plain_operand                — an operand the lowering may pass anywhere
 *   label_or_plain               — a plain operand or a label
 *   compiler_label, jump_label_ok, inst_jump_labels_ok
 *                                — labels a terminator may jump to: compiler
 *                                  labels or "fn_" function entries
 *   label_sfx                    — the fresh_label suffix a label was made
 *                                  with; different suffixes, different labels
 *   lowered_inst_ok              — the per-instruction shape; `internal`
 *                                  selects internal-function or entry code
 *   shape_state, shape_extends   — the state invariant and the append step
 *   shape_step                   — Hoare-style judgment on compile actions
 *   shape_stable                 — a state predicate kept by every append
 *   gas_operand, retpc_operand   — a variable holding a GAS / RETPC_PARAM
 *                                  output (RETPC_PARAM: of the current
 *                                  function's entry block)
 *
 * The rules for shape_step are in loweringShapeRules.
 *)
Theory loweringShapeDefs
Ancestors
  list rich_list compileEnv loweringStateRelDefs emitHelper emitHelperProps fragExec venomInst
  unitShapeDefs

(* ===== Code held by a compile state ===== *)

(* Finished blocks oldest first, then the open block: the block stream that
   extract_context_with_internals packages. *)
Definition all_blocks_def:
  all_blocks (st : compile_state) =
    REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb;
        bb_instructions := st.cs_current_insts |>]
End

Definition state_insts_def:
  state_insts (st : compile_state) =
    FLAT (MAP (\bb. bb.bb_instructions) (all_blocks st))
End

(* Internal entry labels are internal_fn_label's "internal ..." spelling;
   every internal function's code starts with a block of one, and no other
   block has one. *)
Definition internal_label_ok_def:
  internal_label_ok lbl <=> isPREFIX "internal " lbl
End

(* The blocks of the function being compiled: from the last block with an
   internal entry label on, or all of them in entry code. *)
Definition fn_suffix_def:
  fn_suffix [] = [] /\
  fn_suffix (bb :: bbs) =
    if EXISTS (\b. internal_label_ok b.bb_label) bbs then fn_suffix bbs
    else bb :: bbs
End

(* The entry block's instructions: the return PC is a parameter, read
   there, so the RETs it reaches are those of reachable code. *)
Definition fn_entry_insts_def:
  fn_entry_insts bbs =
    case fn_suffix bbs of [] => [] | b :: _ => b.bb_instructions
End

Definition cur_entry_insts_def:
  cur_entry_insts (st : compile_state) = fn_entry_insts (all_blocks st)
End

(* Under cs_extends st st', state_insts st is a prefix of state_insts st'
   (state_insts_cs_extends), so these are exactly the appended parts. *)
Definition added_insts_def:
  added_insts (st : compile_state) (st' : compile_state) =
    DROP (LENGTH (state_insts st)) (state_insts st')
End

Definition added_labels_def:
  added_labels (st : compile_state) (st' : compile_state) =
    DROP (LENGTH (all_blocks st)) (MAP (\bb. bb.bb_label) (all_blocks st'))
End

(* ===== Opaque values ===== *)

Definition opaque_out_def:
  opaque_out opc insts x <=>
    ?inst. MEM inst insts /\ inst.inst_opcode = opc /\ MEM x inst.inst_outputs
End

(* RETPC_PARAM outputs cannot be used by ASSIGN/PHI, so their
   copy/PHI closure is just the seeds. GAS values may propagate normally. *)
Definition opaque_insts_ok_def:
  opaque_insts_ok insts <=>
    !inst x. MEM inst insts /\ MEM (Var x) inst.inst_operands ==>
      (opaque_out RETPC_PARAM insts x ==>
         inst.inst_opcode = RET /\
         ?front. inst.inst_operands = front ++ [Var x] /\ ~MEM (Var x) front)
End

(* Every RET's last operand is a RETPC_PARAM output of its own function's
   entry block. *)
Definition rets_scoped_def:
  rets_scoped bbs <=>
    !pre bb post inst.
      bbs = pre ++ [bb] ++ post /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = RET ==>
      ?front x. inst.inst_operands = front ++ [Var x] /\
                opaque_out RETPC_PARAM (fn_entry_insts (pre ++ [bb])) x
End

(* An operand that may appear in any position: no label, no compiler
   variable still to be allocated, and no return-PC value. *)
Definition plain_operand_def:
  plain_operand (st : compile_state) op <=>
    ~is_label_operand op /\
    !x. op = Var x ==>
        not_fresh_at st x /\
        ~opaque_out RETPC_PARAM (state_insts st) x
End

(* An operand of an ordinary instruction: a label (jump target, INVOKE
   callee) or a plain operand. *)
Definition label_or_plain_def:
  label_or_plain st op <=> is_label_operand op \/ plain_operand st op
End

(* ===== Per-instruction shape ===== *)

(* Labels made by fresh_label. *)
Definition compiler_label_def:
  compiler_label l <=> l IN compiler_labels_future 0
End

(* Labels made by fresh_label with suffix sfx; two different suffixes never
   give the same label, which is how a JNZ's two targets differ. *)
Definition label_sfx_def:
  label_sfx sfx l <=> ?k. l = fresh_label_output sfx k
End

(* Compiler-generated labels and external entry labels ("fn_" ++ name). *)
Definition jump_label_ok_def:
  jump_label_ok l <=> compiler_label l \/ isPREFIX "fn_" l
End

(* Every label a terminator names: the block's successors. *)
Definition inst_jump_labels_ok_def:
  inst_jump_labels_ok inst <=>
    is_terminator inst.inst_opcode ==>
    !l. MEM (Label l) inst.inst_operands ==> jump_label_ok l
End

(* Entry code (internal = F) never returns through RET and declares no
   parameters; internal-function code (internal = T) never halts the
   transaction with STOP or RETURN. *)
Definition lowered_inst_ok_def:
  lowered_inst_ok internal inst <=>
    raw_opcode_ok inst.inst_opcode /\ inst_shape_ok inst /\
    inst_jump_labels_ok inst /\
    (internal ==> ~MEM inst.inst_opcode [STOP; RETURN]) /\
    (~internal ==> inst.inst_opcode <> RET /\
                   ~is_param_opcode inst.inst_opcode)
End

(* ===== Positional certificates for checked calls ===== *)

(* A branch witness must already be closed: besides its predecessor and
   itself there is a later (possibly open) block.  Labels need not be unique. *)
Definition raw_checked_blocks_def:
  raw_checked_blocks (bbs : basic_block list) <=>
    !i k. i < LENGTH bbs /\
      k < LENGTH (EL i bbs).bb_instructions /\
      MEM (EL k (EL i bbs).bb_instructions).inst_opcode [CALL; STATICCALL] ==>
      ?v guard.
        (EL k (EL i bbs).bb_instructions).inst_outputs = [v] /\
        k + 1 < LENGTH (EL i bbs).bb_instructions /\
        guard = EL (k + 1) (EL i bbs).bb_instructions /\
        ((guard.inst_opcode = ASSERT /\ guard.inst_operands = [Var v]) \/
         (guard.inst_opcode = JNZ /\
          ?ok fail_lbl. guard.inst_operands = [Var v; Label ok; Label fail_lbl] /\
            i + 2 < LENGTH bbs /\
            (EL (i + 1) bbs).bb_label = fail_lbl /\ compiler_label fail_lbl /\
            (EL (i + 1) bbs).bb_instructions <> [] /\
            EVERY (\j. j.inst_opcode <> INVOKE)
              (EL (i + 1) bbs).bb_instructions /\
            (LAST (EL (i + 1) bbs).bb_instructions).inst_opcode = REVERT))
End

Definition raw_checked_state_def:
  raw_checked_state st <=> raw_checked_blocks (all_blocks st)
End

Theorem raw_checked_blocks_no_calls:
  EVERY (\bb. EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL])
                       bb.bb_instructions) bbs ==>
  raw_checked_blocks bbs
Proof
  simp[raw_checked_blocks_def, EVERY_EL] >> metis_tac[]
QED

Theorem raw_checked_blocks_unchecked:
  MEM call.inst_opcode [CALL; STATICCALL] ==>
  ~raw_checked_blocks [<| bb_label := l; bb_instructions := [call] |>]
Proof
  rw[raw_checked_blocks_def] >>
  qexistsl [`0`, `0`] >> simp[]
QED

Theorem raw_checked_blocks_assert:
  call.inst_outputs = [v] /\
  guard.inst_opcode = ASSERT /\ guard.inst_operands = [Var v] ==>
  raw_checked_blocks
    [<| bb_label := l; bb_instructions := [call; guard] |>]
Proof
  rw[raw_checked_blocks_def] >>
  `k = 0 \/ k = 1` by decide_tac >> gvs[] >>
  qexists_tac `v` >> simp[]
QED

Theorem raw_checked_blocks_branch:
  call.inst_outputs = [v] /\
  guard.inst_opcode = JNZ /\
  guard.inst_operands = [Var v; Label ok; Label fail_lbl] /\
  compiler_label fail_lbl /\
  rbb.bb_label = fail_lbl /\ rbb.bb_instructions <> [] /\
  EVERY (\j. j.inst_opcode <> INVOKE) rbb.bb_instructions /\
  (LAST rbb.bb_instructions).inst_opcode = REVERT /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) rbb.bb_instructions /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) cont.bb_instructions ==>
  raw_checked_blocks
    [<| bb_label := l; bb_instructions := [call; guard] |>; rbb; cont]
Proof
  rw[raw_checked_blocks_def] >>
  (Cases_on `i = 0`
   >- (gvs[] >> `k = 0 \/ k = 1` by decide_tac >> gvs[] >>
       qexists_tac `v` >> simp[]) >>
   `i = 1 \/ i = 2` by decide_tac >> gvs[EVERY_EL] >> metis_tac[])
QED

Theorem raw_checked_blocks_open_fail:
  MEM call.inst_opcode [CALL; STATICCALL] /\
  guard.inst_opcode = JNZ ==>
  ~raw_checked_blocks
    [<| bb_label := l; bb_instructions := [call; guard] |>; rbb]
Proof
  rw[raw_checked_blocks_def] >>
  qexistsl [`0`, `0`] >> simp[]
QED

Theorem raw_checked_blocks_append_no_calls:
  raw_checked_blocks bbs /\
  EVERY (\bb. EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL])
                       bb.bb_instructions) extra ==>
  raw_checked_blocks (bbs ++ extra)
Proof
  pure_rewrite_tac[raw_checked_blocks_def] >> rpt strip_tac >>
  Cases_on `i < LENGTH bbs`
  >- (gvs[EL_APPEND1] >>
      first_x_assum (qspecl_then [`i`, `k`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `v` >> simp[] >>
      `i + 1 < LENGTH bbs` by decide_tac >> simp[EL_APPEND1]) >>
  gvs[EL_APPEND2, EVERY_EL, LENGTH_APPEND] >>
  `i - LENGTH bbs < LENGTH extra` by decide_tac >> metis_tac[]
QED

Theorem raw_checked_blocks_extend_open:
  raw_checked_blocks (front ++ [bb]) /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) insts ==>
  raw_checked_blocks
    (front ++ [bb with bb_instructions := bb.bb_instructions ++ insts])
Proof
  pure_rewrite_tac[raw_checked_blocks_def] >> rpt strip_tac >>
  Cases_on `i < LENGTH front`
  >- (gvs[EL_APPEND1] >>
      first_x_assum (qspecl_then [`i`, `k`] mp_tac) >>
      simp[EL_APPEND1] >> strip_tac >> qexists_tac `v` >> simp[] >>
      `i + 1 < LENGTH front` by (gvs[LENGTH_APPEND] >> decide_tac) >>
      gvs[EL_APPEND1]) >>
  `i = LENGTH front` by (gvs[LENGTH_APPEND] >> decide_tac) >>
  gvs[EL_APPEND2] >>
  (Cases_on `k < LENGTH bb.bb_instructions`
   >- (gvs[EL_APPEND1] >>
       first_x_assum (qspecl_then [`LENGTH front`, `k`] mp_tac) >>
       simp[EL_APPEND2] >> strip_tac >>
       qexists_tac `v` >> simp[EL_APPEND1]) >>
   gvs[EL_APPEND2, EVERY_EL, LENGTH_APPEND] >>
   `k - LENGTH bb.bb_instructions < LENGTH insts` by decide_tac >> metis_tac[])
QED

Theorem raw_checked_blocks_splice:
  raw_checked_blocks (front ++ [bb]) /\
  raw_checked_blocks (head :: tail) ==>
  raw_checked_blocks
    (front ++ ((bb with bb_instructions :=
      bb.bb_instructions ++ head.bb_instructions) :: tail))
Proof
  pure_rewrite_tac[raw_checked_blocks_def] >> rpt strip_tac >>
  Cases_on `i < LENGTH front`
  >- (gvs[EL_APPEND1] >>
      qpat_x_assum `!i k. i < LENGTH front + 1 /\ _ ==> _`
        (qspecl_then [`i`, `k`] mp_tac) >>
      simp[EL_APPEND1] >> strip_tac >> qexists_tac `v` >> simp[] >>
      `i + 1 < LENGTH front` by (gvs[LENGTH_APPEND] >> decide_tac) >>
      gvs[EL_APPEND1]) >>
  Cases_on `i = LENGTH front`
  >- (gvs[EL_APPEND2] >>
      (Cases_on `k < LENGTH bb.bb_instructions`
      >- (gvs[EL_APPEND1] >>
          qpat_x_assum `!i k. i < LENGTH front + 1 /\ _ ==> _`
            (qspecl_then [`LENGTH front`, `k`] mp_tac) >>
          simp[EL_APPEND2] >> strip_tac >>
          qexists_tac `v` >> simp[EL_APPEND1]) >>
      suspend "new_head")) >>
  suspend "new_tail"
QED

Resume raw_checked_blocks_splice[new_head]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!i k. i < LENGTH front + 1 /\ _ ==> _` kall_tac >>
  gvs[EL_APPEND_EQN] >>
  first_x_assum (qspecl_then [`0`, `k - LENGTH bb.bb_instructions`] mp_tac) >>
  simp[]
QED

Resume raw_checked_blocks_splice[new_tail]:
  qpat_x_assum `!i k. i < LENGTH (front ++ [bb]) /\ _ ==> _` kall_tac >>
  `LENGTH front < i` by decide_tac >>
  gvs[EL_APPEND_EQN] >>
  first_x_assum (qspecl_then [`i - LENGTH front`, `k`] mp_tac) >>
  `i - LENGTH front = SUC (i - (LENGTH front + 1))` by decide_tac >>
  `i + 1 - LENGTH front = SUC (i - LENGTH front)` by decide_tac >>
  gvs[arithmeticTheory.ADD_CLAUSES] >>
  `i + 1 - LENGTH front = SUC (SUC (i - (LENGTH front + 1)))` by decide_tac >>
  `i + 2 < SUC (LENGTH front + LENGTH tail) <=>
   i + 1 < LENGTH front + LENGTH tail` by decide_tac >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Finalise raw_checked_blocks_splice

Theorem raw_checked_blocks_splice_assert:
  raw_checked_blocks (front ++ [bb]) /\
  call.inst_outputs = [v] /\
  guard.inst_opcode = ASSERT /\ guard.inst_operands = [Var v] ==>
  raw_checked_blocks
    (front ++ [bb with bb_instructions := bb.bb_instructions ++ [call; guard]])
Proof
  strip_tac >> drule raw_checked_blocks_splice >>
  disch_then (qspecl_then
    [`[]`, `<| bb_label := bb.bb_label; bb_instructions := [call; guard] |>`] mp_tac) >>
  simp[] >> disch_then irule >> irule raw_checked_blocks_assert >> simp[]
QED

Theorem raw_checked_blocks_splice_branch:
  raw_checked_blocks (front ++ [bb]) /\
  call.inst_outputs = [v] /\
  guard.inst_opcode = JNZ /\
  guard.inst_operands = [Var v; Label ok; Label fail_lbl] /\
  compiler_label fail_lbl /\
  rbb.bb_label = fail_lbl /\ rbb.bb_instructions <> [] /\
  EVERY (\j. j.inst_opcode <> INVOKE) rbb.bb_instructions /\
  (LAST rbb.bb_instructions).inst_opcode = REVERT /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) rbb.bb_instructions /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) cont.bb_instructions ==>
  raw_checked_blocks
    (front ++ [bb with bb_instructions := bb.bb_instructions ++ [call; guard];
               rbb; cont])
Proof
  strip_tac >> drule raw_checked_blocks_splice >>
  disch_then (qspecl_then
    [`[rbb; cont]`, `<| bb_label := bb.bb_label; bb_instructions := [call; guard] |>`] mp_tac) >>
  simp[] >> disch_then irule >> irule raw_checked_blocks_branch >> simp[] >> metis_tac[]
QED

(* ===== State invariant and the append step ===== *)

Definition shape_base_state_def:
  shape_base_state (st : compile_state) <=>
    opaque_insts_ok (state_insts st) /\ rets_scoped (all_blocks st) /\
    (!inst x. MEM inst (state_insts st) /\ MEM (Var x) inst.inst_operands ==>
              not_fresh_at st x) /\
    (!inst x. MEM inst (state_insts st) /\ MEM x inst.inst_outputs ==>
              not_fresh_at st x) /\
    (!inst x. MEM inst (state_insts st) /\ MEM x inst.inst_outputs /\
              opaque_out RETPC_PARAM (state_insts st) x ==>
              inst.inst_opcode = RETPC_PARAM) /\
    (!i j x. MEM i (state_insts st) /\ MEM j (state_insts st) /\
             i.inst_opcode = RETPC_PARAM /\
             MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j)
End

Definition shape_state_def:
  shape_state st <=> shape_base_state st /\ raw_checked_state st
End

(* LP constrains the labels of the blocks started on the way; none starts
   another internal function. *)
Definition shape_extends_def:
  shape_extends internal (LP : string -> bool) st st' <=>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    EVERY (lowered_inst_ok internal) (added_insts st st') /\
    EVERY LP (added_labels st st') /\
    EVERY (\l. ~internal_label_ok l) (added_labels st st') /\
    !inst x. MEM inst (added_insts st st') /\
             MEM inst.inst_opcode [GAS; RETPC_PARAM] /\
             MEM x inst.inst_outputs ==> ~not_fresh_at st x
End

(* The unchecked interval of an atomic call template uses only the base
   invariant.  Full shape_step is restored at the checked endpoint. *)
Definition shape_base_step_def:
  shape_base_step internal LP (P : compile_state -> bool) (m : 'a compiler)
                  (Q : 'a -> compile_state -> bool) <=>
    !st x st'. m st = (x, st') /\ P st /\ shape_base_state st ==>
      shape_extends internal LP st st' /\ shape_base_state st' /\ Q x st'
End

Definition shape_step_def:
  shape_step internal LP (P : compile_state -> bool) (m : 'a compiler)
             (Q : 'a -> compile_state -> bool) <=>
    !st x st'. m st = (x, st') /\ P st /\ shape_state st ==>
      shape_extends internal LP st st' /\ shape_state st' /\ Q x st'
End

(* A precondition that survives appending code. *)
Definition shape_stable_def:
  shape_stable (R : compile_state -> bool) <=>
    !internal LP st st'. R st /\ shape_extends internal LP st st' ==> R st'
End

(* GAS provenance and the return-PC operand restricted by opaque_insts_ok. *)
Definition gas_operand_def:
  gas_operand (st : compile_state) op <=>
    ?g. op = Var g /\ not_fresh_at st g /\
        opaque_out GAS (state_insts st) g /\
        ~opaque_out RETPC_PARAM (state_insts st) g
End

Definition retpc_operand_def:
  retpc_operand (st : compile_state) op <=>
    ?r. op = Var r /\ not_fresh_at st r /\
        opaque_out RETPC_PARAM (cur_entry_insts st) r /\
        ~opaque_out GAS (state_insts st) r
End

(* ===== The compile monad only appends ===== *)

Theorem state_insts_cs_extends:
  !st st'. cs_extends st st' ==>
           state_insts st' = state_insts st ++ added_insts st st'
Proof
  rpt strip_tac >>
  `?ext. state_insts st' = state_insts st ++ ext`
    suffices_by (strip_tac >> simp[added_insts_def, DROP_LENGTH_APPEND]) >>
  gvs[cs_extends_def, state_insts_def, all_blocks_def] >>
  Cases_on `new = []` >> gvs[IS_PREFIX_APPEND] >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  pop_assum SUBST1_TAC >>
  simp[REVERSE_APPEND, FLAT_APPEND, MAP_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem cs_extends_block_stream:
  cs_extends st st' ==>
  ?insts tail.
    all_blocks st' = REVERSE st.cs_blocks ++
      [<| bb_label := st.cs_current_bb;
          bb_instructions := st.cs_current_insts ++ insts |>] ++ tail /\
    added_insts st st' = insts ++ FLAT (MAP (\bb. bb.bb_instructions) tail)
Proof
  strip_tac >>
  `?insts tail. all_blocks st' = REVERSE st.cs_blocks ++
      [<| bb_label := st.cs_current_bb;
          bb_instructions := st.cs_current_insts ++ insts |>] ++ tail`
    suffices_by
      (strip_tac >> qexistsl [`insts`, `tail`] >> simp[] >>
       drule state_insts_cs_extends >>
       simp[state_insts_def] >>
       simp[all_blocks_def, MAP_APPEND, FLAT_APPEND] >>
       pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND_11] >> simp[]) >>
  gvs[cs_extends_def] >> Cases_on `new = []`
  >- (gvs[IS_PREFIX_APPEND, all_blocks_def] >>
      qexistsl [`l`, `[]`] >> simp[]) >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  pop_assum SUBST_ALL_TAC >> gvs[IS_PREFIX_APPEND] >>
  `LAST new = <| bb_label := st.cs_current_bb;
                 bb_instructions := st.cs_current_insts ++ l |>`
    by simp[basic_block_component_equality] >>
  qexistsl [`l`, `REVERSE (FRONT new) ++
     [<| bb_label := st'.cs_current_bb;
         bb_instructions := st'.cs_current_insts |>]`] >>
  simp[all_blocks_def, REVERSE_APPEND, APPEND_ASSOC]
QED

Theorem raw_checked_state_cs_extends:
  cs_extends st st' /\ raw_checked_state st /\
  EVERY (\j. ~MEM j.inst_opcode [CALL; STATICCALL]) (added_insts st st') ==>
  raw_checked_state st'
Proof
  strip_tac >> drule cs_extends_block_stream >> strip_tac >>
  gvs[raw_checked_state_def, EVERY_APPEND, EVERY_FLAT, EVERY_MAP] >>
  qpat_x_assum `raw_checked_blocks (all_blocks st)` mp_tac >>
  simp[all_blocks_def] >> strip_tac >>
  drule raw_checked_blocks_extend_open >>
  disch_then (qspec_then `insts` mp_tac) >> simp[] >> strip_tac >>
  drule raw_checked_blocks_append_no_calls >>
  disch_then (qspec_then `tail` mp_tac) >> simp[]
QED

Theorem block_labels_cs_extends:
  !st st'. cs_extends st st' ==>
    MAP (\bb. bb.bb_label) (all_blocks st') =
    MAP (\bb. bb.bb_label) (all_blocks st) ++ added_labels st st'
Proof
  rpt strip_tac >>
  `?ext. MAP (\bb. bb.bb_label) (all_blocks st') =
         MAP (\bb. bb.bb_label) (all_blocks st) ++ ext`
    suffices_by (strip_tac >>
                 simp[added_labels_def, DROP_LENGTH_APPEND, LENGTH_MAP] >>
                 metis_tac[LENGTH_MAP, DROP_LENGTH_APPEND]) >>
  gvs[cs_extends_def, all_blocks_def] >>
  Cases_on `new = []` >> gvs[] >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  pop_assum SUBST1_TAC >>
  simp[REVERSE_APPEND, MAP_APPEND]
QED

Theorem fn_suffix_mem:
  !bbs bb. MEM bb (fn_suffix bbs) ==> MEM bb bbs
Proof
  Induct >> simp[fn_suffix_def] >> rpt strip_tac >>
  Cases_on `EXISTS (\b. internal_label_ok b.bb_label) bbs` >>
  gvs[] >> metis_tac[]
QED

Theorem fn_suffix_append:
  !xs ys. EVERY (\b. ~internal_label_ok b.bb_label) ys ==>
    fn_suffix (xs ++ ys) = fn_suffix xs ++ ys
Proof
  Induct >> simp[fn_suffix_def] >-
    (Induct_on `ys` >> simp[fn_suffix_def, EVERY_MEM, EXISTS_MEM] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `~EXISTS (\b. internal_label_ok b.bb_label) ys`
    by gvs[EVERY_MEM, EXISTS_MEM] >>
  simp[fn_suffix_def, EXISTS_APPEND] >>
  Cases_on `EXISTS (\b. internal_label_ok b.bb_label) xs` >> simp[]
QED

Theorem fn_suffix_last_update:
  !xs bb bb'. bb.bb_label = bb'.bb_label /\
    isPREFIX bb.bb_instructions bb'.bb_instructions ==>
    !i. MEM i (FLAT (MAP (\b. b.bb_instructions) (fn_suffix (xs ++ [bb])))) ==>
        MEM i (FLAT (MAP (\b. b.bb_instructions) (fn_suffix (xs ++ [bb']))))
Proof
  Induct >> simp[fn_suffix_def] >-
    (rpt strip_tac >> gvs[IS_PREFIX_APPEND] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bb`, `bb'`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `EXISTS (\b. internal_label_ok b.bb_label) xs` >>
  Cases_on `internal_label_ok bb.bb_label` >>
  simp[fn_suffix_def, EXISTS_APPEND] >>
  gvs[IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fn_suffix_last_mem:
  !bbs bb. MEM bb (fn_suffix (bbs ++ [bb]))
Proof
  Induct >> simp[fn_suffix_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem fn_suffix_nonempty:
  !bbs. bbs <> [] ==> fn_suffix bbs <> []
Proof
  Induct >> simp[fn_suffix_def] >> rw[] >>
  Cases_on `bbs` >> gvs[]
QED

Theorem fn_entry_insts_suffix:
  !bbs i. MEM i (fn_entry_insts bbs) ==>
          MEM i (FLAT (MAP (\b. b.bb_instructions) (fn_suffix bbs)))
Proof
  rw[fn_entry_insts_def] >> Cases_on `fn_suffix bbs` >> gvs[]
QED

Theorem fn_entry_insts_mem:
  !bbs i. MEM i (fn_entry_insts bbs) ==>
          MEM i (FLAT (MAP (\b. b.bb_instructions) bbs))
Proof
  rw[] >> drule fn_entry_insts_suffix >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[fn_suffix_mem]
QED

Theorem fn_entry_insts_internal_last:
  !xs bb. internal_label_ok bb.bb_label ==>
          fn_entry_insts (xs ++ [bb]) = bb.bb_instructions
Proof
  rw[fn_entry_insts_def] >>
  `fn_suffix (xs ++ [bb]) = [bb]` suffices_by simp[] >>
  Induct_on `xs` >> simp[fn_suffix_def, EXISTS_APPEND]
QED

Theorem fn_entry_insts_append:
  !xs ys. xs <> [] /\ EVERY (\b. ~internal_label_ok b.bb_label) ys ==>
          fn_entry_insts (xs ++ ys) = fn_entry_insts xs
Proof
  rw[fn_entry_insts_def, fn_suffix_append] >>
  drule fn_suffix_nonempty >> Cases_on `fn_suffix xs` >> simp[]
QED

Theorem fn_entry_insts_last_update:
  !xs bb bb'. bb.bb_label = bb'.bb_label /\
    isPREFIX bb.bb_instructions bb'.bb_instructions ==>
    !i. MEM i (fn_entry_insts (xs ++ [bb])) ==>
        MEM i (fn_entry_insts (xs ++ [bb']))
Proof
  Induct >> simp[fn_entry_insts_def, fn_suffix_def] >-
    (rpt strip_tac >> gvs[IS_PREFIX_APPEND] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bb`, `bb'`] mp_tac) >>
  simp[fn_entry_insts_def, EXISTS_APPEND] >> rw[] >> metis_tac[]
QED

Theorem cur_entry_insts_state_insts:
  !st i. MEM i (cur_entry_insts st) ==> MEM i (state_insts st)
Proof
  rw[cur_entry_insts_def, state_insts_def] >> metis_tac[fn_entry_insts_mem]
QED

Theorem cur_entry_insts_mono:
  !internal LP st st'. shape_extends internal LP st st' ==>
    !i. MEM i (cur_entry_insts st) ==> MEM i (cur_entry_insts st')
Proof
  rpt gen_tac >> strip_tac >>
  fs[shape_extends_def, cs_extends_def] >>
  Cases_on `new = []` >> gvs[] >-
    (simp[cur_entry_insts_def, all_blocks_def] >>
     rpt strip_tac >> irule fn_entry_insts_last_update >>
     goal_assum (drule_at Any) >> simp[]) >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  qpat_x_assum `EVERY (\l. ~internal_label_ok l) _` mp_tac >>
  simp[added_labels_def, all_blocks_def, REVERSE_APPEND, MAP_APPEND,
       DROP_LENGTH_APPEND, DROP_LENGTH_TOO_LONG, DROP_APPEND] >>
  strip_tac >>
  simp[cur_entry_insts_def, all_blocks_def, REVERSE_APPEND] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)`
    by metis_tac[REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  pop_assum SUBST_ALL_TAC >>
  `1 <= LENGTH new` by (Cases_on `new` >> gvs[]) >>
  qpat_x_assum `EVERY _ (DROP (1 - LENGTH new) _)` mp_tac >>
  `1 - LENGTH new = 0` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[] >> strip_tac >>
  fs[] >>
  `EVERY (\b. ~internal_label_ok b.bb_label)
    (REVERSE (FRONT new) ++
     [<| bb_label := st'.cs_current_bb;
         bb_instructions := st'.cs_current_insts |>])`
    by fs[EVERY_MAP] >>
  `REVERSE st.cs_blocks ++ LAST new :: REVERSE (FRONT new) ++
     [<| bb_label := st'.cs_current_bb;
         bb_instructions := st'.cs_current_insts |>] =
   (REVERSE st.cs_blocks ++ [LAST new]) ++
     (REVERSE (FRONT new) ++
      [<| bb_label := st'.cs_current_bb;
          bb_instructions := st'.cs_current_insts |>])` by simp[] >>
  pop_assum SUBST1_TAC >>
  `REVERSE st.cs_blocks ++ [LAST new] <> []` by simp[] >>
  drule_all fn_entry_insts_append >> disch_then (fn th => rewrite_tac[th]) >>
  rpt strip_tac >>
  irule fn_entry_insts_last_update >> goal_assum (drule_at Any) >> simp[]
QED

Theorem not_fresh_at_mono:
  !st st' x. st.cs_next_var <= st'.cs_next_var /\ not_fresh_at st x ==>
             not_fresh_at st' x
Proof
  rw[not_fresh_at_def]
QED

Theorem shape_extends_refl:
  !internal LP st. shape_extends internal LP st st
Proof
  simp[shape_extends_def, cs_extends_refl, added_insts_def,
       added_labels_def, DROP_LENGTH_NIL, DROP_LENGTH_TOO_LONG]
QED

Theorem shape_extends_trans:
  !internal LP st1 st2 st3.
    shape_extends internal LP st1 st2 /\ shape_extends internal LP st2 st3 ==>
    shape_extends internal LP st1 st3
Proof
  rpt gen_tac >> simp[shape_extends_def] >> strip_tac >>
  `cs_extends st1 st3` by metis_tac[cs_extends_trans] >>
  `added_insts st1 st3 = added_insts st1 st2 ++ added_insts st2 st3`
    by (`state_insts st3 = state_insts st1 ++ added_insts st1 st3`
          by simp[state_insts_cs_extends] >>
        `state_insts st3 = state_insts st2 ++ added_insts st2 st3`
          by simp[state_insts_cs_extends] >>
        `state_insts st2 = state_insts st1 ++ added_insts st1 st2`
          by simp[state_insts_cs_extends] >>
        gvs[]) >>
  `added_labels st1 st3 = added_labels st1 st2 ++ added_labels st2 st3`
    by (imp_res_tac block_labels_cs_extends >> gvs[]) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem plain_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ plain_operand st op ==>
    plain_operand st' op
Proof
  rw[plain_operand_def, shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem label_or_plain_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ label_or_plain st op ==>
    label_or_plain st' op
Proof
  rw[label_or_plain_def] >> metis_tac[plain_operand_mono]
QED

Theorem gas_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ gas_operand st op ==>
    gas_operand st' op
Proof
  rw[gas_operand_def, shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem retpc_operand_mono:
  !internal LP st st' op.
    shape_extends internal LP st st' /\ retpc_operand st op ==>
    retpc_operand st' op
Proof
  rpt gen_tac >> strip_tac >>
  drule cur_entry_insts_mono >> strip_tac >>
  gvs[retpc_operand_def] >>
  `opaque_out RETPC_PARAM (cur_entry_insts st') r`
    by (fs[opaque_out_def] >> metis_tac[]) >>
  fs[shape_extends_def] >>
  imp_res_tac state_insts_cs_extends >> gvs[] >>
  gvs[opaque_out_def] >> metis_tac[not_fresh_at_mono]
QED

(* The consumer of an immediate-check certificate. *)
Theorem calls_flagged_immediate:
  !insts.
    (!k. k < LENGTH insts /\
         MEM (EL k insts).inst_opcode [CALL; STATICCALL] ==>
         ?v. (EL k insts).inst_outputs = [v] /\
             k + 1 < LENGTH insts /\
             (EL (k + 1) insts).inst_opcode <> INVOKE /\
             flag_fails bbs [v] (EL (k + 1) insts)) ==>
    calls_flagged bbs insts
Proof
  Induct >> simp[calls_flagged_def] >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
      strip_tac >> Cases_on `insts` >> gvs[flag_path_def])
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
      strip_tac >> Cases_on `insts` >> gvs[flag_path_def]) >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> gvs[]
QED

Theorem revert_path_direct_block:
  MEM bb bbs /\ bb.bb_instructions <> [] /\
  EVERY (\j. j.inst_opcode <> INVOKE) bb.bb_instructions /\
  (LAST bb.bb_instructions).inst_opcode = REVERT ==>
  revert_path bbs (LENGTH bbs) bb.bb_label
Proof
  Cases_on `bbs` >> simp[] >> strip_tac >>
  simp[Once revert_path_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem raw_checked_blocks_segment:
  raw_checked_blocks (pre ++ seg ++ post) /\
  (post = [] \/ ~compiler_label (HD post).bb_label) ==>
  EVERY (\bb. calls_flagged seg bb.bb_instructions) seg
Proof
  simp[EVERY_EL] >> strip_tac >> rpt strip_tac >>
  irule calls_flagged_immediate >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `raw_checked_blocks _` mp_tac >>
  simp[raw_checked_blocks_def] >>
  disch_then (qspecl_then [`LENGTH pre + n`, `k`] mp_tac) >>
  simp[EL_APPEND1, EL_APPEND2] >> strip_tac >>
  qexists_tac `v` >> simp[flag_fails_def] >>
  (Cases_on `n + 1 < LENGTH seg`
   >- (gvs[EL_APPEND_EQN] >>
       irule revert_path_direct_block >> simp[] >>
       irule EL_MEM >> simp[]) >>
   `n + 1 = LENGTH seg` by decide_tac >>
   `n + (LENGTH pre + 1) = LENGTH pre + LENGTH seg` by decide_tac >>
   gvs[EL_APPEND2])
QED

Theorem flat_noncompiler_head:
  EVERY (\seg. seg <> [] /\ ~compiler_label (HD seg).bb_label) segs ==>
  FLAT segs = [] \/ ~compiler_label (HD (FLAT segs)).bb_label
Proof
  Cases_on `segs` >> simp[] >> strip_tac >>
  Cases_on `h` >> gvs[]
QED

Theorem raw_checked_blocks_segments:
  !segs pre.
    raw_checked_blocks (pre ++ FLAT segs) /\
    EVERY (\seg. seg <> [] /\ ~compiler_label (HD seg).bb_label) segs ==>
    EVERY (\seg. EVERY (\bb. calls_flagged seg bb.bb_instructions) seg) segs
Proof
  Induct >> simp[] >> rpt strip_tac
  >- (irule raw_checked_blocks_segment >> qexistsl [`FLAT segs`, `pre`] >>
      simp[] >> drule flat_noncompiler_head >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qexists_tac `pre ++ h` >> simp[APPEND_ASSOC]
QED

Theorem raw_checked_blocks_entry:
  raw_checked_blocks (entry ++ FLAT segs) /\
  EVERY (\seg. seg <> [] /\ ~compiler_label (HD seg).bb_label) segs ==>
  EVERY (\bb. calls_flagged entry bb.bb_instructions) entry
Proof
  strip_tac >> irule raw_checked_blocks_segment >>
  qexistsl [`FLAT segs`, `[]`] >> simp[] >>
  drule flat_noncompiler_head >> simp[]
QED
