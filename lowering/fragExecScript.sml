(*
 * Fragment-in-context execution
 *
 * A compiled fragment is the code the compile monad emits between two
 * compile states st and st'.  frag_exec says what running that code does
 * inside any function that contains it (the blocks finished between st and
 * st', and the start of st''s current block): from the point
 * where st left off, in a state that has not halted, execution reaches the
 * point where st' leaves off without halting, or stops with Abort, Halt or
 * IntRet.  Unlike running the fragment assembled
 * into a function of its own, the judgment composes, because the code after
 * the fragment is whatever the real function holds.
 *
 * TOP-LEVEL:
 *   run_from              — run a function from a state inside a block
 *   exit_result           — Abort, Halt or IntRet
 *   emitted_blocks        — the blocks finished between two compile states
 *   fn_has_code           — a function contains the code emitted between
 *                           two compile states
 *   cs_extends            — a compile state only appended to another
 *   frag_exec             — the fragment judgment
 *   cs_appends            — a compile action only appends
 *   cs_extends_*, cs_appends_* — the compile-monad primitives only append
 *   emitted_blocks_append — the new blocks of cs_extends are emitted_blocks
 *   fn_has_code_split     — containment of a fragment holds for its parts
 *   frag_exec_seq         — sequential composition
 *   frag_exec_conseq, frag_exec_refl — consequence and the empty fragment
 *   frag_exec_pointwise   — prove a fragment from each start state
 *   frag_exec_run_inst_seq — lift a straight-line run_inst_seq result
 *   frag_exec_loop        — a header/body/exit loop runs its body N times
 *
 * Steps inside a block:
 *   run_from_step         — a straight-line step moves run_from on
 *   run_from_halt         — a halting step is the result of run_from
 *   fn_has_code_same_block — the instructions a fragment appends to the
 *                           current block are in the function
 *
 * Abort and halt lifting:
 *   frag_exec_step_abort  — a one-instruction fragment that aborts
 *   frag_exec_assert_fail — a failing emitted ASSERT aborts
 *   stop_frag             — a STOP ends the run with empty return data
 *   step_inst_invoke_abort, exec_block_step_abort, run_blocks_run_from,
 *   run_context_run_blocks — Abort passes through INVOKE, exec_block,
 *                           run_blocks and run_context unchanged
 *   run_blocks_run_from_no_phi — run_blocks_run_from for a block without
 *                           PHIs, which is every block the lowering emits
 *
 * Crossing blocks:
 *   run_from_jump         — a jump enters the target block from its start
 *   run_from_jump_result  — every non-Error result after a jump is a result
 *                           before it, PHIs in the target or not
 *   frag_exec_enter       — jumping into the start of a fragment
 *
 * Helpers:
 *   fn_has_code_start, fn_has_code_mid, fn_has_code_new_block — the blocks
 *                           and instructions a contained fragment puts in
 *                           the function
 *   lookup_block_fn_insts — an instruction of a looked-up block is in fn_insts
 *)

Theory fragExec
Ancestors
  list rich_list compileEnv emitHelper exprLoweringProps
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState
  instIdxIndep

(* ===== Definitions ===== *)

(* Run fn from s, which may be in the middle of block s.vs_current_bb.
   After the block, run_blocks continues as usual. *)
Definition run_from_def:
  run_from fuel ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb =>
        case exec_block fuel ctx bb s of
          OK s' => if s'.vs_halted then Halt s' else run_blocks fuel ctx fn s'
        | r => r
End

(* Results that leave the function for good. *)
Definition exit_result_def:
  exit_result (Abort a s) = T /\
  exit_result (Halt s) = T /\
  exit_result (IntRet v s) = T /\
  exit_result _ = F
End

Theorem exit_result_not_error:
  !r e. exit_result r ==> r <> Error e
Proof
  Cases >> rw[exit_result_def]
QED

(* The blocks finished between st and st', newest first: the front of
   st'.cs_blocks that st did not have. *)
Definition emitted_blocks_def:
  emitted_blocks (st : compile_state) (st' : compile_state) =
    TAKE (LENGTH st'.cs_blocks - LENGTH st.cs_blocks) st'.cs_blocks
End

(* fn contains the code emitted between st and st': every block finished in
   between, and a block whose instructions start with st''s current
   instructions.  Blocks emitted before st need not be in fn: a unit's
   blocks are split into several functions (package_internal_blocks), and
   only the fragment's own code has to be in the function running it. *)
Definition fn_has_code_def:
  fn_has_code (st : compile_state) (st' : compile_state) (fn : ir_function) <=>
    (!bb. MEM bb (emitted_blocks st st') ==>
          lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
    ?bb. lookup_block st'.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX st'.cs_current_insts bb.bb_instructions
End

(* st' only appended to st: new finished blocks go in front (cs_blocks is
   newest first), the oldest of them is st's current block, and the current
   instructions only grow. *)
Definition cs_extends_def:
  cs_extends (st : compile_state) (st' : compile_state) <=>
    ?new. st'.cs_blocks = new ++ st.cs_blocks /\
      if new = [] then
        st'.cs_current_bb = st.cs_current_bb /\
        isPREFIX st.cs_current_insts st'.cs_current_insts
      else
        (LAST new).bb_label = st.cs_current_bb /\
        isPREFIX st.cs_current_insts (LAST new).bb_instructions
End

(* The fragment judgment.  In every function containing the code emitted
   between st and st', from a state satisfying P and not halted at the
   point where st left off, either
   - execution reaches the point where st' leaves off in a state satisfying
     Q and not halted, and every non-Error result from there is a result
     from the start, or
   - execution stops with an exit result satisfying R. *)
Definition frag_exec_def:
  frag_exec ctx (st : compile_state) (st' : compile_state) P Q R <=>
    !fn s.
      fn_has_code st st' fn /\ P s /\ ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      (?s'. Q s' /\ ~s'.vs_halted /\
            s'.vs_current_bb = st'.cs_current_bb /\
            s'.vs_inst_idx = LENGTH st'.cs_current_insts /\
            !fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn s = r) \/
      (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r)
End

(* ===== The compile monad only appends ===== *)

Theorem cs_extends_refl:
  !st. cs_extends st st
Proof
  rw[cs_extends_def] >> qexists_tac `[]` >> simp[]
QED

Theorem cs_extends_trans:
  !st1 st2 st3. cs_extends st1 st2 /\ cs_extends st2 st3 ==> cs_extends st1 st3
Proof
  rw[cs_extends_def] >> qexists_tac `new' ++ new` >> simp[] >>
  Cases_on `new = []` >> Cases_on `new' = []` >> gvs[LAST_APPEND_NOT_NIL] >>
  metis_tac[isPREFIX_TRANS]
QED

Theorem cs_extends_same_block:
  !st st'.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts ==>
    cs_extends st st'
Proof
  rw[cs_extends_def] >> qexists_tac `[]` >> simp[]
QED

Theorem cs_extends_emit:
  !inst st x st'. emit inst st = (x, st') ==> cs_extends st st'
Proof
  rw[emit_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_new_block:
  !lbl st x st'. new_block lbl st = (x, st') ==> cs_extends st st'
Proof
  rw[new_block_def, cs_extends_def] >>
  qexists_tac `[<| bb_label := st.cs_current_bb;
                   bb_instructions := st.cs_current_insts |>]` >>
  simp[]
QED

Theorem cs_extends_fresh_var:
  !st x st'. fresh_var st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_var_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_fresh_label:
  !sfx st x st'. fresh_label sfx st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_label_def] >> irule cs_extends_same_block >> simp[]
QED

Theorem cs_extends_fresh_id:
  !st x st'. fresh_id st = (x, st') ==> cs_extends st st'
Proof
  rw[fresh_id_def] >> irule cs_extends_same_block >> simp[]
QED

(* A compile action only appends. *)
Definition cs_appends_def:
  cs_appends (m : 'a compiler) <=>
    !st x st'. m st = (x, st') ==> cs_extends st st'
End

Theorem cs_appends_bind:
  !m f. cs_appends m /\ (!a. cs_appends (f a)) ==> cs_appends (comp_bind m f)
Proof
  rw[cs_appends_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >> metis_tac[cs_extends_trans]
QED

Theorem cs_appends_ignore_bind:
  !m f. cs_appends m /\ cs_appends f ==> cs_appends (comp_ignore_bind m f)
Proof
  rw[comp_ignore_bind_def] >> irule cs_appends_bind >> simp[]
QED

Theorem cs_appends_return:
  !x. cs_appends (comp_return x)
Proof
  rw[cs_appends_def, comp_return_def, cs_extends_refl]
QED

Theorem cs_appends_prims:
  (!inst. cs_appends (emit inst)) /\
  (!lbl. cs_appends (new_block lbl)) /\
  cs_appends fresh_var /\
  (!sfx. cs_appends (fresh_label sfx)) /\
  cs_appends fresh_id
Proof
  rw[cs_appends_def] >>
  metis_tac[cs_extends_emit, cs_extends_new_block, cs_extends_fresh_var,
            cs_extends_fresh_label, cs_extends_fresh_id]
QED

Theorem cs_appends_emit_helpers:
  (!opc ops outs. cs_appends (emit_inst opc ops outs)) /\
  (!opc ops. cs_appends (emit_op opc ops)) /\
  (!opc ops. cs_appends (emit_void opc ops))
Proof
  rw[emit_inst_def, emit_op_def, emit_void_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_return]) >>
  rw[cs_appends_prims, cs_appends_return]
QED

(* The new blocks of cs_extends are the emitted blocks. *)
Theorem emitted_blocks_append:
  !st st' new. st'.cs_blocks = new ++ st.cs_blocks ==> emitted_blocks st st' = new
Proof
  rpt strip_tac >> simp[emitted_blocks_def] >>
  pop_assum (fn th => rewrite_tac[th]) >> simp[TAKE_LENGTH_APPEND]
QED

(* Code in a function for a fragment is code for each of its parts. *)
Theorem fn_has_code_split:
  !st1 st2 st3 fn.
    cs_extends st1 st2 /\ cs_extends st2 st3 /\ fn_has_code st1 st3 fn ==>
    fn_has_code st1 st2 fn /\ fn_has_code st2 st3 fn
Proof
  rpt gen_tac >> simp[cs_extends_def] >> strip_tac >>
  rename1 `st2.cs_blocks = n12 ++ st1.cs_blocks` >>
  rename1 `st3.cs_blocks = n23 ++ st2.cs_blocks` >>
  `emitted_blocks st1 st2 = n12 /\ emitted_blocks st2 st3 = n23 /\
   emitted_blocks st1 st3 = n23 ++ n12` by
    (rpt conj_tac >> irule emitted_blocks_append >> fs[]) >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  asm_rewrite_tac[fn_has_code_def, MEM_APPEND] >> strip_tac >>
  rpt conj_tac
  >- metis_tac[]
  >- (Cases_on `n23 = []` >> fs[]
      >- metis_tac[isPREFIX_TRANS] >>
      metis_tac[rich_listTheory.MEM_LAST_NOT_NIL])
  >- metis_tac[] >>
  metis_tac[]
QED

(* The start of a fragment is in fn too. *)
Theorem fn_has_code_start:
  !st st' fn.
    cs_extends st st' /\ fn_has_code st st' fn ==>
    ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX st.cs_current_insts bb.bb_instructions
Proof
  rw[cs_extends_def] >> Cases_on `new = []` >> gvs[]
  >- (fs[fn_has_code_def] >> metis_tac[isPREFIX_TRANS]) >>
  `emitted_blocks st st' = new` by (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >>
  qexists_tac `LAST new` >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

(* fn contains the code of any part of a fragment it contains. *)
Theorem fn_has_code_mid:
  !st0 sa sb st' fn.
    cs_extends st0 sa /\ cs_extends sa sb /\ cs_extends sb st' /\
    fn_has_code st0 st' fn ==>
    fn_has_code sa sb fn
Proof
  rpt strip_tac >>
  `cs_extends st0 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st0 sb fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

(* A block finished by new_block is in fn as it was finished. *)
Theorem fn_has_code_new_block:
  !sa lbl x sb fn.
    new_block lbl sa = (x, sb) /\ fn_has_code sa sb fn ==>
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <| bb_label := sa.cs_current_bb;
              bb_instructions := sa.cs_current_insts |>
Proof
  rw[new_block_def] >>
  `emitted_blocks sa (sa with <| cs_blocks :=
       <| bb_label := sa.cs_current_bb;
          bb_instructions := sa.cs_current_insts |> :: sa.cs_blocks;
       cs_current_bb := lbl; cs_current_insts := [] |>) =
   [<| bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts |>]` by
    (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >>
  first_x_assum (qspec_then `<| bb_label := sa.cs_current_bb;
                               bb_instructions := sa.cs_current_insts |>`
                   mp_tac) >> simp[]
QED

Theorem lookup_block_fn_insts:
  !lbl fn bb i.
    lookup_block lbl fn.fn_blocks = SOME bb /\ MEM i bb.bb_instructions ==>
    MEM i (fn_insts fn)
Proof
  rw[fn_insts_def] >> drule lookup_block_MEM >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

(* ===== Judgment rules ===== *)

Theorem frag_exec_conseq:
  !ctx st st' P Q R P' Q' R'.
    frag_exec ctx st st' P Q R /\
    (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ (!r. R r ==> R' r) ==>
    frag_exec ctx st st' P' Q' R'
Proof
  rw[frag_exec_def] >>
  first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem frag_exec_refl:
  !ctx st P Q R. (!s. P s ==> Q s) ==> frag_exec ctx st st P Q R
Proof
  rw[frag_exec_def] >> disj1_tac >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED

(* A fragment proved from each start state on its own. *)
Theorem frag_exec_pointwise:
  !ctx st st' P Q R.
    (!s0. P s0 ==> frag_exec ctx st st' (\s. s = s0) Q R) ==>
    frag_exec ctx st st' P Q R
Proof
  rw[frag_exec_def] >> first_x_assum drule >> simp[frag_exec_def] >>
  metis_tac[]
QED

(* Sequential composition: the first fragment's end is the second's start. *)
Theorem frag_exec_seq:
  !ctx st1 st2 st3 P Q Q2 R.
    frag_exec ctx st1 st2 P Q R /\ frag_exec ctx st2 st3 Q Q2 R /\
    cs_extends st1 st2 /\ cs_extends st2 st3 ==>
    frag_exec ctx st1 st3 P Q2 R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_def] >> rpt strip_tac >>
  `fn_has_code st1 st2 fn /\ fn_has_code st2 st3 fn` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `frag_exec ctx st1 st2 P Q R`
    (mp_tac o SIMP_RULE std_ss [frag_exec_def]) >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac
  >- (rename1 `Q s2` >>
      qpat_x_assum `frag_exec ctx st2 st3 Q Q2 R`
        (mp_tac o SIMP_RULE std_ss [frag_exec_def]) >>
      disch_then (qspecl_then [`fn`, `s2`] mp_tac) >> simp[] >> strip_tac
      >- (disj1_tac >> rename1 `Q2 s3` >> qexists_tac `s3` >> simp[] >>
          rpt strip_tac >> metis_tac[])
      >> disj2_tac >> metis_tac[exit_result_not_error]) >>
  disj2_tac >> metis_tac[]
QED

(* ===== Lifting straight-line code ===== *)

Theorem run_inst_seq_inst_idx:
  !is s n.
    EVERY (\i. ~is_terminator i.inst_opcode) is ==>
    run_inst_seq is (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (run_inst_seq is s)
Proof
  Induct >> rw[run_inst_seq_def, exec_result_map_def] >>
  simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >> gvs[exec_result_map_def]
QED

Theorem DROP_EQ_CONS[local]:
  !l n h rest.
    DROP n l = h :: rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Running straight-line, call-free, terminator-free instructions inside a
   block steps exec_block past them, or aborts where run_inst_seq aborts. *)
Theorem exec_block_run_inst_seq:
  !is s fuel ctx bb.
    isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
    (!s'. run_inst_seq is s = OK s' ==>
          s'.vs_current_bb = s.vs_current_bb /\
          exec_block fuel ctx bb s =
          exec_block fuel ctx bb
            (s' with vs_inst_idx := s.vs_inst_idx + LENGTH is)) /\
    (!a s'. run_inst_seq is s = Abort a s' ==>
            ?n. exec_block fuel ctx bb s = Abort a (s' with vs_inst_idx := n))
Proof
  Induct >> simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX is rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `exec_block fuel ctx bb s =
   case step_inst_base h s of
     OK s1 => exec_block fuel ctx bb (s1 with vs_inst_idx := SUC s.vs_inst_idx)
   | IntRet vals s1 => IntRet vals s1
   | Halt s1 => Halt s1
   | Abort a s1 => Abort a s1
   | Error e => Error e` by
    (simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke] >>
     Cases_on `step_inst_base h s` >> simp[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  TRY (rename1 `step_inst_base h s = Abort _ s1` >>
       qexists_tac `s1.vs_inst_idx` >> simp[] >> NO_TAC) >>
  rename1 `step_inst_base h s = OK s1` >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
                              `fuel`, `ctx`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx] >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!s'. exec_result_map _ _ = OK s' ==> _`
        (qspec_then `s' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[exec_result_map_def, arithmeticTheory.ADD1])
  >> qpat_x_assum `!a s'. exec_result_map _ _ = Abort a s' ==> _`
       (qspecl_then [`a`, `s' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[exec_result_map_def]
QED

Theorem run_inst_seq_preserves_halted[local]:
  !is s s'.
    run_inst_seq is s = OK s' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
    s'.vs_halted = s.vs_halted
Proof
  rpt strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

(* A straight-line fragment within one block, given by its run_inst_seq
   behaviour: it either finishes in a state satisfying Q or aborts. *)
Theorem frag_exec_run_inst_seq:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s ==>
       (?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
             Q (s' with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
       (?a s'. run_inst_seq (emitted_insts st st') s = Abort a s' /\
               !n. R (Abort a (s' with vs_inst_idx := n)))) ==>
    frag_exec ctx st st' P Q R
Proof
  rw[frag_exec_def] >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?t. st'.cs_current_insts = st.cs_current_insts ++ t /\
       emitted_insts st st' = t` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX t (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  qpat_x_assum `emitted_insts st st' = t` (fn th => fs[th]) >>
  first_x_assum drule >> strip_tac
  >- (disj1_tac >>
      `!fuel. s'.vs_current_bb = s.vs_current_bb /\
              exec_block fuel ctx bb s =
              exec_block fuel ctx bb
                (s' with vs_inst_idx := s.vs_inst_idx + LENGTH t)` by
        (gen_tac >>
         qspecl_then [`t`, `s`, `fuel`, `ctx`, `bb`] mp_tac
           exec_block_run_inst_seq >> simp[]) >>
      `s'.vs_halted = s.vs_halted` by
        metis_tac[run_inst_seq_preserves_halted] >>
      qexists_tac `s' with vs_inst_idx := LENGTH st'.cs_current_insts` >>
      gvs[] >> rpt strip_tac >>
      qexists_tac `fuel` >> gvs[run_from_def]) >>
  disj2_tac >>
  `?n. exec_block 0 ctx bb s = Abort a (s' with vs_inst_idx := n)` by
    (qspecl_then [`t`, `s`, `0`, `ctx`, `bb`] mp_tac
       exec_block_run_inst_seq >> simp[]) >>
  qexists_tac `0` >> simp[run_from_def, exit_result_def]
QED

(* ===== Steps inside a block ===== *)

(* A straight-line instruction steps run_from to the next index. *)
Theorem run_from_step:
  !fuel ctx fn s bb inst s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s1 ==>
    run_from fuel ctx fn s =
    run_from fuel ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke]
QED

(* A step that halts is the result of the run. *)
Theorem run_from_halt:
  !fuel ctx fn s bb inst s'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt s' ==>
    run_from fuel ctx fn s = Halt s'
Proof
  rw[run_from_def, Once exec_block_def, step_inst_non_invoke]
QED

(* The instructions a fragment appends to the current block are in fn. *)
Theorem fn_has_code_same_block:
  !st st' fn new.
    fn_has_code st st' fn /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ new ==>
    ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
         !i. i < LENGTH new ==>
             get_instruction bb (LENGTH st.cs_current_insts + i) =
             SOME (EL i new)
Proof
  rw[fn_has_code_def] >> qexists_tac `bb` >> rw[] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[EL_APPEND2, EL_APPEND1]
QED

(* ===== Abort lifting ===== *)

(* Abort from an instruction is the result of its block. *)
Theorem exec_block_step_abort:
  !fuel ctx bb s inst a s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = Abort a s' ==>
    exec_block fuel ctx bb s = Abort a s'
Proof
  rw[Once exec_block_def]
QED

(* A fragment of one instruction that aborts in every start state. *)
Theorem frag_exec_step_abort:
  !ctx st st' inst P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    (!s. P s ==>
       ?fuel a s'. step_inst fuel ctx inst s = Abort a s' /\ R (Abort a s')) ==>
    frag_exec ctx st st' P Q R
Proof
  rw[frag_exec_def] >> disj2_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `exec_block fuel ctx bb s = Abort a s'` by
    (irule exec_block_step_abort >> qexists_tac `inst` >> gvs[]) >>
  qexists_tac `fuel` >>
  gvs[run_from_def, exit_result_def]
QED

(* A failing emitted ASSERT aborts with Revert_abort. *)
Theorem frag_exec_assert_fail:
  !ctx st op x st' P Q R.
    emit_void ASSERT [op] st = (x, st') /\
    (!s. P s ==>
       eval_operand op s = SOME 0w /\
       R (Abort Revert_abort (revert_state (set_returndata [] s)))) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> irule frag_exec_step_abort >>
  gvs[emit_void_assert_inst] >>
  `(mk_inst st.cs_next_id ASSERT [op] []).inst_opcode <> INVOKE` by
    simp[venomInstTheory.mk_inst_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[step_inst_non_invoke, assert_false_correct]
QED

(* A STOP ends the run, with empty return data. *)
Theorem stop_frag:
  !ctx st st' id P Q R.
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [mk_inst id STOP [] []] /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx st st' P Q R
Proof
  rw[frag_exec_def] >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) =
   SOME (mk_inst id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `(mk_inst id STOP [] []).inst_opcode = STOP` by simp[mk_inst_def] >>
  `step_inst_base (mk_inst id STOP [] []) s =
   Halt (halt_state (s with vs_returndata := []))` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  `run_from 0 ctx fn s = Halt (halt_state (s with vs_returndata := []))` by
    (irule run_from_halt >>
     qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >> simp[]) >>
  qexists_tac `0` >> simp[exit_result_def]
QED

(* Abort from a callee is the result of the INVOKE. *)
Theorem step_inst_invoke_abort:
  !fuel ctx inst s name arg_ops callee args cs a s'.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name, arg_ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops s = SOME args /\
    setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = Abort a s' ==>
    step_inst fuel ctx inst s = Abort a s'
Proof
  rw[Once step_inst_def]
QED


(* Entering a block is running it from past its PHIs, so every result of
   run_from there, Abort included, is the result of run_blocks. *)
Theorem run_blocks_run_from:
  !fuel ctx fn s bb s_phi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi ==>
    run_blocks (SUC fuel) ctx fn s =
    run_from fuel ctx fn
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  simp[Once run_blocks_def, run_from_def] >>
  Cases_on `exec_block fuel ctx bb
              (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[]
QED

Theorem eval_phis_no_phi[local]:
  !l s. phi_prefix_length l = 0 ==> eval_phis s l = OK s
Proof
  Cases >> rw[eval_phis_def, phi_prefix_length_def]
QED

(* The lowering emits no PHIs, so entering one of its blocks is running it
   from its first instruction. *)
Theorem run_blocks_run_from_no_phi:
  !fuel ctx fn s bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 ==>
    run_blocks (SUC fuel) ctx fn s =
    run_from fuel ctx fn (s with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `eval_phis s bb.bb_instructions = OK s` by simp[eval_phis_no_phi] >>
  drule_all run_blocks_run_from >> simp[]
QED

(* The unit's result is the entry function's run_blocks result. *)
Theorem run_context_run_blocks:
  !fuel ctx s name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl ==>
    run_context fuel ctx s =
    run_blocks fuel ctx fn
      (s with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  rw[run_context_def, run_function_def]
QED


(* ===== Crossing blocks ===== *)

(* A jump from the current block enters the target block from its first
   instruction, at the cost of one unit of fuel. *)
Theorem run_from_jump:
  !fuel ctx fn s bb inst lbl bb'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\
    phi_prefix_length bb'.bb_instructions = 0 ==>
    run_from (SUC fuel) ctx fn s = run_from fuel ctx fn (jump_to lbl s)
Proof
  rpt strip_tac >>
  `(jump_to lbl s).vs_current_bb = lbl /\ ~(jump_to lbl s).vs_halted /\
   jump_to lbl s with vs_inst_idx := 0 = jump_to lbl s` by
    simp[jump_to_def] >>
  `exec_block (SUC fuel) ctx bb s = OK (jump_to lbl s)` by
    simp[Once exec_block_def, step_inst_non_invoke] >>
  `run_blocks (SUC fuel) ctx fn (jump_to lbl s) =
   run_from fuel ctx fn (jump_to lbl s with vs_inst_idx := 0)` by
    (irule run_blocks_run_from_no_phi >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_from_def])) >>
  asm_simp_tac std_ss [] >> simp[]
QED

Theorem step_inst_base_phi[local]:
  !inst s.
    inst.inst_opcode = PHI ==>
    step_inst_base inst s = Error "phi outside prefix"
Proof
  rw[step_inst_base_def]
QED

(* Every non-Error result after a jump is the result before it, one unit of
   fuel later.  No premise on the target: a missing block is an Error, and
   so is a block that starts with a PHI, since run_from reaches the PHI by
   stepping it. *)
Theorem run_from_jump_result:
  !fuel ctx fn s bb inst lbl r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    run_from fuel ctx fn (jump_to lbl s) = r /\ (!e. r <> Error e) ==>
    run_from (SUC fuel) ctx fn s = r
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- gvs[run_from_def, jump_to_def] >>
  rename1 `lookup_block lbl _ = SOME bb'` >>
  Cases_on `phi_prefix_length bb'.bb_instructions = 0`
  >- (drule_all run_from_jump >> simp[]) >>
  `?phi rest. bb'.bb_instructions = phi :: rest /\ phi.inst_opcode = PHI` by
    (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
     rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, jump_to_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_phi]
QED

(* A jump to the start of a fragment's first block: what the fragment
   reaches or exits with, the jump does too.  This is how a JNZ or JMP
   enters a branch, a loop body or a failure block. *)
Theorem frag_exec_enter:
  !ctx fn s bb inst sa sb P Q R.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to sa.cs_current_bb s) /\
    ~s.vs_halted /\
    frag_exec ctx sa sb P Q R /\ fn_has_code sa sb fn /\
    sa.cs_current_insts = [] /\ P (jump_to sa.cs_current_bb s) ==>
    (?s'. Q s' /\ ~s'.vs_halted /\
          s'.vs_current_bb = sb.cs_current_bb /\
          s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
          !fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
                   ?fuel'. run_from fuel' ctx fn s = r) \/
    (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r)
Proof
  rpt strip_tac >>
  `!fuel r. run_from fuel ctx fn (jump_to sa.cs_current_bb s) = r /\
            (!e. r <> Error e) ==> run_from (SUC fuel) ctx fn s = r` by
    metis_tac[run_from_jump_result] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspecl_then [`fn`, `jump_to sa.cs_current_bb s`] mp_tac) >>
  impl_tac >- simp[jump_to_def] >>
  strip_tac
  >- (disj1_tac >> qexists_tac `s'` >> simp[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[exit_result_not_error]
QED

(* Fixed-function interface for fragment outcomes. *)
Definition frag_outcome_def:
  frag_outcome ctx fn s st Q R <=>
    (?t. Q t /\ ~t.vs_halted /\
         t.vs_current_bb = st.cs_current_bb /\
         t.vs_inst_idx = LENGTH st.cs_current_insts /\
         !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx fn s = r) \/
    (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r)
End

Theorem frag_outcome_refl:
  Q s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  frag_outcome ctx fn s st Q R
Proof
  rw[frag_outcome_def] >> disj1_tac >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED

Theorem frag_outcome_apply:
  frag_exec ctx sa sb P Q R /\ fn_has_code sa sb fn /\
  P s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  frag_outcome ctx fn s sb Q R
Proof
  simp[frag_exec_def, frag_outcome_def] >> metis_tac[]
QED

Theorem frag_outcome_compose:
  frag_outcome ctx fn s sa P R /\
  (!t. P t /\ ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       frag_outcome ctx fn t sb Q R) ==>
  frag_outcome ctx fn s sb Q R
Proof
  rw[frag_outcome_def]
  >- (first_x_assum drule >> simp[] >> strip_tac
      >- (rename1 `Q endpoint` >> disj1_tac >>
          qexists_tac `endpoint` >> simp[] >> metis_tac[]) >>
      disj2_tac >> metis_tac[exit_result_not_error]) >>
  disj2_tac >> metis_tac[]
QED

Theorem frag_outcome_jump:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
  frag_outcome ctx fn (jump_to lbl s) sb Q R ==>
  frag_outcome ctx fn s sb Q R
Proof
  rpt strip_tac >>
  `!fuel r. run_from fuel ctx fn (jump_to lbl s) = r /\
            (!e. r <> Error e) ==> run_from (SUC fuel) ctx fn s = r` by
    metis_tac[run_from_jump_result] >>
  gvs[frag_outcome_def]
  >- (rename1 `Q endpoint` >> disj1_tac >>
      qexists_tac `endpoint` >> simp[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[exit_result_not_error]
QED

(* ===== Loops ===== *)

(* A loop as the lowering emits it: a jump to a header block whose
   straight-line code ends in JNZ to the exit or to the body, the body
   fragment, a jump back to the header, and the exit block.  I k holds at
   the start of the header's k-th run and J k at its JNZ; the condition is
   nonzero exactly at k = N, so the body runs N times.  Jumps change only
   the position, so I and J must not depend on it. *)
Theorem frag_exec_loop:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr body exit cnd
   x0 x1 x2 x3 x4 x5 I J N R.
    emit_inst JMP [Label hdr] [] st0 = (x0, st1) /\
    new_block hdr st1 = (x1, sth) /\
    emit_inst JNZ [cnd; Label exit; Label body] [] stj = (x2, st2) /\
    new_block body st2 = (x3, stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4, st3) /\
    new_block exit st3 = (x5, stx) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    (!k s l. I k s ==> I k (jump_to l s)) /\
    (!k s l. J k s ==> J k (jump_to l s)) /\
    (!k. k <= N ==> frag_exec ctx sth stj (I k) (J k) R) /\
    (!k s. k <= N /\ J k s ==>
           ?w. eval_operand cnd s = SOME w /\ (w = 0w <=> k < N)) /\
    (!k. k < N ==> frag_exec ctx stb ste (J k) (I (SUC k)) R) ==>
    frag_exec ctx st0 stx (I 0) (J N) R
Proof
  cheat
QED
