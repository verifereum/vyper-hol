(*
 * Fragment-in-context execution
 *
 * A compiled fragment is the code the compile monad emits between two
 * compile states st and st'.  frag_exec says what running that code does
 * inside any function that contains it (the blocks finished between st and
 * st', and the start of st''s current block): from the point
 * where st left off, execution reaches the point where st' leaves off, or
 * stops with Abort, Halt or IntRet.  Unlike running the fragment assembled
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
 *   frag_exec_run_inst_seq — lift a straight-line run_inst_seq result
 *)

Theory fragExec
Ancestors
  list rich_list compileEnv emitHelper exprLoweringProps
  venomExecSemantics venomInst venomInstProofs venomState instIdxIndep

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
   between st and st', from a state satisfying P at the point where st left
   off, either
   - execution reaches the point where st' leaves off in a state satisfying
     Q, and every non-Error result from there is a result from the start, or
   - execution stops with an exit result satisfying R. *)
Definition frag_exec_def:
  frag_exec ctx (st : compile_state) (st' : compile_state) P Q R <=>
    !fn s.
      fn_has_code st st' fn /\ P s /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      (?s'. Q s' /\
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
      qexists_tac `s' with vs_inst_idx := LENGTH st'.cs_current_insts` >>
      gvs[] >> rpt strip_tac >>
      qexists_tac `fuel` >> gvs[run_from_def]) >>
  disj2_tac >>
  `?n. exec_block 0 ctx bb s = Abort a (s' with vs_inst_idx := n)` by
    (qspecl_then [`t`, `s`, `0`, `ctx`, `bb`] mp_tac
       exec_block_run_inst_seq >> simp[]) >>
  qexists_tac `0` >> simp[run_from_def, exit_result_def]
QED
