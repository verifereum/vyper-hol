(*
 * Single-site splices of assembly, against the finalizer contract.
 *
 * The final assembly optimizer's rules rewrite a window of instructions
 * in place: p = pfx ++ pat ++ sfx becomes p' = pfx ++ repl ++ sfx. Each
 * rule walks the program and rewrites one window at a time, so its proof
 * is an induction on the walk that composes single-site splices with
 * asm_refines_trans. This theory proves what every splice shares.
 *
 * Statically, a splice whose replacement has no data, no labels, no new
 * label references and no more bytes than the pattern keeps the program
 * asm_static_wf: label offsets only shrink.
 *
 * Dynamically, when repl holds no label and nothing refers to a label
 * in pat, no jump lands inside the window (sym_state_labels_in: a run
 * only ever holds labels p refers to), and code outside it runs the same
 * at PCs moved by splice_pc. So asm_refines p p' reduces to
 * asm_window_refines: from the
 * window's start, some steps of p and some steps of p' reach the same
 * state outside the window, or the same terminal result.
 *
 * TOP-LEVEL:
 *   sym_steps                  — a fixed number of symbolic steps
 *   splice_pc                  — where a PC outside the window moves
 *   asm_splice_ok              — static side conditions on pat and repl
 *   asm_window_refines         — the local obligation of a rewrite
 *   asm_splice_static_wf       — a splice keeps asm_static_wf and the data
 *   asm_splice_window_refines  — a splice refines, given its window
 *   asm_refines_cons           — the walk's step past a non-matching item
 *   sym_state_labels_in        — every label a state holds is in a list
 *   sym_step_labels_in, sym_steps_labels_in
 *                              — runs keep the labels among p's references
 *
 * Step lemmas for rules' window proofs: sym_steps_pos, sym_step_push_label,
 * sym_step_iszero_val, sym_step_iszero_cases, sym_step_jumpi_label.
 *)

Theory asmSplice
Ancestors
  asmSymPc finalizerContract asmSymSem asmOptimizer asmWf symbolResolve
  codegenEncodingWf spillWordBounds

(* ===== Fixed-length runs ===== *)

(* sym_run's checks, for exactly n steps: 0 steps is success. *)
Definition sym_steps_def:
  sym_steps p env 0 ss = SymOK ss ∧
  sym_steps p env (SUC n) ss =
    if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
    else
      case sym_step p env (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_steps p env n ss'
      | r => r
End

(* One step of sym_steps, for a step count given as a numeral. *)
Theorem sym_steps_pos:
  0 < n ∧ ss.sym_base.as_pc < LENGTH p ⇒
  sym_steps p env n ss =
    case sym_step p env (EL ss.sym_base.as_pc p) ss of
      SymOK ss' => sym_steps p env (n - 1) ss'
    | r => r
Proof
  Cases_on `n` >> rw[sym_steps_def]
QED

Theorem sym_step_push_label:
  sym_step p env (AsmPushLabel l) ss =
  SymOK (ss with <| sym_base := asm_next ss.sym_base;
                    sym_stack := Lab l 0 :: ss.sym_stack |>)
Proof
  simp[sym_step_def, sym_set_stack_def]
QED

Theorem mem_labels_clear_none[local]:
  mem_labels_clear m (λi. F) = m
Proof
  simp[mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem sym_step_iszero_val:
  ss.sym_stack = Val w :: stk ⇒
  sym_step p env (AsmOp "ISZERO") ss =
  SymOK (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                    sym_stack := Val (b2w (w = 0w)) :: stk |>)
Proof
  rw[sym_step_def, sym_step_op_def, asmSemTheory.dup_table_def,
     asmSemTheory.swap_table_def, asmSemTheory.log_table_def,
     sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
     sval_val_def, asm_op_mem_reads_def, asm_op_mem_writes_def,
     mem_labels_hit_def, mem_labels_clear_none, sym_lift_def,
     asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_arith_def,
     asmSemTheory.asm_step_compare_def, asmSemTheory.asm_unop_def,
     asmSemTheory.asm_next_def] >>
  simp[sym_state_component_equality, asmSemTheory.asm_state_component_equality]
QED

Theorem sym_step_iszero_cases:
  (∃w stk. ss.sym_stack = Val w :: stk) ∨
  (∃e. sym_step p env (AsmOp "ISZERO") ss = SymError e) ∨
  (∃e. sym_step p env (AsmOp "ISZERO") ss = SymBad e)
Proof
  Cases_on `ss.sym_stack`
  >- simp[sym_step_def, sym_step_op_def, asmSemTheory.dup_table_def,
          asmSemTheory.swap_table_def, sym_step_concrete_def,
          asm_op_arity_def, asm_op_arity_table_def] >>
  rename1 `ss.sym_stack = v :: _` >> Cases_on `v` >>
  simp[sym_step_def, sym_step_op_def, asmSemTheory.dup_table_def,
       asmSemTheory.swap_table_def, sym_step_concrete_def,
       asm_op_arity_def, asm_op_arity_table_def, sval_val_def]
QED

Theorem sym_step_jumpi_label:
  ss.sym_stack = Lab l 0 :: Val c :: stk ⇒
  sym_step p env (AsmOp "JUMPI") ss =
  if c = 0w then
    SymOK (ss with <| sym_base := asm_next ss.sym_base; sym_stack := stk |>)
  else
    case INDEX_OF (AsmLabel l) p of
      SOME i => SymOK (ss with <| sym_base := ss.sym_base with as_pc := i;
                                  sym_stack := stk |>)
    | NONE => SymBad "jumpi target"
Proof
  rw[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def,
     sym_set_stack_def]
QED

Theorem sym_run_0[local]:
  sym_run p env 0 ss = SymError "out of fuel"
Proof
  simp[Once sym_run_def]
QED

Theorem sym_run_steps_ok:
  ∀j fuel ss a.
    sym_steps p env j ss = SymOK a ⇒
    sym_run p env (j + fuel) ss = sym_run p env fuel a
Proof
  Induct >> simp[sym_steps_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  simp[Once sym_run_def, arithmeticTheory.ADD_CLAUSES] >>
  first_x_assum drule >> simp[]
QED

Theorem sym_run_steps_stop:
  ∀j fuel ss.
    (∀a. sym_steps p env j ss ≠ SymOK a) ∧ j ≤ fuel ⇒
    sym_run p env fuel ss = sym_steps p env j ss
Proof
  Induct >> simp[sym_steps_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >> gvs[] >>
  simp[Once sym_run_def] >> rw[] >> gvs[] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem sym_run_terminal_steps:
  ∀j fuel ss.
    sym_terminal (sym_run p env fuel ss) ⇒
    (∀a. sym_steps p env j ss = SymOK a ⇒
         j < fuel ∧ sym_run p env fuel ss = sym_run p env (fuel - j) a) ∧
    ((∀a. sym_steps p env j ss ≠ SymOK a) ⇒
     sym_run p env fuel ss = sym_steps p env j ss)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `j < fuel`
      >- (drule_then (qspec_then `fuel - j` mp_tac) sym_run_steps_ok >>
          simp[]) >>
      drule_then (qspec_then `0` mp_tac) sym_run_steps_ok >>
      simp[sym_run_0] >> strip_tac >>
      `fuel ≤ j` by decide_tac >>
      drule_then (qspecl_then [`p`, `env`, `ss`] strip_assume_tac)
        sym_run_less_fuel >> gvs[sym_terminal_def]) >>
  Cases_on `j ≤ fuel` >- (irule sym_run_steps_stop >> simp[]) >>
  `fuel ≤ j` by decide_tac >>
  drule_then (qspecl_then [`p`, `env`, `ss`] strip_assume_tac)
    sym_run_less_fuel >> gvs[sym_terminal_def] >>
  irule sym_run_steps_stop >> simp[]
QED

(* ===== The splice ===== *)

(* A PC of p outside the window [k, k + m) as a PC of p', where the window
   has length n. The window's start k stays put. *)
Definition splice_pc_def:
  splice_pc (k:num) m n pc = if pc ≤ k then pc else pc + n - m
End

Definition asm_splice_ok_def:
  asm_splice_ok pat repl ⇔
    pat ≠ [] ∧
    EVERY (λi. ¬is_data_inst i) (pat ++ repl) ∧
    (∀l. ¬MEM (AsmLabel l) repl) ∧
    (∀l. MEM l (asm_label_refs repl) ⇒ MEM l (asm_label_refs pat)) ∧
    (∀name. MEM (AsmOp name) repl ⇒
            MEM (AsmOp name) pat ∨ IS_SOME (evm_opcode_byte name)) ∧
    (∀bytes. MEM (AsmPush bytes) repl ⇒
             MEM (AsmPush bytes) pat ∨ LENGTH bytes ≤ 32) ∧
    (∀l d. MEM (AsmPushOfst l d) repl ⇒ MEM (AsmPushOfst l d) pat) ∧
    SUM (MAP symbolResolve$asm_inst_size repl) ≤
    SUM (MAP symbolResolve$asm_inst_size pat)
End

(* From the window's start, j > 0 steps of p and j' steps of p' either
   leave the window at corresponding PCs in the same state, or end in
   related terminal results. A run of p that errs or misuses a label
   there constrains nothing. *)
Definition asm_window_refines_def:
  asm_window_refines pfx pat repl sfx ⇔
    asm_static_wf (pfx ++ pat ++ sfx) ⇒
    ∀env ss.
      ss.sym_base.as_pc = LENGTH pfx ∧ ss.sym_base.as_stack = [] ⇒
      ∃j j'.
        0 < j ∧
        (∀a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a ⇒
             (a.sym_base.as_pc ≤ LENGTH pfx ∨
              LENGTH pfx + LENGTH pat ≤ a.sym_base.as_pc) ∧
             sym_steps (pfx ++ repl ++ sfx) env j' ss =
               SymOK (sym_with_pc
                        (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
                           a.sym_base.as_pc) a)) ∧
        (sym_terminal (sym_steps (pfx ++ pat ++ sfx) env j ss) ⇒
         sym_result_rel (sym_steps (pfx ++ pat ++ sfx) env j ss)
           (sym_steps (pfx ++ repl ++ sfx) env j' ss))
End

Theorem INDEX_OF_NIL:
  INDEX_OF x [] = NONE
Proof
  simp[listTheory.INDEX_OF_def, listTheory.INDEX_FIND_def]
QED

Theorem INDEX_OF_CONS:
  INDEX_OF x (h :: t) =
  if x = h then SOME 0 else OPTION_MAP SUC (INDEX_OF x t)
Proof
  rw[listTheory.INDEX_OF_def, listTheory.INDEX_FIND_def] >>
  simp[Once listTheory.INDEX_FIND_add] >>
  Cases_on `INDEX_FIND 0 ($= x) t` >> simp[] >>
  rename1 `SOME q` >> PairCases_on `q` >> simp[arithmeticTheory.ADD1]
QED

Theorem INDEX_OF_APPEND:
  ∀l1 x l2.
    INDEX_OF x (l1 ++ l2) =
    if MEM x l1 then INDEX_OF x l1
    else OPTION_MAP ($+ (LENGTH l1)) (INDEX_OF x l2)
Proof
  Induct >> rw[INDEX_OF_CONS, INDEX_OF_NIL] >> gvs[] >>
  Cases_on `INDEX_OF x l2` >> simp[arithmeticTheory.ADD1]
QED

Theorem INDEX_OF_APPEND_NOT_MEM[local]:
  ¬MEM x l1 ⇒
  INDEX_OF x (l1 ++ l2) = OPTION_MAP ($+ (LENGTH l1)) (INDEX_OF x l2)
Proof
  simp[INDEX_OF_APPEND]
QED

Theorem asm_labels_unique_append_not_mem:
  ∀l1 l2 x.
    asm_labels_unique (l1 ++ l2) ∧ MEM (AsmLabel x) l2 ⇒
    ¬MEM (AsmLabel x) l1
Proof
  rw[asm_labels_unique_def, listTheory.FILTER_APPEND_DISTRIB,
     listTheory.ALL_DISTINCT_APPEND] >>
  strip_tac >>
  first_x_assum (qspec_then `SOME x` mp_tac) >>
  simp[listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  conj_tac >> qexists_tac `AsmLabel x` >> simp[]
QED

Theorem splice_index_of_label:
  pat ≠ [] ∧ ¬MEM (AsmLabel l) pat ∧ (∀l. ¬MEM (AsmLabel l) repl) ⇒
  INDEX_OF (AsmLabel l) (pfx ++ repl ++ sfx) =
    OPTION_MAP (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl))
      (INDEX_OF (AsmLabel l) (pfx ++ pat ++ sfx)) ∧
  ∀i. INDEX_OF (AsmLabel l) (pfx ++ pat ++ sfx) = SOME i ⇒
      i < LENGTH pfx ∨ LENGTH pfx + LENGTH pat ≤ i
Proof
  strip_tac >>
  Cases_on `MEM (AsmLabel l) pfx`
  >- (simp[INDEX_OF_APPEND] >> rpt strip_tac >>
      Cases_on `INDEX_OF (AsmLabel l) pfx` >>
      gvs[listTheory.INDEX_OF_eq_SOME, splice_pc_def]) >>
  simp[INDEX_OF_APPEND, INDEX_OF_APPEND_NOT_MEM] >>
  Cases_on `INDEX_OF (AsmLabel l) sfx` >> simp[splice_pc_def] >>
  Cases_on `pat` >> gvs[]
QED

(* ===== Static well-formedness ===== *)

Theorem offsets_append_no_bindings[local]:
  !repl pfx.
    EVERY (\i. ~is_data_inst i) repl /\
    (!l. ~MEM (AsmLabel l) repl) ==>
    SND (compute_label_offsets (pfx ++ repl)) =
    SND (compute_label_offsets pfx)
Proof
  ho_match_mp_tac listTheory.SNOC_INDUCT >>
  simp[] >> rpt gen_tac >> strip_tac >>
  simp[listTheory.EVERY_SNOC, listTheory.MEM_SNOC] >> rpt strip_tac >>
  simp[listTheory.APPEND_SNOC, compute_label_offsets_snoc] >>
  Cases_on `x` >> gvs[is_data_inst_def] >> metis_tac[]
QED

Theorem offsets_append_dominate[local]:
  !pat pfx l off.
    FLOOKUP (SND (compute_label_offsets pfx)) l = SOME off ==>
    ?old. FLOOKUP (SND (compute_label_offsets (pfx ++ pat))) l = SOME old /\
          off <= old
Proof
  ho_match_mp_tac listTheory.SNOC_INDUCT >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[listTheory.APPEND_SNOC, compute_label_offsets_snoc] >>
  Cases_on `x` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >>
  first_x_assum drule >> strip_tac >>
  qspec_then `pfx ++ pat` strip_assume_tac compute_label_offsets_bound >>
  res_tac >> gvs[]
QED

Theorem offsets_common_suffix_dominate[local]:
  !sfx a b.
    FST (compute_label_offsets a) <= FST (compute_label_offsets b) /\
    (!l off. FLOOKUP (SND (compute_label_offsets a)) l = SOME off ==>
       ?old. FLOOKUP (SND (compute_label_offsets b)) l = SOME old /\ off <= old) ==>
    !l off. FLOOKUP (SND (compute_label_offsets (a ++ sfx))) l = SOME off ==>
       ?old. FLOOKUP (SND (compute_label_offsets (b ++ sfx))) l = SOME old /\ off <= old
Proof
  ho_match_mp_tac listTheory.SNOC_INDUCT >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`a`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  `FST (compute_label_offsets (a ++ sfx)) <=
   FST (compute_label_offsets (b ++ sfx))` by
    (qspec_then `a ++ sfx` strip_assume_tac compute_label_offsets_bound >>
     qspec_then `b ++ sfx` strip_assume_tac compute_label_offsets_bound >>
     qspec_then `a` strip_assume_tac compute_label_offsets_bound >>
     qspec_then `b` strip_assume_tac compute_label_offsets_bound >>
     gvs[listTheory.MAP_APPEND, listTheory.SUM_APPEND]) >>
  simp[listTheory.APPEND_SNOC, compute_label_offsets_snoc] >>
  Cases_on `x` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem offsets_splice_dominate[local]:
  EVERY (\i. ~is_data_inst i) repl /\
  (!l. ~MEM (AsmLabel l) repl) /\
  SUM (MAP symbolResolve$asm_inst_size repl) <=
  SUM (MAP symbolResolve$asm_inst_size pat) ==>
  !l off. FLOOKUP (SND (compute_label_offsets (pfx ++ repl ++ sfx))) l = SOME off ==>
    ?old. FLOOKUP (SND (compute_label_offsets (pfx ++ pat ++ sfx))) l = SOME old /\
          off <= old
Proof
  strip_tac >>
  match_mp_tac (offsets_common_suffix_dominate |> Q.SPECL
    [`sfx`, `pfx ++ repl`, `pfx ++ pat`] |> REWRITE_RULE [listTheory.APPEND_ASSOC]) >>
  conj_tac
  >- (qspec_then `pfx ++ repl` strip_assume_tac compute_label_offsets_bound >>
      qspec_then `pfx ++ pat` strip_assume_tac compute_label_offsets_bound >>
      gvs[listTheory.MAP_APPEND, listTheory.SUM_APPEND]) >>
  drule_all offsets_append_no_bindings >> simp[] >>
  metis_tac[offsets_append_dominate]
QED

Theorem symbol_encoding_downward[local]:
  a <= b /\ LENGTH (encode_num_bytes b) <= symbol_size ==>
  LENGTH (encode_num_bytes a) <= symbol_size
Proof
  strip_tac >> drule encode_num_bytes_length_bound >>
  simp[symbol_size_def] >> strip_tac >>
  irule (REWRITE_RULE [symbol_size_def] encode_num_bytes_length_le_symbol_size) >>
  decide_tac
QED

Theorem encoding_wf_membership[local]:
  asm_encoding_wf prog <=>
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    (!lbl off. FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off ==>
       LENGTH (encode_num_bytes off) <= symbol_size) /\
    (!lbl d off. MEM (AsmPushOfst lbl d) prog /\
       FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off ==>
       LENGTH (encode_num_bytes (off + d)) <= symbol_size) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32)
Proof
  simp[asm_encoding_wf_def, pairTheory.pair_case_eq] >>
  Cases_on `compute_label_offsets prog` >> simp[] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem encoding_wf_splice[local]:
  asm_splice_ok pat repl /\ asm_encoding_wf (pfx ++ pat ++ sfx) ==>
  asm_encoding_wf (pfx ++ repl ++ sfx)
Proof
  simp[asm_splice_ok_def, encoding_wf_membership, listTheory.EVERY_APPEND] >>
  strip_tac >>
  `!l off. FLOOKUP (SND (compute_label_offsets (pfx ++ repl ++ sfx))) l = SOME off ==>
     ?old. FLOOKUP (SND (compute_label_offsets (pfx ++ pat ++ sfx))) l = SOME old /\
           off <= old` by
    (match_mp_tac offsets_splice_dominate >> simp[]) >>
  rpt conj_tac
  >- (simp[listTheory.MEM_APPEND] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      irule symbol_encoding_downward >> goal_assum (drule_at Any) >>
      metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `!l off. FLOOKUP _ l = SOME off ==> ?old. _` drule >>
      strip_tac >>
      irule symbol_encoding_downward >> qexists_tac `old + d` >>
      simp[] >> metis_tac[listTheory.MEM_APPEND]) >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem data_index_shift[local]:
  (!j. j >= SUC i /\ j < SUC (LENGTH t) ==> P (EL j (h::t))) <=>
  (!j. j >= i /\ j < LENGTH t ==> P (EL j t))
Proof
  simp[Once arithmeticTheory.FORALL_NUM, arithmeticTheory.GREATER_EQ]
QED

Theorem data_at_end_cons[local]:
  asm_data_at_end (h::t) <=>
  asm_data_at_end t /\
  (!l. h = AsmDataHeader l ==> EVERY is_data_inst t)
Proof
  simp[asm_data_at_end_def, Once arithmeticTheory.FORALL_NUM] >>
  simp[data_index_shift] >>
  Cases_on `h` >> simp[is_data_inst_def, listTheory.EVERY_EL] >>
  simp[Once arithmeticTheory.FORALL_NUM, is_data_inst_def] >>
  metis_tac[]
QED

Theorem data_headers_cons[local]:
  (!i. i < LENGTH (h::t) /\ is_data_inst (EL i (h::t)) ==>
     ?j l. j <= i /\ EL j (h::t) = AsmDataHeader l) <=>
  ((?l. h = AsmDataHeader l) \/
   (~is_data_inst h /\
    (!i. i < LENGTH t /\ is_data_inst (EL i t) ==>
       ?j l. j <= i /\ EL j t = AsmDataHeader l)))
Proof
  simp[Once arithmeticTheory.FORALL_NUM] >>
  eq_tac
  >- (strip_tac >> Cases_on `?l. h = AsmDataHeader l` >> simp[] >>
      conj_tac >- metis_tac[] >> rpt strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      strip_tac >> Cases_on `j` >> gvs[] >> metis_tac[]) >>
  strip_tac
  >- (gvs[] >> rpt strip_tac >> qexists_tac `0` >> simp[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `SUC j` >> simp[] >> metis_tac[]
QED

Theorem every_data_at_end[local]:
  EVERY is_data_inst t ==> asm_data_at_end t
Proof
  simp[listTheory.EVERY_EL, asm_data_at_end_def] >>
  rpt strip_tac >> Cases_on `EL i t` >> simp[] >> metis_tac[]
QED

Theorem data_discipline_cons:
  (asm_data_at_end (h::t) /\
   (!i. i < LENGTH (h::t) /\ is_data_inst (EL i (h::t)) ==>
      ?j l. j <= i /\ EL j (h::t) = AsmDataHeader l)) <=>
  (case h of AsmDataHeader l => EVERY is_data_inst t | _ =>
    ~is_data_inst h /\ asm_data_at_end t /\
    (!i. i < LENGTH t /\ is_data_inst (EL i t) ==>
       ?j l. j <= i /\ EL j t = AsmDataHeader l))
Proof
  rewrite_tac[data_at_end_cons, data_headers_cons] >>
  Cases_on `h` >> simp[is_data_inst_def] >>
  metis_tac[every_data_at_end]
QED

Theorem data_discipline_append[local]:
  !a b. EVERY (\i. ~is_data_inst i) a ==>
  ((asm_data_at_end (a ++ b) /\
    (!i. i < LENGTH (a ++ b) /\ is_data_inst (EL i (a ++ b)) ==>
       ?j l. j <= i /\ EL j (a ++ b) = AsmDataHeader l)) <=>
   (asm_data_at_end b /\
    (!i. i < LENGTH b /\ is_data_inst (EL i b) ==>
       ?j l. j <= i /\ EL j b = AsmDataHeader l)))
Proof
  Induct
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[listTheory.APPEND, data_discipline_cons] >>
  Cases_on `h` >> gvs[is_data_inst_def]
QED


Theorem data_discipline_prefix[local]:
  !a b.
  asm_data_at_end (a ++ b) /\
  (!i. i < LENGTH (a ++ b) /\ is_data_inst (EL i (a ++ b)) ==>
     ?j l. j <= i /\ EL j (a ++ b) = AsmDataHeader l) /\
  (?i. MEM i b /\ ~is_data_inst i) ==>
  EVERY (\i. ~is_data_inst i) a
Proof
  Induct >- simp[] >> rpt gen_tac >>
  pure_rewrite_tac[listTheory.APPEND] >>
  once_rewrite_tac[boolTheory.CONJ_ASSOC] >>
  pure_rewrite_tac[data_discipline_cons] >>
  Cases_on `h` >> simp[is_data_inst_def, listTheory.EVERY_APPEND]
  >- (strip_tac >> first_x_assum irule >> qexists_tac `b` >> simp[] >>
      qexists_tac `i` >> simp[])
  >- (strip_tac >> first_x_assum irule >> qexists_tac `b` >> simp[] >>
      qexists_tac `i` >> simp[])
  >- (strip_tac >> first_x_assum irule >> qexists_tac `b` >> simp[] >>
      qexists_tac `i` >> simp[])
  >- (strip_tac >> first_x_assum irule >> qexists_tac `b` >> simp[] >>
      qexists_tac `i` >> simp[])
  >- (strip_tac >> first_x_assum irule >> qexists_tac `b` >> simp[] >>
      qexists_tac `i` >> simp[]) >>
  simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]
QED

Theorem data_discipline_splice[local]:
  pat <> [] /\ EVERY (\i. ~is_data_inst i) (pat ++ repl) /\
  asm_data_at_end (pfx ++ pat ++ sfx) /\
  (!i. i < LENGTH (pfx ++ pat ++ sfx) /\ is_data_inst (EL i (pfx ++ pat ++ sfx)) ==>
     ?j l. j <= i /\ EL j (pfx ++ pat ++ sfx) = AsmDataHeader l) ==>
  asm_data_at_end (pfx ++ repl ++ sfx) /\
  (!i. i < LENGTH (pfx ++ repl ++ sfx) /\ is_data_inst (EL i (pfx ++ repl ++ sfx)) ==>
     ?j l. j <= i /\ EL j (pfx ++ repl ++ sfx) = AsmDataHeader l)
Proof
  strip_tac >>
  `?i. MEM i (pat ++ sfx) /\ ~is_data_inst i` by
    (Cases_on `pat` >> gvs[listTheory.EVERY_APPEND] >>
     qexists_tac `h` >> simp[]) >>
  `EVERY (\i. ~is_data_inst i) pfx` by
    (irule data_discipline_prefix >> qexists_tac `pat ++ sfx` >> simp[] >>
     qexists_tac `i` >> gvs[]) >>
  `EVERY (\i. ~is_data_inst i) pat /\ EVERY (\i. ~is_data_inst i) repl` by
    gvs[listTheory.EVERY_APPEND] >>
  qspecl_then [`pfx`, `pat ++ sfx`] mp_tac data_discipline_append >>
  qspecl_then [`pat`, `sfx`] mp_tac data_discipline_append >>
  qspecl_then [`pfx`, `repl ++ sfx`] mp_tac data_discipline_append >>
  qspecl_then [`repl`, `sfx`] mp_tac data_discipline_append >>
  simp[] >> metis_tac[]
QED

Theorem nondata_no_header[local]:
  EVERY (\i. ~is_data_inst i) xs ==>
  (!l. ~MEM (AsmDataHeader l) xs) /\ (!l. ~MEM (AsmDataLabel l) xs)
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[is_data_inst_def]
QED

Theorem label_options_empty[local]:
  (!l. ~MEM (AsmLabel l) xs) ==>
  FILTER IS_SOME (MAP (\i. case i of AsmLabel l => SOME l | _ => NONE) xs) = []
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  Cases_on `h` >> gvs[] >> metis_tac[]
QED

Theorem labels_unique_splice[local]:
  (!l. ~MEM (AsmLabel l) repl) /\ asm_labels_unique (pfx ++ pat ++ sfx) ==>
  asm_labels_unique (pfx ++ repl ++ sfx)
Proof
  strip_tac >> drule label_options_empty >>
  gvs[asm_labels_unique_def, listTheory.MAP_APPEND, listTheory.FILTER_APPEND_DISTRIB,
      listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem label_refs_append:
  asm_label_refs (a ++ b) = asm_label_refs a ++ asm_label_refs b
Proof
  simp[asm_label_refs_def, listTheory.MAP_APPEND, listTheory.FLAT_APPEND]
QED

Theorem splice_structural_membership[local]:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ repl ++ sfx))) /\
  asm_static_wf (pfx ++ pat ++ sfx) ==>
  (!l. MEM (AsmLabel l) (pfx ++ repl ++ sfx) ==>
       ~MEM (AsmDataHeader l) (pfx ++ repl ++ sfx)) /\
  (!l. MEM l (asm_label_refs (pfx ++ repl ++ sfx)) ==>
       MEM (AsmLabel l) (pfx ++ repl ++ sfx) \/ MEM (AsmDataHeader l) (pfx ++ repl ++ sfx)) /\
  (!l. ~MEM (AsmDataLabel l) (pfx ++ repl ++ sfx)) /\
  FILTER is_data_inst (pfx ++ repl ++ sfx) = FILTER is_data_inst (pfx ++ pat ++ sfx)
Proof
  simp[asm_splice_ok_def, listTheory.EVERY_APPEND] >> strip_tac >>
  drule nondata_no_header >> strip_tac >>
  `FILTER is_data_inst pat = [] /\ FILTER is_data_inst repl = []`
    by simp[listTheory.FILTER_EQ_NIL] >>
  `(!l. ~MEM (AsmDataHeader l) pat) /\ (!l. ~MEM (AsmDataLabel l) pat)` by
    (irule nondata_no_header >> simp[]) >>
  gvs[asm_static_wf_def, listTheory.MEM_APPEND, label_refs_append,
      listTheory.FILTER_APPEND_DISTRIB] >> metis_tac[]
QED

Theorem asm_splice_static_wf:
  asm_splice_ok pat repl ∧
  (∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ repl ++ sfx))) ∧
  asm_static_wf (pfx ++ pat ++ sfx) ⇒
  asm_static_wf (pfx ++ repl ++ sfx) ∧
  FILTER is_data_inst (pfx ++ repl ++ sfx) =
  FILTER is_data_inst (pfx ++ pat ++ sfx)
Proof
  strip_tac >>
  drule_all splice_structural_membership >> strip_tac >>
  `asm_encoding_wf (pfx ++ repl ++ sfx)` by
    (irule encoding_wf_splice >> qexists_tac `pat` >> gvs[asm_static_wf_def]) >>
  `asm_labels_unique (pfx ++ repl ++ sfx)` by
    (irule labels_unique_splice >>
     gvs[asm_splice_ok_def, asm_static_wf_def] >> qexists_tac `pat` >> simp[]) >>
  `asm_data_at_end (pfx ++ repl ++ sfx) /\
   (!i. i < LENGTH (pfx ++ repl ++ sfx) /\ is_data_inst (EL i (pfx ++ repl ++ sfx)) ==>
      ?j l. j <= i /\ EL j (pfx ++ repl ++ sfx) = AsmDataHeader l)` by
    (match_mp_tac data_discipline_splice >>
     gvs[asm_splice_ok_def, asm_static_wf_def]) >>
  simp[asm_static_wf_def]
QED

(* ===== Labels the state holds ===== *)

(* Every label in a stack value or a memory byte is in refs. With refs the
   program's label references, this holds from sym_init on, so a label
   nothing refers to is never a jump target. *)
Definition sym_state_labels_in_def:
  sym_state_labels_in refs ss ⇔
    (∀l d. MEM (Lab l d) ss.sym_stack ⇒ MEM l refs) ∧
    (∀i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l, d, j) ⇒ MEM l refs)
End

Theorem sym_set_stack_labels_in[local]:
  sym_state_labels_in refs ss ∧ (∀l d. MEM (Lab l d) stk ⇒ MEM l refs) ∧
  sym_set_stack stk ss = SymOK ss' ⇒ sym_state_labels_in refs ss'
Proof
  rw[sym_set_stack_def] >> gvs[sym_state_labels_in_def] >> metis_tac[]
QED

Theorem sym_push_lab_labels_in[local]:
  sym_state_labels_in refs ss ∧ MEM l refs ∧
  (∀l d. MEM (Lab l d) stk ⇒ MEM l refs) ∧
  sym_push_lab l d stk ss = SymOK ss' ⇒ sym_state_labels_in refs ss'
Proof
  rw[sym_push_lab_def] >> irule sym_set_stack_labels_in >>
  qpat_assum `_ = SymOK ss'` (irule_at Any) >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem sym_lift_labels_in[local]:
  sym_state_labels_in refs ss ∧
  (∀i l d j. FLOOKUP labs i = SOME (l, d, j) ⇒ MEM l refs) ∧
  sym_lift k labs ss r = SymOK ss' ⇒ sym_state_labels_in refs ss'
Proof
  Cases_on `r` >> rw[sym_lift_def] >>
  gvs[sym_state_labels_in_def, listTheory.MEM_MAP] >> rw[] >>
  metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

Theorem mem_labels_clear_lookup[local]:
  FLOOKUP (mem_labels_clear m P) i = SOME v ⇒ FLOOKUP m i = SOME v
Proof
  rw[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem flookup_fupdate_list_cases[local]:
  ∀ls fm. FLOOKUP (fm |++ ls) i = SOME v ⇒
          FLOOKUP fm i = SOME v ∨ MEM (i, v) ls
Proof
  Induct >> simp[finite_mapTheory.FUPDATE_LIST_THM] >>
  qx_gen_tac `kv` >> PairCases_on `kv` >> rpt strip_tac >>
  first_x_assum drule >> rw[finite_mapTheory.FLOOKUP_UPDATE] >> simp[]
QED

Theorem mem_label_at_lookup[local]:
  mem_label_at m off = SOME (l, d) ⇒ FLOOKUP m off = SOME (l, d, 0)
Proof
  simp[mem_label_at_def] >> Cases_on `FLOOKUP m off` >> simp[] >>
  rename1 `FLOOKUP m off = SOME e` >> PairCases_on `e` >> rw[]
QED

Theorem sym_step_concrete_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_step_concrete name ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_step_concrete_def, AllCaseEqs()] >>
  irule sym_lift_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  gvs[sym_state_labels_in_def] >> metis_tac[mem_labels_clear_lookup]
QED

Theorem sym_jump_labels_in[local]:
  sym_state_labels_in refs ss ∧
  (sym_jump p ss = SymOK ss' ∨ sym_jumpi p ss = SymOK ss') ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_jump_def, sym_jumpi_def, sym_set_stack_def, AllCaseEqs()] >>
  gvs[sym_state_labels_in_def] >> metis_tac[]
QED

Theorem sym_add_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_add p env ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_add_def, AllCaseEqs()] >>
  TRY (drule_all sym_step_concrete_labels_in >> simp[] >> NO_TAC) >>
  irule sym_push_lab_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  gvs[sym_state_labels_in_def] >> metis_tac[]
QED

Theorem fupdate_genlist_labels_in[local]:
  (∀i l d j. FLOOKUP m i = SOME (l, d, j) ⇒ MEM l refs) ∧ MEM l refs ∧
  FLOOKUP (m |++ GENLIST (λi. (off + i, (l, d, i))) n) k = SOME (l', d', j)
  ⇒ MEM l' refs
Proof
  strip_tac >> drule flookup_fupdate_list_cases >> strip_tac
  >- metis_tac[] >>
  gvs[listTheory.MEM_GENLIST]
QED

Theorem sym_mstore_cases[local]:
  sym_mstore ss = SymOK ss' ⇒
  sym_step_concrete "MSTORE" ss = SymOK ss' ∨
  ∃off l d stk.
    ss.sym_stack = Val off :: Lab l d :: stk ∧
    sym_lift 2
      (ss.sym_mem_labels |++ GENLIST (λi. (w2n off + i, (l, d, i))) 32) ss
      (asm_mstore (ss.sym_base with as_stack := [off; 0w])) = SymOK ss'
Proof
  rw[sym_mstore_def, AllCaseEqs()] >> gvs[]
QED

Theorem sym_mstore_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_mstore ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  strip_tac >> drule sym_mstore_cases >> strip_tac
  >- (drule_all sym_step_concrete_labels_in >> simp[]) >>
  `∀i l' d' j.
     FLOOKUP (ss.sym_mem_labels |++ GENLIST (λi. (w2n off + i, (l, d, i))) 32)
       i = SOME (l', d', j) ⇒ MEM l' refs`
    by (rpt strip_tac >>
        drule_at (Pos last) fupdate_genlist_labels_in >>
        disch_then irule >>
        fs[sym_state_labels_in_def] >> metis_tac[listTheory.MEM]) >>
  irule sym_lift_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  metis_tac[]
QED

Theorem sym_mload_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_mload ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_mload_def, AllCaseEqs()] >>
  TRY (drule_all sym_step_concrete_labels_in >> simp[] >> NO_TAC) >>
  drule mem_label_at_lookup >> gvs[sym_state_labels_in_def] >>
  metis_tac[]
QED

Theorem sym_codecopy_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_codecopy p env ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_codecopy_def, AllCaseEqs()] >>
  irule sym_lift_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  gvs[sym_state_labels_in_def] >> metis_tac[mem_labels_clear_lookup]
QED

Theorem sym_dup_swap_labels_in[local]:
  sym_state_labels_in refs ss ∧
  (sym_dup n ss = SymOK ss' ∨ sym_swap n ss = SymOK ss') ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_dup_def, sym_swap_def] >> irule sym_set_stack_labels_in >>
  qpat_assum `_ = SymOK ss'` (irule_at Any) >> gvs[sym_state_labels_in_def] >>
  `0 < LENGTH ss.sym_stack` by decide_tac >>
  metis_tac[listTheory.EL_MEM, listTheory.MEM_LUPDATE_E, listTheory.EL, listTheory.MEM]
QED

Theorem sym_step_op_labels_in[local]:
  sym_state_labels_in refs ss ∧ sym_step_op p env name ss = SymOK ss' ⇒
  sym_state_labels_in refs ss'
Proof
  rw[sym_step_op_def, AllCaseEqs()] >>
  imp_res_tac sym_jump_labels_in >> imp_res_tac sym_add_labels_in >>
  imp_res_tac sym_mstore_labels_in >> imp_res_tac sym_mload_labels_in >>
  imp_res_tac sym_codecopy_labels_in >> imp_res_tac sym_dup_swap_labels_in >>
  imp_res_tac sym_step_concrete_labels_in >> simp[] >>
  irule sym_set_stack_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  gvs[sym_state_labels_in_def] >> metis_tac[listTheory.MEM]
QED

Theorem mem_asm_label_refs[local]:
  (MEM (AsmPushLabel l) p ⇒ MEM l (asm_label_refs p)) ∧
  (MEM (AsmPushOfst l d) p ⇒ MEM l (asm_label_refs p))
Proof
  simp[asm_label_refs_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
       PULL_EXISTS] >>
  conj_tac >> strip_tac >> first_assum (irule_at Any) >> simp[]
QED

(* Each step keeps the labels a state holds among p's references. *)
Theorem sym_step_labels_in:
  MEM inst p ∧ sym_state_labels_in (asm_label_refs p) ss ∧
  sym_step p env inst ss = SymOK ss' ⇒
  sym_state_labels_in (asm_label_refs p) ss'
Proof
  Cases_on `inst` >> rw[sym_step_def]
  >~ [`sym_step_op`] >- metis_tac[sym_step_op_labels_in]
  >~ [`sym_set_stack`]
  >- (irule sym_set_stack_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
      imp_res_tac mem_asm_label_refs >> gvs[sym_state_labels_in_def] >>
      metis_tac[])
  >~ [`sym_push_lab`]
  >- (irule sym_push_lab_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
      imp_res_tac mem_asm_label_refs >> gvs[sym_state_labels_in_def] >>
      metis_tac[]) >>
  irule sym_lift_labels_in >> qpat_assum `_ = SymOK ss'` (irule_at Any) >>
  gvs[sym_state_labels_in_def] >> metis_tac[]
QED

Theorem sym_steps_labels_in:
  ∀j ss a. sym_state_labels_in (asm_label_refs p) ss ∧
    sym_steps p env j ss = SymOK a ⇒
    sym_state_labels_in (asm_label_refs p) a
Proof
  Induct >> simp[sym_steps_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  `MEM (EL ss.sym_base.as_pc p) p` by simp[listTheory.EL_MEM] >>
  drule_all sym_step_labels_in >> strip_tac >>
  first_x_assum irule >> qexists_tac `ss'` >> simp[]
QED

(* ===== Refinement ===== *)

Theorem splice_fetch[local]:
  pat <> [] /\ (i < LENGTH pfx \/ LENGTH pfx + LENGTH pat <= i) /\
  i < LENGTH (pfx ++ pat ++ sfx) ==>
  splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) i <
    LENGTH (pfx ++ repl ++ sfx) /\
  EL (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) i)
    (pfx ++ repl ++ sfx) = EL i (pfx ++ pat ++ sfx)
Proof
  strip_tac >> Cases_on `i < LENGTH pfx`
  >- simp[splice_pc_def, listTheory.EL_APPEND_EQN] >>
  `0 < LENGTH pat` by (Cases_on `pat` >> gvs[]) >>
  `LENGTH pfx < i` by decide_tac >>
  simp[splice_pc_def, listTheory.LENGTH_APPEND] >>
  `LENGTH pfx + LENGTH repl <= i + LENGTH repl - LENGTH pat` by decide_tac >>
  simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_APPEND] >>
  gvs[listTheory.LENGTH_APPEND]
QED

Theorem splice_pc_next[local]:
  0 < m /\ (i < k \/ k + m <= i) ==>
  splice_pc k m n (i + 1) = splice_pc k m n i + 1 /\
  (i + 1 <= k \/ k + m <= i + 1)
Proof
  rw[splice_pc_def] >> decide_tac
QED

Theorem sym_steps_base_stack[local]:
  !j ss a. ss.sym_base.as_stack = [] /\
    sym_steps p env j ss = SymOK a ==> a.sym_base.as_stack = []
Proof
  Induct >> simp[sym_steps_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  drule_all sym_step_base_stack >> strip_tac >>
  first_x_assum irule >> qexists_tac `ss'` >> simp[]
QED

Theorem sym_step_from_zero[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" ==>
  sym_step p env inst (sym_with_pc q ss) =
  sym_result_pc_add q (sym_step p env inst (sym_with_pc 0 ss))
Proof
  strip_tac >>
  mp_tac (Q.INST [`ss` |-> `sym_with_pc 0 ss`, `n` |-> `q`]
    sym_step_pc_add) >>
  simp[sym_with_pc_def]
QED

Theorem sym_step_move_ok[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
  sym_step p env inst ss = SymOK a ==>
  sym_step p env inst (sym_with_pc q ss) =
    SymOK (sym_with_pc (q + 1) a)
Proof
  strip_tac >>
  `ss = sym_with_pc ss.sym_base.as_pc ss` by simp[sym_with_pc_def] >>
  drule_all sym_step_pc_next >> strip_tac >>
  drule_all sym_step_from_zero >>
  disch_then (qspecl_then [`ss`, `q`, `p`, `env`] assume_tac) >>
  drule_all sym_step_from_zero >>
  disch_then (qspecl_then [`ss`, `ss.sym_base.as_pc`, `p`, `env`] mp_tac) >>
  simp[Once sym_with_pc_def] >>
  Cases_on `sym_step p env inst (sym_with_pc 0 ss)` >>
  gvs[sym_result_pc_add_def, sym_with_pc_def] >> strip_tac >>
  gvs[] >> rename1 `SymOK b` >> `b.sym_base.as_pc = 1` by decide_tac >> simp[]
QED

Theorem sym_step_move_terminal[local]:
  inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
  sym_terminal (sym_step p env inst ss) ==>
  sym_result_rel (sym_step p env inst ss)
    (sym_step p env inst (sym_with_pc q ss))
Proof
  strip_tac >>
  drule_all sym_step_from_zero >>
  disch_then (qspecl_then [`ss`, `q`, `p`, `env`] assume_tac) >>
  drule_all sym_step_from_zero >>
  disch_then (qspecl_then [`ss`, `ss.sym_base.as_pc`, `p`, `env`] mp_tac) >>
  simp[sym_with_pc_def] >> strip_tac >>
  Cases_on `sym_step p env inst (sym_with_pc 0 ss)` >>
  gvs[sym_result_pc_add_def, sym_terminal_def, sym_with_pc_def,
      sym_result_rel_def, sym_obs_def]
QED

Theorem splice_headers[local]:
  asm_splice_ok pat repl ==>
  (!l. MEM (AsmDataHeader l) (pfx ++ pat ++ sfx) <=>
       MEM (AsmDataHeader l) (pfx ++ repl ++ sfx))
Proof
  rw[asm_splice_ok_def, listTheory.EVERY_MEM] >>
  `~MEM (AsmDataHeader l) pat /\ ~MEM (AsmDataHeader l) repl`
    by (rpt strip_tac >> first_x_assum drule >> simp[is_data_inst_def]) >>
  simp[]
QED

Theorem splice_jump_ok[local]:
  pat <> [] /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ pat ++ sfx))) /\
  (!l. ~MEM (AsmLabel l) repl) /\
  sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss /\
  sym_jump (pfx ++ pat ++ sfx) ss = SymOK a ==>
  (a.sym_base.as_pc <= LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
  sym_jump (pfx ++ repl ++ sfx) (sym_with_pc q ss) =
    SymOK (sym_with_pc
      (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)
Proof
  simp[sym_jump_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `dest` >> gvs[sym_jump_dest_def, AllCaseEqs()] >>
  rename1 `Lab lbl _` >>
  `~MEM (AsmLabel lbl) pat`
    by (strip_tac >> first_x_assum drule >>
        fs[sym_state_labels_in_def] >> metis_tac[listTheory.MEM]) >>
  mp_tac (Q.INST [`l` |-> `lbl`] splice_index_of_label) >> simp[] >>
  strip_tac >>
  gvs[sym_with_pc_def, sym_jump_dest_def] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem splice_fallthrough_ok[local]:
  pat <> [] /\
  (ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
  sym_set_stack stk ss = SymOK a ==>
  (a.sym_base.as_pc <= LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
  sym_set_stack stk
    (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       ss.sym_base.as_pc) ss) =
    SymOK (sym_with_pc
      (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)
Proof
  strip_tac >> `0 < LENGTH pat` by (Cases_on `pat` >> gvs[]) >>
  drule splice_pc_next >>
  disch_then (qspecl_then [`LENGTH repl`, `LENGTH pfx`, `ss.sym_base.as_pc`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[sym_set_stack_def, asmSemTheory.asm_next_def, sym_with_pc_def]
QED

Theorem splice_inst_step_ok[local]:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ pat ++ sfx))) /\
  sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss /\
  (ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
  sym_step (pfx ++ pat ++ sfx) env inst ss = SymOK a ==>
  (a.sym_base.as_pc <= LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
  sym_step (pfx ++ repl ++ sfx) env inst
    (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       ss.sym_base.as_pc) ss) =
    SymOK (sym_with_pc
      (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `pat <> [] /\ (!l. ~MEM (AsmLabel l) repl)` by fs[asm_splice_ok_def] >>
  Cases_on `inst = AsmOp "JUMP"`
  >- (gvs[sym_step_def, sym_step_op_def] >> drule_all splice_jump_ok >>
      disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc` mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  Cases_on `inst = AsmOp "JUMPI"`
  >- (gnvs[sym_step_def, sym_step_op_def] >>
      Cases_on `ss.sym_stack` >> gnvs[sym_jumpi_def] >>
      rename1 `ss.sym_stack = dest :: rest` >>
      Cases_on `rest` >> gnvs[sym_jumpi_def] >>
      rename1 `ss.sym_stack = dest :: cond :: stk` >>
      Cases_on `cond` >> gnvs[sym_jumpi_def] >>
      rename1 `Val c` >> Cases_on `c = 0w`
      >- (gvs[] >>
          irule (SRULE [arithmeticTheory.ADD_COMM] splice_fallthrough_ok) >>
          simp[] >> metis_tac[]) >>
      `sym_jump (pfx ++ pat ++ sfx) (ss with sym_stack := dest :: stk) = SymOK a`
        by (gvs[sym_jump_def, sym_jumpi_def, AllCaseEqs()]) >>
      `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx))
         (ss with sym_stack := dest :: stk)`
        by (fs[sym_state_labels_in_def] >> metis_tac[listTheory.MEM]) >>
      drule_all splice_jump_ok >>
      disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc` mp_tac) >>
      gvs[sym_jump_def, sym_jumpi_def, sym_with_pc_def, AllCaseEqs()]) >>
  `0 < LENGTH pat` by (Cases_on `pat` >> gvs[]) >>
  `a.sym_base.as_pc = ss.sym_base.as_pc + 1` by metis_tac[sym_step_pc_next] >>
  drule splice_pc_next >>
  disch_then (qspecl_then [`LENGTH repl`, `LENGTH pfx`, `ss.sym_base.as_pc`] mp_tac) >>
  simp[] >> strip_tac >>
  `!x. sym_step (pfx ++ repl ++ sfx) env inst x =
       sym_step (pfx ++ pat ++ sfx) env inst x`
    by (gen_tac >> irule sym_step_prog_cong >> simp[splice_headers]) >>
  simp[] >>
  drule_all sym_step_move_ok >>
  disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
    ss.sym_base.as_pc` mp_tac) >> gvs[]
QED

Theorem sym_jumps_not_terminal[local]:
  ~sym_terminal (sym_jump p ss) /\ ~sym_terminal (sym_jumpi p ss)
Proof
  namedCases_on `ss.sym_stack` ["", "dest rest"] >>
  simp[sym_jump_def, sym_jumpi_def, sym_terminal_def] >>
  namedCases_on `rest` ["", "cond stk"] >>
  simp[sym_terminal_def]
  >- (Cases_on `sym_jump_dest p dest` >> simp[sym_terminal_def]) >>
  Cases_on `cond` >> simp[sym_terminal_def, sym_set_stack_def] >>
  Cases_on `sym_jump_dest p dest` >> simp[sym_terminal_def] >>
  rw[sym_terminal_def]
QED

Theorem splice_inst_step_terminal[local]:
  asm_splice_ok pat repl /\
  sym_terminal (sym_step (pfx ++ pat ++ sfx) env inst ss) ==>
  sym_result_rel (sym_step (pfx ++ pat ++ sfx) env inst ss)
    (sym_step (pfx ++ repl ++ sfx) env inst (sym_with_pc q ss))
Proof
  strip_tac >>
  `inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI"`
    by (conj_tac >> strip_tac >>
        gvs[sym_step_def, sym_step_op_def, sym_jumps_not_terminal]) >>
  `!x. sym_step (pfx ++ repl ++ sfx) env inst x =
       sym_step (pfx ++ pat ++ sfx) env inst x`
    by (gen_tac >> irule sym_step_prog_cong >> simp[splice_headers]) >>
  simp[] >> irule sym_step_move_terminal >> simp[]
QED

Theorem splice_run_terminal[local]:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ pat ++ sfx))) /\
  asm_window_refines pfx pat repl sfx /\ asm_static_wf (pfx ++ pat ++ sfx) ==>
  !fuel env ss.
    ss.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss /\
    (ss.sym_base.as_pc <= LENGTH pfx \/
      LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
    sym_terminal (sym_run (pfx ++ pat ++ sfx) env fuel ss) ==>
    ?fuel'. sym_result_rel (sym_run (pfx ++ pat ++ sfx) env fuel ss)
      (sym_run (pfx ++ repl ++ sfx) env fuel'
        (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
          ss.sym_base.as_pc) ss))
Proof
  strip_tac >> completeInduct_on `fuel` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ss.sym_base.as_pc = LENGTH pfx`
  >- suspend "window" >>
  (Q.SUBGOAL_THEN `ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc` assume_tac
    >- decide_tac) >>
  `pat <> []` by fs[asm_splice_ok_def] >>
  `fuel <> 0 /\ ss.sym_base.as_pc < LENGTH (pfx ++ pat ++ sfx)`
    by (Cases_on `fuel = 0` >>
        fs[Once sym_run_def, sym_terminal_def] >>
        Cases_on `ss.sym_base.as_pc >= LENGTH (pfx ++ pat ++ sfx)` >>
        fs[sym_terminal_def]) >>
  drule_all splice_fetch >> strip_tac >>
  suspend "outside"
QED

Resume splice_run_terminal[window]:
  `sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
     ss.sym_base.as_pc) ss = ss`
    by (simp[splice_pc_def] >>
        qpat_x_assum `ss.sym_base.as_pc = LENGTH pfx`
          (fn th => rewrite_tac[GSYM th]) >> simp[sym_with_pc_def]) >>
  simp[] >>
  qpat_x_assum `asm_window_refines _ _ _ _` mp_tac >>
  simp[asm_window_refines_def] >>
  disch_then (qspecl_then [`env`, `ss`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `j` (qx_choose_then `j'` strip_assume_tac)) >>
  drule sym_run_terminal_steps >>
  disch_then (qspec_then `j` strip_assume_tac) >>
  Cases_on `?a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a`
  >- suspend "window_ok" >>
  `sym_run (pfx ++ pat ++ sfx) env fuel ss =
   sym_steps (pfx ++ pat ++ sfx) env j ss` by metis_tac[] >>
  `sym_result_rel (sym_steps (pfx ++ pat ++ sfx) env j ss)
     (sym_steps (pfx ++ repl ++ sfx) env j' ss)` by metis_tac[] >>
  drule sym_result_rel_terminal >> strip_tac >>
  qexists_tac `j'` >>
  `sym_run (pfx ++ repl ++ sfx) env j' ss =
     sym_steps (pfx ++ repl ++ sfx) env j' ss`
    by (irule sym_run_steps_stop >> simp[] >>
        Cases_on `sym_steps (pfx ++ repl ++ sfx) env j' ss` >>
        gvs[sym_terminal_def]) >> simp[]
QED

Resume splice_run_terminal[window_ok]:
  qpat_x_assum `?a. _` (qx_choose_then `a` assume_tac) >>
  `j < fuel /\ sym_run (pfx ++ pat ++ sfx) env fuel ss =
      sym_run (pfx ++ pat ++ sfx) env (fuel - j) a` by metis_tac[] >>
  `sym_steps (pfx ++ repl ++ sfx) env j' ss =
     SymOK (sym_with_pc
       (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)`
    by metis_tac[] >>
  `a.sym_base.as_stack = []` by metis_tac[sym_steps_base_stack] >>
  `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) a`
    by metis_tac[sym_steps_labels_in] >>
  first_x_assum (qspec_then `fuel - j` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`env`, `a`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `j' + f` >>
  drule sym_run_steps_ok >> disch_then (qspec_then `f` mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume splice_run_terminal[outside]:
  first_x_assum (qspec_then `repl` strip_assume_tac) >>
  Cases_on `?a. sym_step (pfx ++ pat ++ sfx) env
    (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss = SymOK a`
  >- suspend "outside_ok" >>
  `sym_run (pfx ++ pat ++ sfx) env fuel ss =
     sym_step (pfx ++ pat ++ sfx) env
       (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss`
    by (simp[Once sym_run_def] >>
        Cases_on `sym_step (pfx ++ pat ++ sfx) env
          (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss` >> gvs[]) >>
  `sym_terminal (sym_step (pfx ++ pat ++ sfx) env
     (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss)` by metis_tac[] >>
  drule_all splice_inst_step_terminal >>
  disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
    ss.sym_base.as_pc` assume_tac) >>
  drule sym_result_rel_terminal >> strip_tac >>
  qexists_tac `1` >>
  Cases_on `sym_step (pfx ++ repl ++ sfx) env
    (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx))
    (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
      ss.sym_base.as_pc) ss)` >>
  gvs[sym_terminal_def, Once sym_run_def, sym_with_pc_def,
      listTheory.LENGTH_APPEND] >> simp[Once sym_run_def]
QED

Resume splice_run_terminal[outside_ok]:
  qpat_x_assum `?a. _` (qx_choose_then `a` assume_tac) >>
  drule_all splice_inst_step_ok >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.sym_base.as_stack = []` by metis_tac[sym_step_base_stack] >>
  `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) a`
    by metis_tac[sym_step_labels_in, listTheory.EL_MEM] >>
  `sym_run (pfx ++ pat ++ sfx) env fuel ss =
     sym_run (pfx ++ pat ++ sfx) env (fuel - 1) a`
    by (gnvs[listTheory.LENGTH_APPEND] >> simp[Once sym_run_def]) >>
  first_x_assum (qspec_then `fuel - 1` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`env`, `a`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `SUC f` >>
  `sym_run (pfx ++ repl ++ sfx) env (SUC f)
     (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       ss.sym_base.as_pc) ss) =
   sym_run (pfx ++ repl ++ sfx) env f
     (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       a.sym_base.as_pc) a)`
    by (gnvs[sym_with_pc_def, listTheory.LENGTH_APPEND] >>
        simp[Once sym_run_def]) >> metis_tac[]
QED

Finalise splice_run_terminal

Theorem asm_splice_window_refines:
  asm_splice_ok pat repl ∧
  (∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ pat ++ sfx))) ∧
  asm_window_refines pfx pat repl sfx ⇒
  asm_refines (pfx ++ pat ++ sfx) (pfx ++ repl ++ sfx)
Proof
  strip_tac >> simp[asm_refines_def] >> strip_tac >>
  `∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ repl ++ sfx))`
    by (gvs[asm_splice_ok_def, label_refs_append] >> metis_tac[]) >>
  `asm_static_wf (pfx ++ repl ++ sfx) /\
   FILTER is_data_inst (pfx ++ repl ++ sfx) =
     FILTER is_data_inst (pfx ++ pat ++ sfx)`
    by (irule asm_splice_static_wf >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `sym_terminal _`) splice_run_terminal >>
  simp[sym_init_def, splice_pc_def, sym_with_pc_def,
       sym_state_labels_in_def, listTheory.MEM_MAP]
QED

(* A rule's walk past an item it keeps: the induction hypothesis holds for
   every prefix, so in particular for the prefix extended by that item. *)
Theorem asm_refines_cons:
  (∀pfx. asm_refines (pfx ++ rest) (pfx ++ out)) ⇒
  ∀pfx. asm_refines (pfx ++ x :: rest) (pfx ++ x :: out)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `pfx ++ [x]` mp_tac) >>
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED
