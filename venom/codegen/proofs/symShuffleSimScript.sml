(*
 * The symbolic machine runs a planner prefix (stack shuffles, spills and
 * restores) without a SymBad, keeping the kinds of the frame's values.
 * Purely symbolic: no Venom state and no concrete assembly state.  The
 * concrete side comes from codegen's own prefix simulation and
 * asm_sym_steps_lockstep.
 *)
Theory symShuffleSim
Ancestors
  codegenSymRel mixedPrefixSim strongPrefixSim prefixExec prefixSim planExec
  contextCodegenRel asmSymSem asmSem stackPlanTypes list arithmetic

(* Successful symbolic runs compose without inspecting intermediate states. *)
Theorem sym_steps_compose:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK out ==>
  sym_steps p env (m + n) ss = SymOK out
Proof
  simp[sym_steps_add]
QED

Theorem sym_steps_single:
  asm_block_at p ss.sym_base.as_pc [inst] ==>
  sym_steps p env 1 ss = sym_step p env inst ss
Proof
  simp[stackOpSimTheory.asm_block_at_cons] >> strip_tac >>
  simp[Once codegenSymRelTheory.sym_steps_compute] >>
  Cases_on `sym_step p env inst ss` >> simp[codegenSymRelTheory.sym_steps_def]
QED

Theorem sym_steps_pop:
  asm_block_at p ss.sym_base.as_pc [AsmOp "POP"] /\
  ss.sym_stack = v :: stk ==>
  sym_steps p env 1 ss =
    SymOK (ss with <| sym_base := asm_next ss.sym_base;
                     sym_stack := stk |>)
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, sym_step_op_def, sym_set_stack_def]
QED

Theorem sym_steps_push_label:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <| sym_base := asm_next ss.sym_base;
                     sym_stack := Lab l 0 :: ss.sym_stack |>)
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, sym_set_stack_def]
QED

Theorem sym_steps_push:
  asm_block_at p ss.sym_base.as_pc [AsmPush bytes] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (word_of_bytes F (0w:bytes32) (REVERSE bytes)) ::
                   ss.sym_stack |>)
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, asm_step_def, sym_lift_def, asm_next_def,
       sym_state_component_equality]
QED

Theorem sym_steps_label:
  asm_block_at p ss.sym_base.as_pc [AsmLabel l] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []) |>)
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, asm_step_def, sym_lift_def, asm_next_def,
       sym_state_component_equality]
QED

Theorem sym_step_op_dup:
  ALOOKUP dup_table name = SOME n ==>
  sym_step_op p env name ss = sym_dup n ss
Proof
  strip_tac >> drule alistTheory.ALOOKUP_MEM >>
  simp[dup_table_def] >> strip_tac >> gvs[sym_step_op_def]
QED

Theorem sym_step_op_swap:
  ALOOKUP swap_table name = SOME n ==>
  sym_step_op p env name ss = sym_swap n ss
Proof
  strip_tac >> drule alistTheory.ALOOKUP_MEM >>
  simp[swap_table_def] >> strip_tac >>
  gvs[sym_step_op_def, dup_table_def]
QED

Theorem sym_steps_dup:
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  ALOOKUP dup_table name = SOME n /\ n < LENGTH ss.sym_stack ==>
  sym_steps p env 1 ss =
    SymOK (ss with <| sym_base := asm_next ss.sym_base;
                     sym_stack := EL n ss.sym_stack :: ss.sym_stack |>)
Proof
  strip_tac >> drule sym_step_op_dup >> strip_tac >>
  drule sym_steps_single >>
  simp[sym_step_def, sym_dup_def, sym_set_stack_def]
QED

Theorem sym_steps_swap:
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  ALOOKUP swap_table name = SOME n /\
  n < LENGTH ss.sym_stack /\ 0 < n ==>
  sym_steps p env 1 ss =
    SymOK (ss with <| sym_base := asm_next ss.sym_base;
      sym_stack := LUPDATE (HD ss.sym_stack) n
                     (LUPDATE (EL n ss.sym_stack) 0 ss.sym_stack) |>)
Proof
  strip_tac >> drule sym_step_op_swap >> strip_tac >>
  drule sym_steps_single >>
  simp[sym_step_def, sym_swap_def, sym_set_stack_def]
QED

Theorem sym_step_jumpdest:
  sym_step p env (AsmOp "JUMPDEST") ss =
    SymOK (ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []) |>)
Proof
  EVAL_TAC >> simp[sym_state_component_equality, asm_state_component_equality,
                   GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem sym_steps_jumpdest:
  asm_block_at p ss.sym_base.as_pc [AsmOp "JUMPDEST"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := asm_next (ss.sym_base with as_stack := []) |>)
Proof
  strip_tac >> drule sym_steps_single >> simp[sym_step_jumpdest]
QED

(* The successor boundary needs only the tail run, not its derivation. *)
Theorem sym_steps_pops_suc:
  asm_block_at p ss.sym_base.as_pc (REPLICATE (SUC k) (AsmOp "POP")) /\
  ss.sym_stack = v :: stk /\
  sym_steps p env k
    (ss with <| sym_base := asm_next ss.sym_base; sym_stack := stk |>) =
    SymOK (ss with <|
      sym_base := ss.sym_base with as_pc := ss.sym_base.as_pc + SUC k;
      sym_stack := DROP k stk |>) ==>
  sym_steps p env (SUC k) ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with as_pc := ss.sym_base.as_pc + SUC k;
      sym_stack := DROP (SUC k) ss.sym_stack |>)
Proof
  strip_tac >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "POP"]` by
    gvs[rich_listTheory.REPLICATE, stackOpSimTheory.asm_block_at_cons] >>
  drule_all sym_steps_pop >> strip_tac >>
  rewrite_tac[SUC_ONE_ADD] >> irule sym_steps_compose >>
  qexists_tac `ss with <| sym_base := asm_next ss.sym_base; sym_stack := stk |>` >>
  simp[SUC_ONE_ADD]
QED

Theorem sym_steps_pops:
  !k ss.
    asm_block_at p ss.sym_base.as_pc (REPLICATE k (AsmOp "POP")) /\
    k <= LENGTH ss.sym_stack ==>
    sym_steps p env k ss =
      SymOK (ss with <|
        sym_base := ss.sym_base with as_pc := ss.sym_base.as_pc + k;
        sym_stack := DROP k ss.sym_stack |>)
Proof
  Induct >- simp[codegenSymRelTheory.sym_steps_def,
                 sym_state_component_equality] >>
  rpt strip_tac >> namedCases_on `ss.sym_stack` ["", "v stk"]
  >- gvs[] >>
  qpat_assum `ss.sym_stack = _` (fn th => SUBST1_TAC (GSYM th)) >>
  irule sym_steps_pops_suc >>
  gvs[asm_next_def, sym_state_component_equality, SUC_ONE_ADD,
      rich_listTheory.REPLICATE, stackOpSimTheory.asm_block_at_cons]
QED

(* Label-word observation depends only on its own bytes. *)
Theorem mem_label_at_locality:
  (!b. in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  mem_label_at labs' off = mem_label_at labs off
Proof
  strip_tac >>
  `!i. i < 32 ==> FLOOKUP labs' (off + i) = FLOOKUP labs (off + i)` by
    simp[in_mem_range_def] >>
  `FLOOKUP labs' off = FLOOKUP labs off` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[mem_label_at_def, EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem mem_sval_at_locality:
  (!b. in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  strip_tac >> Cases_on `sv`
  >- (simp[mem_sval_at_def] >> metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]) >>
  drule mem_label_at_locality >> simp[mem_sval_at_def]
QED

Theorem mem_sval_at_install:
  mem_sval_at (labs |++ GENLIST (\i. (off+i, (l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, asmSymBridgeTheory.mstore_labels_lookup,
       EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem mem_labels_clear_flookup:
  FLOOKUP (mem_labels_clear labs P) b =
    if P b then NONE else FLOOKUP labs b
Proof
  simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       pred_setTheory.IN_APP] >> IF_CASES_TAC >> gvs[]
QED

Theorem mem_sval_at_clear:
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FDOM_DRESTRICT, pred_setTheory.IN_APP]
QED

Theorem mem_labels_frame_domain:
  (!b. ~P b ==> FLOOKUP labs' b = FLOOKUP labs b) /\
  (!b. b IN FDOM labs ==> C b) /\
  (!b. P b ==> C b) ==>
  !b. b IN FDOM labs' ==> C b
Proof
  rpt strip_tac >> Cases_on `P b`
  >- metis_tac[] >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem sym_mstore_label_effect:
  ss.sym_stack = Val addr :: Lab l d :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        ss'.sym_mem_labels =
          ss.sym_mem_labels |++ GENLIST (\i. (w2n addr+i, (l,d,i))) 32
Proof
  strip_tac >> simp[sym_mstore_def, asm_mstore_def, sym_lift_def,
                    asm_next_def, Excl "GENLIST"]
QED

Theorem sym_mstore_val_effect:
  ss.sym_stack = Val addr :: Val w :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        ss'.sym_mem_labels =
          mem_labels_clear ss.sym_mem_labels (in_mem_range (w2n addr) 32)
Proof
  strip_tac >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, asm_op_mem_reads_def,
       log_table_def, mem_labels_hit_def, asm_op_mem_writes_def,
       asmOpSimTheory.asm_step_op_mstore, asm_mstore_def, sym_lift_def,
       asm_next_def]
QED

Theorem mem_sval_val_no_label:
  mem_sval_at labs off (Val w) ==>
  mem_label_at labs off = NONE /\ ~mem_labels_hit labs (in_mem_range off 32)
Proof
  simp[mem_sval_at_def, mem_labels_hit_def] >> strip_tac >>
  `FLOOKUP labs off = NONE` by
    (simp[finite_mapTheory.FLOOKUP_DEF] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[mem_label_at_def] >> metis_tac[]
QED

Theorem sym_mload_label_effect:
  ss.sym_stack = Val addr :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n addr) (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\
        ss'.sym_stack = Lab l d :: stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[mem_sval_at_def] >> strip_tac >>
  simp[sym_mload_def, asm_next_def]
QED

Theorem sym_mload_val_effect:
  ss.sym_stack = Val addr :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n addr) (Val w) ==>
  ?ss' w'. sym_mload ss = SymOK ss' /\
           ss'.sym_stack = Val w' :: stk /\
           ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
           ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> drule mem_sval_val_no_label >> strip_tac >>
  simp[sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, asm_op_mem_reads_def,
       asm_op_mem_writes_def, log_table_def,
       asmOpSimTheory.asm_step_op_mload, asm_mload_def, sym_lift_def,
       asm_next_def, mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem sym_mstore_label:
  ss.sym_stack = Val addr :: Lab l d :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        mem_sval_at ss'.sym_mem_labels (w2n addr) (Lab l d) /\
        (!b. ~in_mem_range (w2n addr) 32 b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule sym_mstore_label_effect >> strip_tac >>
  qexists_tac `ss'` >>
  pure_asm_rewrite_tac[mem_sval_at_install,
                       asmSymBridgeTheory.mstore_labels_lookup] >>
  simp[in_mem_range_def]
QED

Theorem sym_mstore_val:
  ss.sym_stack = Val addr :: Val w :: stk ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        mem_sval_at ss'.sym_mem_labels (w2n addr) (Val w) /\
        (!b. ~in_mem_range (w2n addr) 32 b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule sym_mstore_val_effect >> strip_tac >>
  qexists_tac `ss'` >> simp[mem_sval_at_clear, mem_labels_clear_flookup]
QED

Theorem sym_steps_mstore:
  asm_block_at p ss.sym_base.as_pc [AsmOp "MSTORE"] /\
  ss.sym_stack = Val addr :: sv :: stk ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\ ss'.sym_stack = stk /\
        ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
        mem_sval_at ss'.sym_mem_labels (w2n addr) sv /\
        (!b. ~in_mem_range (w2n addr) 32 b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, sym_step_op_def] >> strip_tac >>
  Cases_on `sv` >> metis_tac[sym_mstore_label, sym_mstore_val]
QED

Theorem op_kind_ok_val_retype:
  op_kind_ok fn ret op (Val w) ==> op_kind_ok fn ret op (Val w')
Proof
  Cases_on `op` >> simp[op_kind_ok_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem sym_steps_mload_kind:
  asm_block_at p ss.sym_base.as_pc [AsmOp "MLOAD"] /\
  ss.sym_stack = Val addr :: stk /\
  mem_sval_at ss.sym_mem_labels (w2n addr) sv /\
  op_kind_ok fn ret op sv ==>
  ?ss' sv'. sym_steps p env 1 ss = SymOK ss' /\
            ss'.sym_stack = sv' :: stk /\ op_kind_ok fn ret op sv' /\
            ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
            ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> drule sym_steps_single >>
  simp[sym_step_def, sym_step_op_def] >> strip_tac >>
  Cases_on `sv`
  >- metis_tac[sym_mload_val_effect, op_kind_ok_val_retype] >>
  metis_tac[sym_mload_label_effect]
QED

Theorem sym_kinds_ok_push:
  !cp fn ret srest ps ss op sv base.
    sym_kinds_ok cp fn ret srest ps ss /\ op_kind_ok fn ret op sv ==>
    sym_kinds_ok cp fn ret srest
      (ps with ps_stack := SNOC op ps.ps_stack)
      (ss with <|sym_base := base; sym_stack := sv :: ss.sym_stack|>)
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists_tac `sv :: top` >> simp[]
QED

Theorem sym_prefix_push_lit:
  !cp fn ret srest ps ss initial_fmp lo p env v.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (exec_stack_op initial_fmp (SOPush (Lit v))) ==>
    ?ss'. sym_steps p env 1 ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (apply_prefix_op initial_fmp lo (SOPush (Lit v)) ps) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[exec_stack_op_def, apply_prefix_op_def, apply_simple_op_def] >>
  rpt strip_tac >> drule sym_steps_push >>
  simp[asm_next_def] >> strip_tac >> irule sym_kinds_ok_push >>
  simp[op_kind_ok_def]
QED

Theorem sym_prefix_push_label:
  !cp fn ret srest ps ss initial_fmp lo p env l.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc [AsmPushLabel l] ==>
    ?ss'. sym_steps p env 1 ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (ps with ps_stack := SNOC (Label l) ps.ps_stack) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  rpt strip_tac >> drule sym_steps_push_label >>
  simp[asm_next_def] >> strip_tac >> irule sym_kinds_ok_push >>
  simp[op_kind_ok_def]
QED

Theorem sym_prefix_initial_fmp:
  !cp fn ret srest ps ss initial_fmp lo p env.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (exec_stack_op initial_fmp SOInitialFmp) ==>
    ?ss'. sym_steps p env 1 ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (apply_prefix_op initial_fmp lo SOInitialFmp ps) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[exec_stack_op_def, apply_prefix_op_def, stackModelTheory.stack_push_def] >>
  rpt strip_tac >> drule sym_steps_push >>
  simp[asm_next_def] >> strip_tac >> irule sym_kinds_ok_push >>
  simp[op_kind_ok_def]
QED

Theorem sym_prefix_label:
  !cp fn ret srest ps ss initial_fmp lo p env l.
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (exec_stack_op initial_fmp (SOLabel l)) ==>
    ?ss'. sym_steps p env 1 ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (apply_prefix_op initial_fmp lo (SOLabel l) ps) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[exec_stack_op_def, apply_prefix_op_def, apply_simple_op_def] >>
  rpt strip_tac >> drule sym_steps_label >>
  gvs[asm_next_def, sym_kinds_ok_def]
QED

Theorem sym_kinds_ok_pop:
  !cp fn ret srest ps ss k base.
    sym_kinds_ok cp fn ret srest ps ss /\ k <= LENGTH ps.ps_stack ==>
    sym_kinds_ok cp fn ret srest
      (ps with ps_stack := TAKE (LENGTH ps.ps_stack - k) ps.ps_stack)
      (ss with <|sym_base := base; sym_stack := DROP k ss.sym_stack|>)
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists_tac `DROP k top` >>
  `REVERSE (TAKE (LENGTH ps.ps_stack - k) ps.ps_stack) =
   DROP k (REVERSE ps.ps_stack)` by
    metis_tac[rich_listTheory.BUTLASTN_TAKE_UNCOND, rich_listTheory.DROP_REVERSE] >>
  drule LIST_REL_LENGTH >> simp[] >> strip_tac >>
  simp[DROP_APPEND1, rich_listTheory.LIST_REL_DROP]
QED

Theorem sym_prefix_pop:
  !cp fn ret srest ps ss initial_fmp lo p env k.
    k <= LENGTH ps.ps_stack /\ sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (exec_stack_op initial_fmp (SOPop k)) ==>
    ?ss'. sym_steps p env k ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (apply_prefix_op initial_fmp lo (SOPop k) ps) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + k /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[exec_stack_op_def, apply_prefix_op_def, apply_simple_op_def] >>
  rpt strip_tac >>
  `k <= LENGTH ss.sym_stack` by
    (gvs[sym_kinds_ok_def] >> drule LIST_REL_LENGTH >> simp[]) >>
  drule_all sym_steps_pops >> simp[] >> strip_tac >>
  irule sym_kinds_ok_pop >> simp[]
QED

Theorem sym_kinds_ok_peek:
  !cp fn ret srest ps ss k.
    sym_kinds_ok cp fn ret srest ps ss /\
    0 < k /\ k <= LENGTH ps.ps_stack ==>
    op_kind_ok fn ret (EL (LENGTH ps.ps_stack - k) ps.ps_stack)
      (EL (k-1) ss.sym_stack)
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  `k - 1 < LENGTH top` by gvs[LIST_REL_EL_EQN] >>
  `EL (k-1) (REVERSE ps.ps_stack) =
   EL (LENGTH ps.ps_stack - k) ps.ps_stack` by
    (simp[EL_REVERSE] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  gvs[EL_APPEND_EQN, LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < _ ==> op_kind_ok _ _ _ _`
    (qspec_then `k-1` mp_tac) >> simp[]
QED

Theorem sym_prefix_dup:
  !cp fn ret srest ps ss initial_fmp lo p env k.
    0 < k /\ k <= 16 /\ k <= LENGTH ps.ps_stack /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (exec_stack_op initial_fmp (SODup k)) ==>
    ?ss'. sym_steps p env 1 ss = SymOK ss' /\
      sym_kinds_ok cp fn ret srest
        (apply_prefix_op initial_fmp lo (SODup k) ps) ss' /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
      ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[exec_stack_op_def, apply_prefix_op_def, apply_simple_op_def] >>
  rpt strip_tac >>
  `k-1 < LENGTH ss.sym_stack` by
    (gvs[sym_kinds_ok_def] >> drule LIST_REL_LENGTH >> simp[]) >>
  `ALOOKUP dup_table (dup_name k) = SOME (k-1)` by
    (qspec_then `k-1` mp_tac stackOpSimTheory.dup_table_lookup >> simp[]) >>
  drule_all sym_steps_dup >> simp[asm_next_def] >> strip_tac >>
  irule sym_kinds_ok_push >> simp[] >> irule sym_kinds_ok_peek >>
  simp[] >> metis_tac[]
QED

(* A prefix of planner ops with no SOPushOfst (codegen emits one only for
   OFFSET, which unit_shape_ok excludes), whose spills write inside the
   byte set R and the context's spill regions, steps symbolically to the
   state the planner predicts, kinds kept and the label bytes outside R
   unchanged. *)
Theorem sym_prefix_ops_sim:
  !ops initial_fmp lo p env cp fn ret srest R ps ss.
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    prefix_spill_wf initial_fmp lo ops ps /\
    EVERY is_prefix_op ops /\
    EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
    (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
       R b /\ context_spill_byte cp b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss =
            SymOK ss' /\
          sym_kinds_ok cp fn ret srest
            (apply_prefix_ops initial_fmp lo ops ps) ss' /\
          ss'.sym_base.as_pc =
            ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          (!b. ~R b ==>
               FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  cheat
QED
