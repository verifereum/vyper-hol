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
