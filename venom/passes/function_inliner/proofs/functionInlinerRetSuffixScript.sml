(*
 * Function Inliner — RET Suffix Execution Helper
 *)

Theory functionInlinerRetSuffix
Ancestors
  functionInlinerInvokeCloneHelpers

open stringTheory rich_listTheory listTheory venomStateTheory
     pairTheory indexedListsTheory

open functionInlinerInvokeCloneHelpersTheory
     functionInlinerDefsTheory functionInlinerCloneSimTheory
     functionInlinerCloneNpTheory
     venomExecSemanticsTheory venomInstTheory venomWfTheory
     stateEquivTheory

Theorem run_block_clone_ret_suffix:
  !prefix labels invoke_ops invoke_outs ret_lbl ctx fuel
   bb bb_clone sc sd ret_vals.
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    bb_well_formed bb /\
    eval_operands
      (MAP (clone_operand prefix labels)
           (LAST bb.bb_instructions).inst_operands) sd = SOME ret_vals /\
    sd.vs_inst_idx = PRE (LENGTH bb.bb_instructions) /\
    shared_globals_np sc sd /\
    ~sd.vs_halted /\
    EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
    ALL_DISTINCT invoke_outs /\
    LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands
    ==>
    ?sd'. run_block fuel ctx bb_clone sd = OK sd' /\
      sd'.vs_current_bb = ret_lbl /\
      ~sd'.vs_halted /\
      shared_globals_np sc sd' /\
      (!i. i < LENGTH (LAST bb.bb_instructions).inst_operands /\
           i < LENGTH invoke_outs ==>
           lookup_var (EL i invoke_outs) sd' = SOME (EL i ret_vals)) /\
      (!x. ~MEM x invoke_outs ==> lookup_var x sd' = lookup_var x sd)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `?insts' pidx'. rewrite_inline_insts invoke_ops invoke_outs ret_lbl
     (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
     (insts', pidx')` by metis_tac[PAIR] >>
  `bb_clone.bb_instructions = insts'` by fs[] >>
  qabbrev_tac `ret_ops = MAP (clone_operand prefix labels)
    (LAST bb.bb_instructions).inst_operands` >>
  `eval_operands ret_ops sd = SOME ret_vals` by fs[Abbr `ret_ops`] >>
  `LENGTH ret_vals = LENGTH ret_ops` by
    metis_tac[eval_operands_some_length] >>
  `LENGTH (FRONT bb.bb_instructions) = PRE (LENGTH bb.bb_instructions)` by
    simp[LENGTH_FRONT] >>
  `LENGTH ret_ops = LENGTH (LAST bb.bb_instructions).inst_operands` by
    simp[Abbr `ret_ops`] >>
  `!j. j < LENGTH ret_ops ==>
    eval_operand (EL j ret_ops) sd = SOME (EL j ret_vals)` by
    metis_tac[eval_operands_some_el] >>
  `LENGTH invoke_outs >= LENGTH ret_ops` by fs[] >>
  (* Fact A: isPREFIX for clone operand vars *)
  `!j. j < LENGTH ret_ops ==>
    !v. EL j ret_ops = Var v ==> isPREFIX prefix v` by
    suspend "isPREFIX" >>
  (* Fact B: get_instruction for ASSIGN entries *)
  `!j. j < LENGTH ret_ops ==>
    get_instruction bb_clone (PRE (LENGTH bb.bb_instructions) + j) = SOME
      <| inst_id := 0; inst_opcode := ASSIGN;
         inst_operands := [EL j ret_ops];
         inst_outputs := [EL j invoke_outs] |>` by
    suspend "get_assign" >>
  (* Fact C: get_instruction for JMP *)
  `get_instruction bb_clone
    (PRE (LENGTH bb.bb_instructions) + LENGTH ret_ops) = SOME
      <| inst_id := (LAST bb.bb_instructions).inst_id;
         inst_opcode := JMP;
         inst_operands := [Label ret_lbl]; inst_outputs := [] |>` by
    suspend "get_jmp" >>
  (* All 12 conjuncts of run_block_assigns_jmp are now in assumptions *)
  `LENGTH (LAST bb.bb_instructions).inst_operands = LENGTH ret_vals` by fs[] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  MATCH_MP_TAC run_block_assigns_jmp >>
  MAP_EVERY qexists_tac [`LENGTH ret_ops`, `ret_ops`,
    `PRE (LENGTH bb.bb_instructions)`, `prefix`,
    `(LAST bb.bb_instructions).inst_id`] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  simp[]
QED

(* ---- isPREFIX: clone_operand produces prefixed vars ---- *)
Resume run_block_clone_ret_suffix[isPREFIX]:
  rpt strip_tac >>
  `j < LENGTH (LAST bb.bb_instructions).inst_operands` by fs[] >>
  qpat_x_assum `Abbrev (ret_ops = _)` (SUBST_ALL_TAC o
    REWRITE_RULE[markerTheory.Abbrev_def]) >>
  fs[EL_MAP] >>
  metis_tac[clone_operand_var_isPREFIX]
QED

(* ---- get_assign: get_instruction for ASSIGN entries ---- *)
Resume run_block_clone_ret_suffix[get_assign]:
  rpt strip_tac >>
  `j < LENGTH (clone_instruction prefix labels
      (LAST bb.bb_instructions)).inst_operands` by
    simp[clone_instruction_def] >>
  mp_tac (Q.SPECL [`bb`, `bb_clone`, `invoke_ops`, `invoke_outs`,
    `ret_lbl`, `prefix`, `labels`, `insts'`, `pidx'`, `j`]
    get_instruction_ret_assign) >>
  impl_tac >- (rpt strip_tac >> fs[]) >>
  strip_tac >>
  `(clone_instruction prefix labels (LAST bb.bb_instructions)).inst_operands =
    ret_ops` by simp[clone_instruction_def, Abbr `ret_ops`] >>
  `PRE (LENGTH bb.bb_instructions) + j =
    LENGTH (FRONT bb.bb_instructions) + j` by fs[] >>
  fs[]
QED

(* ---- get_jmp: get_instruction for JMP ---- *)
Resume run_block_clone_ret_suffix[get_jmp]:
  mp_tac (Q.SPECL [`bb`, `bb_clone`, `invoke_ops`, `invoke_outs`,
    `ret_lbl`, `prefix`, `labels`, `insts'`, `pidx'`]
    get_instruction_ret_jmp) >>
  impl_tac >- (rpt strip_tac >> fs[]) >>
  strip_tac >>
  (* Simplify clone_instruction wrapper *)
  pop_assum (assume_tac o SIMP_RULE (srw_ss()) [clone_instruction_def]) >>
  (* Align indices: FRONT→PRE and (LAST..).inst_operands→ret_ops *)
  qpat_x_assum `LENGTH (FRONT _) = _`
    (fn front_eq => qpat_x_assum `LENGTH ret_ops = _`
      (fn len_eq => first_x_assum
        (assume_tac o REWRITE_RULE [front_eq, GSYM len_eq]))) >>
  (* Now asm: get_instruction bb_clone (PRE(..) + LENGTH ret_ops) =
              SOME (LAST .. with <|opcode:=JMP;..|>)
     Goal uses explicit record literal. Resolve with component equality. *)
  pop_assum mp_tac >> simp[instruction_component_equality]
QED

Finalise run_block_clone_ret_suffix;

val _ = export_theory();
