(*
 * Function Inliner — Call Site Simulation Helpers
 *
 * Structural helpers for inline_call_site: block lookup, fn_no_alloca
 * preservation, execution_equiv helpers, same-ctx result_equiv.
 *)

Theory functionInlinerCallSimHelpers
Ancestors
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim functionInlinerCloneExec
  functionInlinerBlockSplit
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory pred_setTheory

open functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerCalleeSimTheory
     functionInlinerCloneExecTheory functionInlinerBlockSplitTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory

(* ================================================================
   Re-exports
   ================================================================ *)

Theorem renumber_fn_inst_ids_correct =
  functionInlinerInlineTheory.renumber_fn_inst_ids_correct;

Theorem run_function_zero[local,simp]:
  !ctx fn s. run_function 0 ctx fn s = Error "out of fuel"
Proof
  ONCE_REWRITE_TAC[run_function_def] >> simp[]
QED

Theorem result_equiv_error[local,simp]:
  !fresh e1 e2. result_equiv fresh (Error e1) (Error e2)
Proof
  simp[result_equiv_def]
QED

(* ================================================================
   vs_labels preservation through run_block
   ================================================================ *)

(* step_inst preserves vs_labels; run_block is a sequence of step_inst calls,
   so vs_labels is preserved through the whole block. *)
Theorem run_block_preserves_labels:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     run_block f c bb st = OK st' ==>
     st'.vs_labels = st.vs_labels`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx >= LENGTH bb.bb_instructions` >- (
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >> simp[get_instruction_def]
  ) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[] >- (
    Cases_on `v.vs_halted` >> gvs[] >>
    metis_tac[step_inst_preserves_labels_always]
  ) >>
  strip_tac >>
  imp_res_tac step_inst_preserves_labels_always >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
  (impl_tac >- simp[Abbr `idx`]) >>
  disch_then (qspecl_then [`f`, `c`,
    `v with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
  simp[]
QED

(* ================================================================
   shared_globals_np helpers
   ================================================================ *)

Theorem shared_globals_np_refl[local,simp]:
  !s. shared_globals_np s s
Proof
  rw[shared_globals_np_def]
QED

Theorem shared_globals_np_trans:
  !s1 s2 s3.
    shared_globals_np s1 s2 /\ shared_globals_np s2 s3 ==>
    shared_globals_np s1 s3
Proof
  rw[shared_globals_np_def]
QED

Theorem execution_equiv_shared_globals_np[local]:
  !vars s1 s2.
    execution_equiv vars s1 s2 ==> shared_globals_np s1 s2
Proof
  rw[execution_equiv_def, shared_globals_np_def]
QED

Theorem state_equiv_shared_globals_np:
  !vars s1 s2.
    state_equiv vars s1 s2 ==> shared_globals_np s1 s2
Proof
  rw[state_equiv_def] >> metis_tac[execution_equiv_shared_globals_np]
QED

(* result_equiv implies lift_result (state_equiv) shared_globals_np *)
Theorem result_equiv_weaken_terminal:
  !vars r1 r2.
    result_equiv vars r1 r2 ==>
    lift_result (state_equiv vars) shared_globals_np r1 r2
Proof
  gen_tac >> Cases >> Cases >>
  simp[result_equiv_def, lift_result_def] >>
  rw[execution_equiv_def, shared_globals_np_def]
QED

(* lift_result (state_equiv) shared_globals_np: Error case *)
Theorem lift_result_error[local,simp]:
  !R1 R2 e1 e2. lift_result R1 R2 (Error e1) (Error e2)
Proof
  simp[lift_result_def]
QED

Theorem resolve_phi_MEM:
  !prev_bb ops op. resolve_phi prev_bb ops = SOME op ==> MEM op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >> rw[] >> metis_tac[]
QED

Triviality resolve_phi_no_label[local]:
  !prev ops. ~MEM (Label prev) ops ==> resolve_phi prev ops = NONE
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def]
QED

(* ================================================================
   Section 1: Block lookup helpers for inline_call_site
   ================================================================ *)

Theorem lookup_block_APPEND:
  !lbl xs ys.
    lookup_block lbl (xs ++ ys) =
    case lookup_block lbl xs of
      SOME bb => SOME bb
    | NONE => lookup_block lbl ys
Proof
  rw[lookup_block_def] >>
  Induct_on `xs` >> simp[FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> simp[]
QED

Theorem lookup_block_replace_eq:
  !lbl new_bb bbs.
    new_bb.bb_label = lbl /\
    (?bb. lookup_block lbl bbs = SOME bb) ==>
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, replace_block_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = new_bb.bb_label` >> gvs[] >>
  gvs[lookup_block_def, replace_block_def]
QED

Theorem lookup_block_replace_neq:
  !lbl other new_bb bbs.
    lbl <> other /\ new_bb.bb_label = other ==>
    lookup_block lbl (replace_block other new_bb bbs) =
    lookup_block lbl bbs
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, replace_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.bb_label = new_bb.bb_label` >> gvs[] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def, replace_block_def]
QED

(* lookup_block on a singleton list *)
Theorem lookup_block_singleton[local,simp]:
  !lbl bb.
    lookup_block lbl [bb] =
    if bb.bb_label = lbl then SOME bb else NONE
Proof
  rw[lookup_block_def, FIND_thm]
QED

(* ================================================================
   Section 2: fn_no_alloca preservation
   ================================================================ *)

Triviality FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

(* clone_function preserves no-alloca *)
Theorem clone_function_no_alloca[local]:
  !prefix fn.
    fn_no_alloca fn ==>
    fn_no_alloca (clone_function prefix fn)
Proof
  rw[fn_no_alloca_def, clone_function_def, LET_THM,
     clone_basic_block_def, EVERY_MEM, MEM_MAP] >>
  gvs[MEM_MAP] >> res_tac
QED

(* rewrite_inline_inst preserves no-alloca *)
Theorem rewrite_inline_inst_no_alloca[local]:
  !invoke_ops invoke_outs return_label inst param_idx insts pi'.
    (rewrite_inline_inst invoke_ops invoke_outs return_label
       inst param_idx = (insts, pi')) /\
    inst.inst_opcode <> ALLOCA ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) insts
Proof
  rw[rewrite_inline_inst_def, LET_THM] >> gvs[] >>
  simp[EVERY_APPEND, EVERY_MEM, indexedListsTheory.MEM_MAPi] >>
  rpt strip_tac >> gvs[]
QED

(* rewrite_inline_insts preserves no-alloca *)
Theorem rewrite_inline_insts_no_alloca[local]:
  !invoke_ops invoke_outs return_label insts param_idx insts' pi'.
    (rewrite_inline_insts invoke_ops invoke_outs return_label
       insts param_idx = (insts', pi')) /\
    EVERY (\i. i.inst_opcode <> ALLOCA) insts ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) insts'
Proof
  Induct_on `insts` >> rw[rewrite_inline_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[EVERY_APPEND] >> conj_tac
  >- (irule rewrite_inline_inst_no_alloca >> metis_tac[])
  >> (first_x_assum irule >> metis_tac[])
QED

(* rewrite_inline_blocks preserves no-alloca *)
Theorem rewrite_inline_blocks_no_alloca[local]:
  !invoke_ops invoke_outs return_label bbs param_idx bbs' pi'.
    (rewrite_inline_blocks invoke_ops invoke_outs return_label
       bbs param_idx = (bbs', pi')) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions) bbs'
Proof
  Induct_on `bbs` >> rw[rewrite_inline_blocks_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  conj_tac
  >- (gvs[rewrite_inline_block_def, LET_THM] >> pairarg_tac >> gvs[] >>
      irule rewrite_inline_insts_no_alloca >> metis_tac[])
  >> (first_x_assum irule >> metis_tac[])
QED

(* replace_block preserves EVERY on blocks *)
Theorem replace_block_every_no_alloca[local]:
  !lbl new_bb bbs.
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions) bbs /\
    EVERY (\i. i.inst_opcode <> ALLOCA) new_bb.bb_instructions ==>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions)
      (replace_block lbl new_bb bbs)
Proof
  simp[replace_block_def, EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rw[] >> res_tac >> gvs[] >> metis_tac[]
QED

(* Helper for the replace_block subgoal *)
Triviality inline_call_site_no_alloca_replace[local]:
  !caller bb_lbl x idx lbl_expr.
    fn_no_alloca caller /\
    lookup_block bb_lbl caller.fn_blocks = SOME x /\
    lbl_expr.inst_opcode <> ALLOCA ==>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions)
      (replace_block bb_lbl
        (x with bb_instructions :=
          TAKE idx x.bb_instructions ++ [lbl_expr]) caller.fn_blocks)
Proof
  rpt strip_tac >> irule replace_block_every_no_alloca >>
  gvs[fn_no_alloca_def] >>
  simp[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
  imp_res_tac lookup_block_MEM >> gvs[EVERY_MEM] >> res_tac >>
  gvs[EVERY_MEM] >> imp_res_tac MEM_TAKE >> res_tac
QED

(* Helper for the DROP subgoal *)
Triviality inline_call_site_no_alloca_drop[local]:
  !caller bb_lbl x idx.
    fn_no_alloca caller /\
    lookup_block bb_lbl caller.fn_blocks = SOME x ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) (DROP (idx + 1) x.bb_instructions)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >> gvs[fn_no_alloca_def, EVERY_MEM] >>
  res_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_DROP_IMP]
QED

(* inline_call_site preserves fn_no_alloca *)
Theorem inline_call_site_no_alloca:
  !prefix ret_lbl caller callee bb_lbl idx.
    fn_no_alloca caller /\ fn_no_alloca callee ==>
    fn_no_alloca (inline_call_site prefix ret_lbl caller callee bb_lbl idx)
Proof
  rw[inline_call_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp[fn_no_alloca_def, EVERY_APPEND] >> rpt strip_tac
  >| [(* replace_block TAKE++[jmp] — case 1 *)
      irule replace_block_every_no_alloca >> gvs[fn_no_alloca_def] >>
      simp[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
      imp_res_tac lookup_block_MEM >> gvs[EVERY_MEM] >> res_tac >>
      gvs[EVERY_MEM] >> imp_res_tac MEM_TAKE >> res_tac,
      (* DROP — case 1 *)
      imp_res_tac lookup_block_MEM >> gvs[fn_no_alloca_def, EVERY_MEM] >>
      res_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_DROP_IMP],
      (* rewritten_blocks — case 1 *)
      metis_tac[rewrite_inline_blocks_no_alloca,
                clone_function_no_alloca, fn_no_alloca_def],
      (* replace_block TAKE++[jmp] — case 2 *)
      irule replace_block_every_no_alloca >> gvs[fn_no_alloca_def] >>
      simp[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
      imp_res_tac lookup_block_MEM >> gvs[EVERY_MEM] >> res_tac >>
      gvs[EVERY_MEM] >> imp_res_tac MEM_TAKE >> res_tac,
      (* DROP — case 2 *)
      imp_res_tac lookup_block_MEM >> gvs[fn_no_alloca_def, EVERY_MEM] >>
      res_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_DROP_IMP],
      (* rewritten_blocks — case 2 *)
      metis_tac[rewrite_inline_blocks_no_alloca,
                clone_function_no_alloca, fn_no_alloca_def]]
QED

(* fix_inline_phis preserves fn_no_alloca *)
Theorem fix_inline_phis_no_alloca:
  !orig_lbl new_lbl ret_bb fn.
    fn_no_alloca fn ==>
    fn_no_alloca (fix_inline_phis orig_lbl new_lbl ret_bb fn)
Proof
  rw[fix_inline_phis_def, fn_no_alloca_def, LET_THM, EVERY_MEM, MEM_MAP] >>
  gvs[] >> first_x_assum drule >> rw[] >>
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `MEM bb'.bb_label (bb_succs ret_bb)` >> gvs[MEM_MAP] >>
  res_tac >> Cases_on `inst.inst_opcode = PHI` >>
  gvs[subst_label_inst_def]
QED

(* FOLDL renumber preserves EVERY on opcodes *)
Triviality foldl_renumber_every_no_alloca[local]:
  !insts n acc.
    EVERY (\i. i.inst_opcode <> ALLOCA) acc /\
    EVERY (\i. i.inst_opcode <> ALLOCA) insts ==>
    EVERY (\i. i.inst_opcode <> ALLOCA)
      (SND (FOLDL (\(id,acc') inst. (id + 1, acc' ++ [inst with inst_id := id]))
        (n,acc) insts))
Proof
  Induct >> simp[]
QED

(* renumber_block_inst_ids preserves no-alloca *)
Triviality renumber_block_preserves_no_alloca[local]:
  !n bb n' bb'.
    renumber_block_inst_ids n bb = (n', bb') /\
    EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) bb'.bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA)
    (SND (FOLDL (\(id,acc) inst. (id + 1, acc ++ [inst with inst_id := id]))
      (n,[]) bb.bb_instructions))` by
    (irule foldl_renumber_every_no_alloca >> simp[]) >>
  gvs[]
QED

(* FOLDL of renumber preserves the EVERY no-alloca property *)
Triviality foldl_renumber_preserves_no_alloca[local]:
  !bbs n0 acc.
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions) acc /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions)
      (SND (FOLDL (\(n,acc') bb.
        (\(n',bb'). (n', acc' ++ [bb']))
          (renumber_block_inst_ids n bb)) (n0,acc) bbs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[EVERY_APPEND] >>
  imp_res_tac renumber_block_preserves_no_alloca >> simp[]
QED

(* renumber preserves fn_no_alloca *)
Theorem renumber_fn_inst_ids_no_alloca[local]:
  !fn. fn_no_alloca fn ==> fn_no_alloca (renumber_fn_inst_ids fn)
Proof
  rw[fn_no_alloca_def, renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions)
    (SND (FOLDL (\(n,acc') bb.
      (\(n',bb'). (n', acc' ++ [bb']))
        (renumber_block_inst_ids n bb)) (0,[]) fn.fn_blocks))` by
    (irule foldl_renumber_preserves_no_alloca >> simp[]) >>
  gvs[]
QED

(* inline_one_site preserves fn_no_alloca *)
Theorem inline_one_site_no_alloca:
  !caller callee ist caller' ist'.
    inline_one_site caller callee ist = SOME (caller', ist') /\
    fn_no_alloca caller /\ fn_no_alloca callee ==>
    fn_no_alloca caller'
Proof
  rw[inline_one_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  irule renumber_fn_inst_ids_no_alloca >>
  TRY (irule fix_inline_phis_no_alloca) >>
  irule inline_call_site_no_alloca >> simp[]
QED

(* ================================================================
   Section 3: Structural preservation (existing)
   ================================================================ *)

Theorem inline_one_site_preserves_preconds:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    labels_fresh_above ist.is_inline_count fn ==>
    ALL_DISTINCT (fn_labels fn') /\
    labels_fresh_above ist'.is_inline_count fn'
Proof
  rpt strip_tac
  >- (
    mp_tac inline_one_site_all_distinct >>
    disch_then (qspecl_then [`fn`, `callee`, `ist`, `fn'`, `ist'`] mp_tac) >>
    (impl_tac >- (simp[] >> irule ret_lbl_not_in_mapped_callee_weak >> simp[])) >>
    simp[]
  )
  >>
  imp_res_tac labels_fresh_above_inline_one_site >>
  gvs[inline_one_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ================================================================
   Section 3b: Block lookup characterization
   ================================================================ *)

(* FIND through MAP where f preserves bb_label *)
Theorem FIND_MAP_label[local]:
  !f (bbs:basic_block list) lbl.
    (!bb. (f bb).bb_label = bb.bb_label) ==>
    FIND (\bb. bb.bb_label = lbl) (MAP f bbs) =
    OPTION_MAP f (FIND (\bb. bb.bb_label = lbl) bbs)
Proof
  gen_tac >> Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[]
QED

(* fix_inline_phis characterization: lookup preserves structure,
   only modifies PHI operands in successor blocks of return_bb *)
Theorem FIND_pred:
  !P (l:'a list) x. FIND P l = SOME x ==> P x
Proof
  gen_tac >> Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[]
QED

Theorem lookup_block_fix_inline_phis:
  !orig_lbl new_lbl ret_bb func lbl.
    lookup_block lbl (fix_inline_phis orig_lbl new_lbl ret_bb func).fn_blocks =
    case lookup_block lbl func.fn_blocks of
      NONE => NONE
    | SOME bb =>
        if MEM lbl (bb_succs ret_bb) then
          SOME (bb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst orig_lbl new_lbl inst)
                bb.bb_instructions)
        else SOME bb
Proof
  rw[fix_inline_phis_def, LET_THM, lookup_block_def] >>
  qabbrev_tac `g = \bb:basic_block.
    if MEM bb.bb_label (bb_succs ret_bb) then
      bb with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst orig_lbl new_lbl inst)
            bb.bb_instructions
    else bb` >>
  `!bb. (g bb).bb_label = bb.bb_label` by
    (rw[Abbr `g`] >> simp[]) >>
  drule_then (qspecl_then [`func.fn_blocks`, `lbl`] mp_tac) FIND_MAP_label >>
  simp[] >>
  Cases_on `FIND (\bb. bb.bb_label = lbl) func.fn_blocks` >> simp[Abbr `g`] >>
  imp_res_tac FIND_pred >> gvs[] >>
  strip_tac >> Cases_on `MEM x.bb_label (bb_succs ret_bb)` >> simp[]
QED

(* Any label built with inline_prefix n cannot appear in labels_fresh_above n *)
Theorem prefixed_label_not_in_labels:
  !n caller rest.
    labels_fresh_above n caller ==>
    ~MEM (STRCAT (inline_prefix n) rest) (fn_labels caller)
Proof
  rpt strip_tac >>
  fs[labels_fresh_above_def, EVERY_MEM] >>
  first_x_assum drule >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[IS_PREFIX_APPEND3 |> INST_TYPE [alpha |-> ``:char``]]
QED

(* ================================================================
   Section 4: Core single-site simulation
   ================================================================ *)

(* find_invoke_site guarantees the block exists *)
Theorem find_invoke_site_lookup:
  !name bbs lbl idx.
    find_invoke_site name bbs = SOME (lbl, idx) ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def, lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  Cases_on `find_invoke_idx name h.bb_instructions 0` >> gvs[] >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  first_x_assum drule >> simp[lookup_block_def, FIND_thm]
QED

(* ret_lbl is always in the result of inline_call_site *)
Theorem inline_call_site_has_ret_bb:
  !prefix ret_lbl caller callee bb_lbl idx.
    lookup_block bb_lbl caller.fn_blocks <> NONE ==>
    lookup_block ret_lbl
      (inline_call_site prefix ret_lbl caller callee bb_lbl idx).fn_blocks <>
      NONE
Proof
  rw[inline_call_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp[lookup_block_APPEND, lookup_block_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ret_bb is exactly the return block with suffix instructions *)
Triviality lookup_block_not_in_labels:
  !lbl fn.
    ~MEM lbl (fn_labels fn) ==>
    lookup_block lbl fn.fn_blocks = NONE
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >>
  imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
  fs[fn_labels_def, MEM_MAP] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem inline_call_site_ret_bb_instructions:
  !prefix ret_lbl caller callee bb_lbl idx bb ret_bb.
    lookup_block bb_lbl caller.fn_blocks = SOME bb /\
    ~MEM ret_lbl (fn_labels caller) /\
    ret_lbl <> bb_lbl /\
    lookup_block ret_lbl
      (inline_call_site prefix ret_lbl caller callee bb_lbl idx).fn_blocks =
      SOME ret_bb ==>
    ret_bb.bb_instructions = DROP (idx + 1) bb.bb_instructions /\
    ret_bb.bb_label = ret_lbl
Proof
  rw[inline_call_site_def, LET_THM] >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `bb.bb_label = bb_lbl` by imp_res_tac lookup_block_label >>
  `lookup_block ret_lbl caller.fn_blocks = NONE` by
    (irule lookup_block_not_in_labels >> first_assum ACCEPT_TAC) >>
  fs[lookup_block_APPEND, lookup_block_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac lookup_block_replace_neq >> gvs[]
QED

(* ================================================================
   Section 3b: Same-ctx execution_equiv simulation helpers

   These generalize run_block_result_equiv to handle INVOKE instructions.
   Key insight: with the same ctx, INVOKE produces identical callee states
   (since setup_callee only depends on globals which are the same under
   execution_equiv), so run_function is identical, and merge_callee_state
   preserves execution_equiv.
   ================================================================ *)

(* eval_operand depends only on variables, not bb/idx/prev_bb *)
Triviality eval_operand_execution_equiv:
  !vars op s1 s2.
    execution_equiv vars s1 s2 /\ (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >> simp[eval_operand_def, execution_equiv_def]
QED

Triviality eval_operands_execution_equiv:
  !vars ops s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  gen_tac >> Induct >> rw[eval_operands_def] >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_execution_equiv >> simp[] >>
     Cases_on `h` >> simp[] >> metis_tac[]) >>
  simp[] >>
  Cases_on `eval_operand h s1` >> simp[] >>
  first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >> simp[]
QED

(* setup_callee produces identical states under execution_equiv *)
Triviality setup_callee_execution_equiv:
  !vars func args s1 s2.
    execution_equiv vars s1 s2 ==>
    setup_callee func args s1 = setup_callee func args s2
Proof
  rw[execution_equiv_def, setup_callee_def] >>
  simp[venom_state_component_equality]
QED

(* merge_callee_state preserves execution_equiv *)
Triviality merge_callee_state_execution_equiv:
  !vars s1 s2 callee_s.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (merge_callee_state s1 callee_s)
                         (merge_callee_state s2 callee_s)
Proof
  rw[execution_equiv_def, merge_callee_state_def, lookup_var_def]
QED

(* update_var preserves execution_equiv *)
Triviality update_var_execution_equiv:
  !vars out val s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (update_var out val s1) (update_var out val s2)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* Stronger version: update_var preserves execution_equiv AND all non-var fields *)
Triviality update_var_preserves_all:
  !vars out val s1 s2.
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    execution_equiv vars (update_var out val s1) (update_var out val s2) /\
    (update_var out val s1).vs_current_bb =
      (update_var out val s2).vs_current_bb /\
    (update_var out val s1).vs_inst_idx =
      (update_var out val s2).vs_inst_idx /\
    (update_var out val s1).vs_prev_bb = s1.vs_prev_bb /\
    (update_var out val s2).vs_prev_bb = s2.vs_prev_bb /\
    ((update_var out val s1).vs_halted <=>
     (update_var out val s2).vs_halted)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* bind_outputs preserves execution_equiv *)
(* merge_callee_state preserves state_equiv *)
Triviality merge_callee_state_state_equiv:
  !vars s1 s2 callee_s.
    state_equiv vars s1 s2 ==>
    state_equiv vars (merge_callee_state s1 callee_s)
                      (merge_callee_state s2 callee_s)
Proof
  rw[state_equiv_def, merge_callee_state_def, execution_equiv_def,
     lookup_var_def]
QED

(* update_var preserves state_equiv *)
Triviality update_var_state_equiv:
  !vars out val s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (update_var out val s1) (update_var out val s2)
Proof
  rw[state_equiv_def, update_var_def, execution_equiv_def,
     lookup_var_def, FLOOKUP_UPDATE]
QED

(* bind_outputs preserves state_equiv *)
(* FOLDL of update_var preserves state_equiv *)
Triviality foldl_update_var_state_equiv:
  !pairs vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >>
  Cases >> rw[] >>
  first_x_assum irule >>
  metis_tac[update_var_state_equiv]
QED

(* bind_outputs on state_equiv states: either both NONE or both SOME with state_equiv *)
Triviality bind_outputs_state_equiv:
  !outs vals vars s1 s2.
    state_equiv vars s1 s2 ==>
    (bind_outputs outs vals s1 = NONE <=> bind_outputs outs vals s2 = NONE) /\
    (!s1' s2'. bind_outputs outs vals s1 = SOME s1' /\
               bind_outputs outs vals s2 = SOME s2' ==>
               state_equiv vars s1' s2')
Proof
  rw[bind_outputs_def] >> rw[] >> gvs[] >>
  irule foldl_update_var_state_equiv >> simp[]
QED

Triviality decode_invoke_arg_ops_mem:
  !inst name arg_ops v.
    decode_invoke inst = SOME (name, arg_ops) /\
    MEM (Var v) arg_ops ==>
    MEM (Var v) inst.inst_operands
Proof
  rw[decode_invoke_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* INVOKE with same ctx: step_inst preserves result_equiv.
   Chain: eval_operands equal → setup_callee equal → run_function identical →
   merge_callee_state preserves state_equiv → bind_outputs preserves result_equiv. *)
Triviality step_inst_invoke_result_equiv:
  !fuel ctx vars callee_name arg_ops callee_fn inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (callee_name, arg_ops) /\
    lookup_function callee_name ctx.ctx_functions = SOME callee_fn /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                       (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `execution_equiv vars s1 s2` by fs[state_equiv_def] >>
  `eval_operands arg_ops s1 = eval_operands arg_ops s2` by (
    irule eval_operands_execution_equiv >>
    qexists_tac `vars` >> simp[] >>
    metis_tac[decode_invoke_arg_ops_mem]) >>
  simp[step_inst_def] >>
  (* Now both sides have eval_operands arg_ops s2 (simp rewrites s1→s2) *)
  Cases_on `eval_operands arg_ops s2` >> simp[result_equiv_def] >>
  (* setup_callee: equal by execution_equiv *)
  `setup_callee callee_fn x s1 = setup_callee callee_fn x s2` by
    metis_tac[setup_callee_execution_equiv] >>
  simp[] >>
  Cases_on `setup_callee callee_fn x s2` >> simp[result_equiv_def] >>
  (* run_function: identical (same ctx, same callee state) *)
  Cases_on `run_function fuel ctx callee_fn x'` >>
  simp[] >> gvs[result_equiv_def] >>
  (* Halt and Abort cases: execution_equiv refl *)
  TRY (metis_tac[execution_equiv_refl]) >>
  (* IntRet case: merge_callee_state preserves state_equiv *)
  rename1 `run_function _ _ _ _ = IntRet ret_vals callee_s` >>
  `state_equiv vars (merge_callee_state s1 callee_s) (merge_callee_state s2 callee_s)` by
    (irule merge_callee_state_state_equiv >> simp[]) >>
  (* bind_outputs: both NONE or both SOME *)
  `(bind_outputs inst.inst_outputs ret_vals (merge_callee_state s1 callee_s) = NONE <=>
    bind_outputs inst.inst_outputs ret_vals (merge_callee_state s2 callee_s) = NONE)` by
    metis_tac[bind_outputs_state_equiv] >>
  Cases_on `bind_outputs inst.inst_outputs ret_vals (merge_callee_state s1 callee_s)` >>
  Cases_on `bind_outputs inst.inst_outputs ret_vals (merge_callee_state s2 callee_s)` >>
  gvs[result_equiv_def] >>
  metis_tac[bind_outputs_state_equiv, state_equiv_def]
QED

(* step_inst on state_equiv states with same ctx preserves result_equiv.
   Generalizes step_inst_result_equiv to handle INVOKE (same ctx). *)
Theorem step_inst_same_ctx_result_equiv:
  !fuel ctx vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                       (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    Cases_on `decode_invoke inst` >- (
      simp[step_inst_def, result_equiv_def]) >>
    PairCases_on `x` >>
    Cases_on `lookup_function x0 ctx.ctx_functions` >- (
      simp[step_inst_def, result_equiv_def]) >>
    irule step_inst_invoke_result_equiv >>
    metis_tac[]
  ) >>
  irule step_inst_result_equiv >> simp[]
QED

(* Block-level: run_block on same block, same ctx, state_equiv states.
   Handles INVOKE via same-ctx argument (unlike run_block_result_equiv
   which excludes INVOKE). *)
Theorem run_block_same_ctx_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >>
  `!n fuel ctx vars bb s1 s2.
     n = LENGTH bb.bb_instructions - s1.vs_inst_idx ==>
     state_equiv vars s1 s2 /\
     (!inst. MEM inst bb.bb_instructions ==>
             !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
     result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)`
    suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >> gvs[] >>
  (* Unfold both sides *)
  ONCE_REWRITE_TAC[run_block_def] >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
    (gvs[get_instruction_def] >> metis_tac[listTheory.EL_MEM]) >>
  `result_equiv vars (step_inst fuel ctx inst s1)
                     (step_inst fuel ctx inst s2)` by
    metis_tac[step_inst_same_ctx_result_equiv] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_def] >>
  rename1 `step_inst _ _ _ s1 = OK v1` >>
  rename1 `step_inst _ _ _ s2 = OK v2` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >- (
    `v1.vs_halted = v2.vs_halted` by
      fs[state_equiv_def, execution_equiv_def] >>
    Cases_on `v1.vs_halted` >> gvs[result_equiv_def] >>
    fs[state_equiv_def]) >>
  `v1.vs_inst_idx = v2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  simp[] >>
  first_x_assum irule >> simp[] >>
  gvs[get_instruction_def] >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* ================================================================
   Section 5: state_equiv monotonicity and inline_prefix subset
   ================================================================ *)

Theorem state_equiv_mono:
  !A B s1 s2.
    A SUBSET B /\ state_equiv A s1 s2 ==>
    state_equiv B s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem inline_prefix_subset_inline_vars:
  !k v. isPREFIX (inline_prefix k) v ==> isPREFIX "inl" v
Proof
  rw[inline_prefix_def] >>
  Cases_on `v` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[]
QED

(* ================================================================
   Section 6: bb_well_formed preservation through inline_one_site
   ================================================================ *)

(* Helper: TAKE prefix of a well-formed block has no terminators *)
Triviality take_no_terminators[local]:
  !bb k.
    bb_well_formed bb /\
    k < LENGTH bb.bb_instructions /\
    ~is_terminator (EL k bb.bb_instructions).inst_opcode ==>
    !i. i < k ==> ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rw[bb_well_formed_def] >>
  CCONTR_TAC >> fs[] >>
  `i < LENGTH bb.bb_instructions` by simp[] >>
  res_tac >> simp[]
QED

(* Helper: EL on TAKE k xs ++ [y] *)
Triviality el_take_append_sing[local]:
  !k (xs:'a list) y i.
    k <= LENGTH xs /\ i <= k ==>
    EL i (TAKE k xs ++ [y]) =
    if i < k then EL i xs else y
Proof
  rw[EL_APPEND_EQN, LENGTH_TAKE, EL_TAKE] >>
  SUBGOAL_THEN ``i = k:num`` ASSUME_TAC >- simp[] >> simp[]
QED

(* Truncated call block: TAKE call_idx ++ [JMP] is well-formed *)
Theorem truncated_bb_well_formed:
  !bb call_idx ops.
    bb_well_formed bb /\
    call_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL call_idx bb.bb_instructions).inst_opcode ==>
    bb_well_formed (bb with bb_instructions :=
      TAKE call_idx bb.bb_instructions ++
      [<|inst_id := 0; inst_opcode := JMP;
         inst_operands := ops; inst_outputs := []|>])
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``(bb:basic_block).bb_instructions <> []`` ASSUME_TAC
    >- fs[bb_well_formed_def] >>
  SUBGOAL_THEN ``call_idx <> PRE (LENGTH (bb:basic_block).bb_instructions)``
    ASSUME_TAC
    >- (CCONTR_TAC >> fs[bb_well_formed_def] >>
        imp_res_tac LAST_EL >> gvs[]) >>
  simp[bb_well_formed_def, LENGTH_TAKE, LENGTH_APPEND,
       LAST_APPEND_CONS, is_terminator_def] >>
  rpt strip_tac
  >| [
    (* terminator only at end *)
    Cases_on `i = call_idx` >- simp[] >>
    SUBGOAL_THEN ``(i:num) < call_idx`` ASSUME_TAC >- simp[] >>
    SUBGOAL_THEN
      ``EL i (TAKE call_idx (bb:basic_block).bb_instructions ++
         [<|inst_id := 0; inst_opcode := JMP;
            inst_operands := ops; inst_outputs := ([]:(string list))|>]) =
       EL i bb.bb_instructions``
      ASSUME_TAC >- simp[EL_APPEND_EQN, LENGTH_TAKE, EL_TAKE] >>
    fs[bb_well_formed_def] >> res_tac >> simp[],
    (* PHI prefix *)
    Cases_on `j = call_idx`
    >- (SUBGOAL_THEN
          ``EL call_idx (TAKE call_idx (bb:basic_block).bb_instructions ++
             [<|inst_id := 0; inst_opcode := JMP;
                inst_operands := ops; inst_outputs := ([]:(string list))|>]) =
           <|inst_id := 0; inst_opcode := JMP;
             inst_operands := ops; inst_outputs := []|>``
          ASSUME_TAC >- simp[EL_APPEND_EQN, LENGTH_TAKE] >>
        gvs[is_terminator_def])
    >- (SUBGOAL_THEN ``(j:num) < call_idx`` ASSUME_TAC >- simp[] >>
        SUBGOAL_THEN
          ``EL j (TAKE call_idx (bb:basic_block).bb_instructions ++
             [<|inst_id := 0; inst_opcode := JMP;
                inst_operands := ops; inst_outputs := ([]:(string list))|>]) =
           EL j bb.bb_instructions``
          ASSUME_TAC >- simp[EL_APPEND_EQN, LENGTH_TAKE, EL_TAKE] >>
        SUBGOAL_THEN ``(i:num) < call_idx`` ASSUME_TAC >- simp[] >>
        SUBGOAL_THEN
          ``EL i (TAKE call_idx (bb:basic_block).bb_instructions ++
             [<|inst_id := 0; inst_opcode := JMP;
                inst_operands := ops; inst_outputs := ([]:(string list))|>]) =
           EL i bb.bb_instructions``
          ASSUME_TAC >- simp[EL_APPEND_EQN, LENGTH_TAKE, EL_TAKE] >>
        gvs[bb_well_formed_def] >>
        first_x_assum (qspecl_then [`i`, `j`] mp_tac) >>
        simp[])
  ]
QED

(* Return block: DROP (call_idx+1) of well-formed block is well-formed *)
Triviality return_bb_well_formed[local]:
  !bb call_idx lbl.
    bb_well_formed bb /\
    call_idx < LENGTH bb.bb_instructions /\
    call_idx <> PRE (LENGTH bb.bb_instructions) ==>
    bb_well_formed (<|bb_label := lbl;
      bb_instructions := DROP (call_idx + 1) bb.bb_instructions|>)
Proof
  rw[] >>
  SUBGOAL_THEN ``(bb:basic_block).bb_instructions <> []`` ASSUME_TAC
    >- fs[bb_well_formed_def] >>
  SUBGOAL_THEN ``call_idx + 1 < LENGTH (bb:basic_block).bb_instructions``
    ASSUME_TAC >- simp[] >>
  simp[bb_well_formed_def, DROP_EQ_NIL, EL_DROP, LENGTH_DROP] >>
  rpt conj_tac >> rpt strip_tac
  >| [
    (* LAST is terminator *)
    SUBGOAL_THEN ``LAST (DROP (call_idx + 1) (bb:basic_block).bb_instructions) =
                   LAST bb.bb_instructions`` (fn th => simp[th])
      >- (irule last_drop >> simp[]) >>
    fs[bb_well_formed_def],
    (* terminator only at end — goal: i = PRE(LENGTH bb.bb_instructions - (call_idx + 1)) *)
    SUBGOAL_THEN ``i + (call_idx + 1) < LENGTH (bb:basic_block).bb_instructions``
      ASSUME_TAC >- simp[] >>
    fs[EL_DROP, bb_well_formed_def] >> res_tac >>
    simp[arithmeticTheory.PRE_SUB],
    (* PHI prefix *)
    SUBGOAL_THEN ``j + (call_idx + 1) < LENGTH (bb:basic_block).bb_instructions``
      ASSUME_TAC >- simp[] >>
    SUBGOAL_THEN ``i + (call_idx + 1) < LENGTH (bb:basic_block).bb_instructions``
      ASSUME_TAC >- simp[] >>
    fs[EL_DROP] >>
    qpat_x_assum `bb_well_formed bb` mp_tac >>
    simp[bb_well_formed_def] >> strip_tac >>
    first_x_assum (qspecl_then [`i + (call_idx + 1)`,
      `j + (call_idx + 1)`] mp_tac) >>
    impl_tac >- simp[] >>
    simp[]
  ]
QED

(* Suffix of a well-formed block after a non-PHI instruction has no PHIs *)
Theorem suffix_no_phi:
  !bb k.
    bb_well_formed bb /\
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode <> PHI ==>
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP (SUC k) bb.bb_instructions)
Proof
  rpt strip_tac >> simp[EVERY_EL, EL_DROP, LENGTH_DROP] >>
  rpt strip_tac >>
  `n + SUC k < LENGTH bb.bb_instructions` by simp[] >>
  CCONTR_TAC >> gvs[] >>
  fs[bb_well_formed_def] >>
  `k < n + SUC k` by simp[] >>
  res_tac >> gvs[]
QED

(* rewrite_inline_inst preserves non-terminator status for non-RET/non-PARAM *)
Triviality rewrite_inline_inst_opcode:
  !invoke_ops invoke_outs return_label inst pidx insts pidx'.
    rewrite_inline_inst invoke_ops invoke_outs return_label inst pidx =
      (insts, pidx') ==>
    (inst.inst_opcode <> PARAM /\ inst.inst_opcode <> RET ==>
     insts = [inst]) /\
    (inst.inst_opcode = PARAM /\ pidx < LENGTH invoke_ops ==>
     ?i'. insts = [i'] /\ i'.inst_opcode = ASSIGN) /\
    (inst.inst_opcode = PARAM /\ ~(pidx < LENGTH invoke_ops) ==>
     insts = [inst]) /\
    (inst.inst_opcode = RET ==>
     ?assigns jmp.
       insts = assigns ++ [jmp] /\
       jmp.inst_opcode = JMP /\
       EVERY (\a. a.inst_opcode = ASSIGN) assigns)
Proof
  rw[rewrite_inline_inst_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  simp[EVERY_MEM, indexedListsTheory.MEM_MAPi] >>
  rpt strip_tac >> gvs[]
QED

(* General: bb_well_formed preserved when opcodes preserved pointwise *)
Triviality bb_well_formed_opcode_preserved[local]:
  !bb insts'.
    bb_well_formed bb /\
    LENGTH insts' = LENGTH bb.bb_instructions /\
    (!i. i < LENGTH insts' ==>
      (EL i insts').inst_opcode = (EL i bb.bb_instructions).inst_opcode) ==>
    bb_well_formed (bb with bb_instructions := insts')
Proof
  rw[bb_well_formed_def]
  >- (Cases_on `insts'` >> gvs[])
  >- (`insts' <> []` by (Cases_on `insts'` >> gvs[]) >>
      `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
      `LAST insts' = EL (PRE (LENGTH insts')) insts'` by metis_tac[LAST_EL] >>
      `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions))
                                     bb.bb_instructions` by metis_tac[LAST_EL] >>
      `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
        (Cases_on `bb.bb_instructions` >> gvs[]) >>
      res_tac >> gvs[])
  >- (first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      strip_tac >> res_tac >> gvs[])
  >> `(i:num) < LENGTH insts'` by simp[] >>
     `(j:num) < LENGTH insts'` by simp[] >>
     res_tac >> gvs[] >> metis_tac[]
QED

(* rewrite_inline_insts produces non-empty output from non-empty input *)
Triviality rewrite_inline_insts_nonempty[local]:
  !ops outs ret insts pidx insts' pidx'.
    rewrite_inline_insts ops outs ret insts pidx = (insts', pidx') /\
    insts <> [] ==>
    insts' <> []
Proof
  Induct_on `insts` >> simp[rewrite_inline_insts_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `inst_list` >> simp[] >>
  imp_res_tac rewrite_inline_inst_opcode >>
  Cases_on `h.inst_opcode = PARAM` >> Cases_on `h.inst_opcode = RET` >> gvs[]
QED

(* rewrite_inline_inst produces non-empty list *)
Triviality rewrite_inline_inst_nonempty[local]:
  !ops outs ret inst pidx insts pidx'.
    rewrite_inline_inst ops outs ret inst pidx = (insts, pidx') ==>
    insts <> []
Proof
  rpt strip_tac >>
  imp_res_tac rewrite_inline_inst_opcode >>
  Cases_on `inst.inst_opcode = PARAM` >> Cases_on `inst.inst_opcode = RET` >> gvs[]
QED

(* Non-terminator input to rewrite_inline_inst gives non-terminator outputs *)
Triviality rewrite_inline_inst_non_term[local]:
  !ops outs ret inst pidx insts pidx'.
    rewrite_inline_inst ops outs ret inst pidx = (insts, pidx') /\
    ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) insts
Proof
  rpt strip_tac >>
  imp_res_tac rewrite_inline_inst_opcode >>
  `inst.inst_opcode <> RET` by
    (strip_tac >> gvs[is_terminator_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (Cases_on `pidx < LENGTH ops` >> gvs[is_terminator_def])
  >- gvs[]
QED

(* Combined characterization: rewrite_inline_insts preserves bb_well_formed.
   Proof by induction on instruction list, maintaining all 4 properties together.
   Key invariant: the output so far is either:
   - Empty (base case), or
   - A list where all elements are non-terminators (pre-terminal prefix), or
   - A list ending with the terminal instruction's rewrite *)
(* Helper: rewrite_inline_inst on PHI produces PHI, on non-PHI produces non-PHI *)
Triviality rewrite_inline_inst_phi[local]:
  !ops outs ret inst pidx insts pidx'.
    rewrite_inline_inst ops outs ret inst pidx = (insts, pidx') /\
    ~is_terminator inst.inst_opcode ==>
    EVERY (\i. i.inst_opcode = PHI <=> inst.inst_opcode = PHI) insts
Proof
  rpt strip_tac >>
  imp_res_tac rewrite_inline_inst_opcode >>
  SUBGOAL_THEN ``inst.inst_opcode <> RET``
    ASSUME_TAC >- (strip_tac >> gvs[is_terminator_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (Cases_on `pidx < LENGTH ops` >> gvs[is_terminator_def])
  >- gvs[]
QED

(* Helper: rewrite of terminal instruction has terminal at end *)
Triviality rewrite_inline_inst_terminal[local]:
  !ops outs ret inst pidx insts pidx'.
    rewrite_inline_inst ops outs ret inst pidx = (insts, pidx') /\
    is_terminator inst.inst_opcode ==>
    is_terminator (LAST insts).inst_opcode /\
    insts <> [] /\
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) /\
    (!i. i < LENGTH insts ==> (EL i insts).inst_opcode <> PHI)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rewrite_inline_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PARAM` >> gvs[is_terminator_def] >>
  Cases_on `inst.inst_opcode = RET` >> gvs[is_terminator_def]
  >- (
    simp[LAST_APPEND_CONS, is_terminator_def, indexedListsTheory.LENGTH_MAPi] >>
    CONJ_TAC >- (
      rpt strip_tac >>
      qpat_x_assum `is_terminator _` mp_tac >>
      simp[EL_APPEND_EQN, indexedListsTheory.EL_MAPi,
           indexedListsTheory.LENGTH_MAPi] >>
      IF_CASES_TAC >> gvs[is_terminator_def]) >>
    rpt strip_tac >>
    qpat_x_assum `_.inst_opcode = PHI` mp_tac >>
    simp[EL_APPEND_EQN, indexedListsTheory.EL_MAPi,
         indexedListsTheory.LENGTH_MAPi] >>
    IF_CASES_TAC >> gvs[] >>
    SUBGOAL_THEN ``(i:num) = LENGTH inst.inst_operands`` SUBST_ALL_TAC
    >- decide_tac >> gvs[])
  >- (
    (* Other terminator: [inst] unchanged *)
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def])
QED

(* General composition: prepending non-terminal instructions preserves
   bb_well_formed, provided the PHI-prefix property is maintained at
   the boundary. *)
(* Prepending uniformly-typed non-terminal instructions preserves bb_well_formed.
   "Uniformly-typed" means all prefix instructions have PHI iff phi_flag.
   The boundary condition: if phi_flag is false, suffix must not start with PHI. *)
Theorem bb_well_formed_prepend[local]:
  !prefix suffix bb phi_flag.
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    EVERY (\i. (i.inst_opcode = PHI) = phi_flag) prefix /\
    bb_well_formed (bb with bb_instructions := suffix) /\
    (~phi_flag ==> suffix <> [] ==> (HD suffix).inst_opcode <> PHI)
    ==>
    bb_well_formed (bb with bb_instructions := prefix ++ suffix)
Proof
  Induct_on `prefix`
  >- simp[]
  >- (
    rpt strip_tac >> fs[] >>
    first_x_assum (qspecl_then [`suffix`, `bb`, `phi_flag`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `bb_well_formed (bb with bb_instructions := prefix ++ suffix)` mp_tac >>
    simp[bb_well_formed_def] >> strip_tac >>
    rewrite_tac[bb_well_formed_def] >>
    (* rewrite_tac auto-eliminates h::_ <> [], leaving 3 conjuncts *)
    CONJ_TAC >- (
      SUBGOAL_THEN ``(prefix:(instruction list)) ++ suffix <> []``
        ASSUME_TAC >- (Cases_on `prefix` >> gvs[]) >>
      simp[LAST_CONS_cond]) >>
    CONJ_TAC >- (
      rpt strip_tac >>
      Cases_on `i` >> gvs[] >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
    rpt strip_tac >>
    Cases_on `j` >> gvs[] >>
    Cases_on `i` >> gvs[]
    >- (
      Cases_on `n`
      >- (
        Cases_on `prefix` >> fs[] >>
        Cases_on `h.inst_opcode = PHI` >> gvs[])
      >- (
        first_x_assum (qspecl_then [`0`, `SUC n'`] mp_tac) >>
        simp[] >> strip_tac >>
        Cases_on `prefix` >> fs[] >>
        Cases_on `h.inst_opcode = PHI` >> gvs[]))
    >- (
      first_x_assum (qspecl_then [`n'`, `n`] mp_tac) >>
      simp[]))
QED

(* HD of rewrite_inline_inst output has PHI iff input has PHI *)
Triviality rewrite_inline_inst_hd_phi[local]:
  !ops outs ret inst pidx insts pidx'.
    rewrite_inline_inst ops outs ret inst pidx = (insts, pidx') ==>
    ((HD insts).inst_opcode = PHI <=> inst.inst_opcode = PHI)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rewrite_inline_inst_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  Cases_on `inst.inst_operands` >>
  gvs[indexedListsTheory.MAPi_def]
QED

(* HD of rewrite_inline_insts output has PHI iff first input has PHI *)
Triviality rewrite_inline_insts_hd_phi[local]:
  !ops outs ret insts pidx insts' pidx'.
    rewrite_inline_insts ops outs ret insts pidx = (insts', pidx') /\
    insts <> [] ==>
    ((HD insts').inst_opcode = PHI <=> (HD insts).inst_opcode = PHI)
Proof
  rpt gen_tac >> Cases_on `insts` >>
  simp[rewrite_inline_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac rewrite_inline_inst_nonempty >>
  Cases_on `inst_list` >> gvs[] >>
  imp_res_tac rewrite_inline_inst_hd_phi >> gvs[]
QED

(* Removing the head from a well-formed block preserves well-formedness *)
Triviality bb_well_formed_tail[local]:
  !h rest bb.
    bb_well_formed (bb with bb_instructions := h :: rest) /\ rest <> [] ==>
    bb_well_formed (bb with bb_instructions := rest)
Proof
  rpt strip_tac >>
  qpat_x_assum `bb_well_formed _` mp_tac >>
  simp[bb_well_formed_def] >> strip_tac >>
  simp[bb_well_formed_def] >>
  CONJ_TAC >- (
    Cases_on `rest` >> fs[LAST_DEF]) >>
  CONJ_TAC >- (
    rpt strip_tac >>
    qpat_x_assum `!i. i < SUC _ /\ is_terminator _ ==> _`
      (qspec_then `SUC i` mp_tac) >> simp[] >>
    Cases_on `rest` >> fs[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i j. i < j /\ j < SUC _ /\ _ ==> _`
    (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

(* Extracting ~is_terminator for the head of a multi-instruction block *)
Triviality bb_well_formed_hd_not_term[local]:
  !h rest bb.
    bb_well_formed (bb with bb_instructions := h :: rest) /\ rest <> [] ==>
    ~is_terminator h.inst_opcode
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
    (qspec_then `0` mp_tac) >>
  Cases_on `rest` >> fs[]
QED

(* Head of next segment is not PHI if current head is not PHI *)
Triviality bb_well_formed_hd_phi_mono[local]:
  !h h' t bb.
    bb_well_formed (bb with bb_instructions := h :: h' :: t) /\
    h.inst_opcode <> PHI ==>
    h'.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  first_x_assum (qspecl_then [`0`, `1`] mp_tac) >>
  simp[]
QED

Theorem rewrite_inline_insts_well_formed[local]:
  !bb ops outs ret insts pidx insts' pidx'.
    rewrite_inline_insts ops outs ret insts pidx = (insts', pidx') /\
    bb_well_formed (bb with bb_instructions := insts) ==>
    bb_well_formed (bb with bb_instructions := insts')
Proof
  gen_tac >> Induct_on `insts` >>
  simp[rewrite_inline_insts_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `insts`
  >- (
    (* Base case: single instruction [h] — h is the terminator *)
    gvs[rewrite_inline_insts_def] >>
    SUBGOAL_THEN ``is_terminator h.inst_opcode`` ASSUME_TAC
    >- (fs[bb_well_formed_def, LAST_DEF]) >>
    imp_res_tac rewrite_inline_inst_terminal >>
    simp[bb_well_formed_def] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `j` mp_tac) >> simp[])
  >>
  (* Step case: h :: h' :: t — h is NOT a terminator *)
  SUBGOAL_THEN ``(h':instruction :: t) <> []`` ASSUME_TAC >- simp[] >>
  imp_res_tac bb_well_formed_hd_not_term >>
  imp_res_tac bb_well_formed_tail >>
  imp_res_tac rewrite_inline_inst_non_term >>
  imp_res_tac rewrite_inline_inst_phi >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  irule bb_well_formed_prepend >>
  simp[] >>
  qexists_tac `h.inst_opcode = PHI` >>
  simp[] >>
  rpt strip_tac >>
  imp_res_tac bb_well_formed_hd_phi_mono >>
  mp_tac (Q.SPECL [`ops`, `outs`, `ret`, `h'::t`, `pi'`,
                    `rest_list`, `pi''`] rewrite_inline_insts_hd_phi) >>
  simp[]
QED

(* For rewrite_inline_blocks_well_formed, we prove a direct lemma
   about the block-level rewriting *)
Triviality rewrite_inline_block_well_formed[local]:
  !invoke_ops invoke_outs return_label bb pidx bb' pidx'.
    rewrite_inline_block invoke_ops invoke_outs return_label bb pidx =
      (bb', pidx') /\
    bb_well_formed bb ==>
    bb_well_formed bb'
Proof
  rpt strip_tac >>
  gvs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `bb` >> gvs[basic_block_fn_updates] >>
  mp_tac (Q.SPECL [`basic_block s l`, `invoke_ops`, `invoke_outs`,
                    `return_label`, `l`, `pidx`, `insts`, `pi'`]
          rewrite_inline_insts_well_formed) >>
  simp[basic_block_fn_updates]
QED

(* bb_well_formed depends only on instructions, not label *)
Triviality bb_well_formed_insts_only[local]:
  !bb1 bb2. bb1.bb_instructions = bb2.bb_instructions ==>
            (bb_well_formed bb1 <=> bb_well_formed bb2)
Proof
  simp[bb_well_formed_def]
QED

(* clone_basic_block preserves bb_well_formed *)
Triviality clone_basic_block_preserves_wf[local]:
  !prefix labels bb.
    bb_well_formed bb ==>
    bb_well_formed (clone_basic_block prefix labels bb)
Proof
  rw[clone_basic_block_def] >>
  irule (iffRL bb_well_formed_insts_only) >>
  qexists_tac `bb with bb_instructions :=
    MAP (clone_instruction prefix labels) bb.bb_instructions` >>
  simp[] >>
  irule bb_well_formed_opcode_preserved >>
  simp[LENGTH_MAP, EL_MAP, clone_instruction_def]
QED

(* replace_block preserves EVERY when replacement satisfies pred *)
Triviality every_replace_block_wf[local]:
  !P lbl bb bbs.
    EVERY P bbs /\ P bb ==>
    EVERY P (replace_block lbl bb bbs)
Proof
  simp[replace_block_def, EVERY_MAP] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  rw[] >> fs[]
QED

(* clone blocks are well-formed when callee blocks are well-formed *)
Triviality rewrite_inline_blocks_well_formed[local]:
  !bbs invoke_ops invoke_outs return_label pidx bbs' pidx'.
    rewrite_inline_blocks invoke_ops invoke_outs return_label bbs pidx =
      (bbs', pidx') /\
    EVERY bb_well_formed bbs ==>
    EVERY bb_well_formed bbs'
Proof
  Induct >> simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  conj_tac
  >- metis_tac[rewrite_inline_block_well_formed]
  >- (first_x_assum irule >> metis_tac[])
QED

(* clone_function preserves EVERY bb_well_formed *)
Triviality clone_function_every_bb_wf[local]:
  !prefix callee.
    EVERY bb_well_formed callee.fn_blocks ==>
    EVERY bb_well_formed (clone_function prefix callee).fn_blocks
Proof
  rw[clone_function_def, LET_THM, EVERY_MAP, EVERY_MEM] >>
  gvs[MEM_MAP] >>
  irule clone_basic_block_preserves_wf >> res_tac
QED

(* Main: inline_call_site preserves EVERY bb_well_formed *)
Theorem inline_call_site_every_bb_well_formed:
  !prefix ret_lbl caller callee call_lbl call_idx.
    EVERY bb_well_formed caller.fn_blocks /\
    EVERY bb_well_formed callee.fn_blocks /\
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    call_idx < LENGTH call_bb.bb_instructions /\
    ~is_terminator (EL call_idx call_bb.bb_instructions).inst_opcode ==>
    EVERY bb_well_formed
      (inline_call_site prefix ret_lbl caller callee call_lbl call_idx).fn_blocks
Proof
  rw[inline_call_site_def, LET_THM] >>
  pairarg_tac >> gvs[EVERY_APPEND] >>
  (* Establish bb_well_formed call_bb *)
  SUBGOAL_THEN ``bb_well_formed call_bb`` ASSUME_TAC
  >- (imp_res_tac lookup_block_MEM >> gvs[EVERY_MEM]) >>
  (* Establish call_idx <> PRE LENGTH for return_bb *)
  SUBGOAL_THEN ``call_idx <> PRE (LENGTH call_bb.bb_instructions)`` ASSUME_TAC
  >- (strip_tac >> gvs[] >>
      fs[bb_well_formed_def] >> metis_tac[LAST_EL]) >>
  rpt conj_tac
  (* Part 1: replace_block *)
  >- (irule every_replace_block_wf >> simp[] >>
      mp_tac (Q.SPECL [`call_bb`, `call_idx`,
        `[Label (case (clone_function prefix callee).fn_blocks of
            [] => "" | eb::v1 => eb.bb_label)]`]
        truncated_bb_well_formed) >>
      simp[])
  (* Part 2: return_bb *)
  >- (mp_tac (Q.SPECL [`call_bb`, `call_idx`, `ret_lbl`]
        return_bb_well_formed) >> simp[])
  (* Part 3: rewritten clone blocks *)
  >- (imp_res_tac clone_function_every_bb_wf >>
      metis_tac[rewrite_inline_blocks_well_formed])
QED

(* fix_inline_phis preserves EVERY bb_well_formed *)
Theorem fix_inline_phis_every_bb_well_formed:
  !call_lbl ret_lbl ret_bb fn.
    EVERY bb_well_formed fn.fn_blocks ==>
    EVERY bb_well_formed
      (fix_inline_phis call_lbl ret_lbl ret_bb fn).fn_blocks
Proof
  rw[fix_inline_phis_def, LET_THM, EVERY_MAP] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `MEM bb.bb_label (bb_succs ret_bb)` >> simp[] >>
  SUBGOAL_THEN ``bb_well_formed bb`` ASSUME_TAC
  >- (res_tac >> simp[]) >>
  irule bb_well_formed_opcode_preserved >>
  simp[LENGTH_MAP, EL_MAP, subst_label_inst_def] >>
  rpt strip_tac >> rw[]
QED

(* renumber preserves bb_well_formed per block *)
Triviality renumber_block_preserves_bb_wf[local]:
  !n bb. bb_well_formed bb ==> bb_well_formed (SND (renumber_block_inst_ids n bb))
Proof
  rpt strip_tac >>
  simp[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  irule bb_well_formed_opcode_preserved >>
  simp[] >>
  (* renumber_block_inst_ids_map gives: MAP (opcode,ops,outs) same on both sides *)
  mp_tac (SPEC_ALL renumber_block_inst_ids_map) >>
  simp[renumber_block_inst_ids_def, LET_THM] >>
  strip_tac >>
  `LENGTH insts' = LENGTH bb.bb_instructions` by
    (fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN]) >>
  simp[] >> rpt strip_tac >>
  fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN]
QED

(* Helper: FOLDL over blocks preserves EVERY bb_well_formed *)
Triviality foldl_renumber_blocks_wf[local]:
  !bbs n acc.
    EVERY bb_well_formed bbs /\ EVERY bb_well_formed acc ==>
    EVERY bb_well_formed
      (SND (FOLDL (\(n,acc) bb. let (n',bb') = renumber_block_inst_ids n bb
                                 in (n', acc ++ [bb'])) (n,acc) bbs))
Proof
  Induct >> simp[] >>
  rpt strip_tac >>
  pairarg_tac >> fs[] >>
  first_x_assum irule >>
  simp[EVERY_APPEND] >>
  `bb' = SND (renumber_block_inst_ids n h)` by simp[] >>
  metis_tac[renumber_block_preserves_bb_wf]
QED

(* renumber preserves bb_well_formed *)
Theorem renumber_fn_inst_ids_every_bb_well_formed:
  !fn.
    EVERY bb_well_formed fn.fn_blocks ==>
    EVERY bb_well_formed (renumber_fn_inst_ids fn).fn_blocks
Proof
  rw[renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  qsuff_tac `EVERY bb_well_formed (SND (FOLDL (\(n,acc) bb.
      let (n',bb') = renumber_block_inst_ids n bb in (n', acc ++ [bb']))
      (0,[]) fn.fn_blocks))`
  >- fs[] >>
  irule foldl_renumber_blocks_wf >> simp[]
QED

(* inline_one_site preserves EVERY bb_well_formed *)
Theorem inline_one_site_every_bb_well_formed:
  !caller callee ist caller' ist'.
    inline_one_site caller callee ist = SOME (caller', ist') /\
    EVERY bb_well_formed caller.fn_blocks /\
    EVERY bb_well_formed callee.fn_blocks /\
    ALL_DISTINCT (fn_labels caller) ==>
    EVERY bb_well_formed caller'.fn_blocks
Proof
  rw[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >> gvs[] >>
  rename1 `SOME site` >> Cases_on `site` >> gvs[LET_THM] >>
  rename1 `find_invoke_site _ _ = SOME (bb_lbl, idx)` >>
  (* Get lookup_block + idx bound + opcode from find_invoke_site *)
  imp_res_tac find_invoke_site_lookup >>
  Cases_on `lookup_block bb_lbl caller.fn_blocks` >> gvs[] >>
  rename1 `lookup_block _ _ = SOME call_bb` >>
  `idx < LENGTH call_bb.bb_instructions` by (
    irule find_invoke_site_idx_bound >> gvs[fn_labels_def] >>
    metis_tac[]) >>
  `~is_terminator (EL idx call_bb.bb_instructions).inst_opcode` by (
    imp_res_tac find_invoke_site_opcode >>
    gvs[fn_labels_def, is_terminator_def]) >>
  (* Each step preserves EVERY bb_well_formed *)
  qabbrev_tac `pfx = inline_prefix ist.is_inline_count` >>
  qabbrev_tac `rl = return_block_label pfx ist.is_label_counter` >>
  qabbrev_tac `c1 = inline_call_site pfx rl caller callee bb_lbl idx` >>
  `EVERY bb_well_formed c1.fn_blocks` by (
    qunabbrev_tac `c1` >>
    irule inline_call_site_every_bb_well_formed >>
    metis_tac[]) >>
  Cases_on `lookup_block rl c1.fn_blocks` >> gvs[]
  >- (irule renumber_fn_inst_ids_every_bb_well_formed >> simp[])
  >- (irule renumber_fn_inst_ids_every_bb_well_formed >>
      irule fix_inline_phis_every_bb_well_formed >> simp[])
QED

(* ================================================================
   Section 7: Clone block lookup in caller_xf

   Infrastructure for discharging clone_execution_sim_ext premises.
   ================================================================ *)

(* rewrite_inline_block preserves label *)
Theorem rewrite_inline_block_label:
  !ops outs ret_lbl bb pidx.
    (FST (rewrite_inline_block ops outs ret_lbl bb pidx)).bb_label =
    bb.bb_label
Proof
  rw[rewrite_inline_block_def, LET_THM] >> pairarg_tac >> simp[]
QED

(* rewrite_inline_blocks preserves labels *)
Theorem rewrite_inline_blocks_labels:
  !ops outs ret_lbl bbs pidx.
    MAP (\bb. bb.bb_label)
      (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >> rw[rewrite_inline_blocks_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `rest' = FST (rewrite_inline_blocks ops outs ret_lbl bbs pi')` by
    (Cases_on `rewrite_inline_blocks ops outs ret_lbl bbs pi'` >> gvs[]) >>
  pop_assum SUBST1_TAC >> simp[]
QED

(* rewrite_inline_blocks preserves length *)
Theorem rewrite_inline_blocks_length:
  !ops outs ret_lbl bbs pidx.
    LENGTH (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)) =
    LENGTH bbs
Proof
  Induct_on `bbs` >> rw[rewrite_inline_blocks_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `LENGTH rest' =
   LENGTH (FST (rewrite_inline_blocks ops outs ret_lbl bbs pi'))` by
    (Cases_on `rewrite_inline_blocks ops outs ret_lbl bbs pi'` >> gvs[]) >>
  gvs[]
QED

(* ================================================================
   Section 8: Clone block lookup infrastructure
   (for discharging clone_execution_sim_ext premises)
   ================================================================ *)

(* FIND on MAP: if FIND f xs = SOME x, then FIND (f o g) (MAP g xs) = SOME (g x)
   — but we need the label-specific version *)
Theorem lookup_block_map_clone:
  !prefix labels bbs lbl bb.
    lookup_block lbl bbs = SOME bb /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    lookup_block (STRCAT prefix lbl)
      (MAP (clone_basic_block prefix labels) bbs) =
    SOME (clone_basic_block prefix labels bb)
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[FIND_thm, clone_basic_block_def]
  >> first_x_assum (qspecl_then [`prefix`, `labels`, `lbl`, `bb`] mp_tac) >>
  simp[lookup_block_def]
QED

(* lookup_block in clone_function *)
Theorem lookup_block_clone_function:
  !prefix callee lbl bb.
    lookup_block lbl callee.fn_blocks = SOME bb /\
    ALL_DISTINCT (fn_labels callee) ==>
    lookup_block (STRCAT prefix lbl)
      (clone_function prefix callee).fn_blocks =
    SOME (clone_basic_block prefix (fn_labels callee) bb)
Proof
  rpt strip_tac >>
  simp[clone_function_def, LET_THM] >>
  mp_tac (Q.SPECL [`prefix`, `fn_labels callee`, `callee.fn_blocks`,
    `lbl`, `bb`] lookup_block_map_clone) >>
  fs[fn_labels_def]
QED

(* rewrite_inline_blocks preserves FIND structure:
   if lookup in clone blocks succeeds, then lookup in rewritten blocks
   gives the rewritten version *)
Theorem lookup_block_rewrite_inline_blocks:
  !ops outs ret_lbl bbs pidx lbl bb.
    lookup_block lbl bbs = SOME bb /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    ?bb'. lookup_block lbl
      (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)) = SOME bb' /\
      bb'.bb_label = bb.bb_label
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, FIND_thm, rewrite_inline_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `bb'.bb_label = h.bb_label` by
    (gvs[rewrite_inline_block_def, LET_THM] >> pairarg_tac >> gvs[]) >>
  Cases_on `h.bb_label = lbl` >> gvs[]
  >- simp[lookup_block_def, FIND_thm]
  >>
  simp[lookup_block_def, FIND_thm] >>
  `rest' = FST (rewrite_inline_blocks ops outs ret_lbl bbs pi')` by
    (Cases_on `rewrite_inline_blocks ops outs ret_lbl bbs pi'` >> gvs[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`ops`, `outs`, `ret_lbl`, `pi'`, `lbl`] mp_tac) >>
  simp[lookup_block_def]
QED

(* FIND on APPEND: if not found in first, look in second *)
Theorem lookup_block_append:
  !lbl bbs1 bbs2.
    lookup_block lbl (bbs1 ++ bbs2) =
    case lookup_block lbl bbs1 of
      SOME bb => SOME bb
    | NONE => lookup_block lbl bbs2
Proof
  simp[lookup_block_def] >>
  Induct_on `bbs1` >> simp[FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = lbl` >> simp[]
QED

(* lookup_block not found when label not in MAP *)
Theorem lookup_block_none_not_mem:
  !lbl bbs.
    ~MEM lbl (MAP (\b. b.bb_label) bbs) ==>
    lookup_block lbl bbs = NONE
Proof
  simp[lookup_block_def] >>
  Induct_on `bbs` >> simp[FIND_thm] >>
  rpt strip_tac >> gvs[]
QED


(* ALL_DISTINCT is preserved through clone_function (STRCAT prefix is injective) *)
Theorem clone_function_all_distinct_labels:
  ALL_DISTINCT (fn_labels callee) ==>
  ALL_DISTINCT (MAP (\b. b.bb_label)
    (clone_function prefix callee).fn_blocks)
Proof
  simp[clone_function_def, LET_THM, MAP_MAP_o, combinTheory.o_DEF,
       clone_basic_block_def, fn_labels_def] >>
  strip_tac >>
  `MAP (\x. STRCAT prefix x.bb_label) callee.fn_blocks =
   MAP (STRCAT prefix) (MAP (\b. b.bb_label) callee.fn_blocks)`
    by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  pop_assum SUBST1_TAC >>
  fs[all_distinct_map_strcat]
QED

(* Head block of rewrite_inline_blocks gets the initial pidx *)
Theorem rewrite_inline_blocks_head_pidx:
  !ops outs ret_lbl bb rest pidx.
    ALL_DISTINCT (MAP (\b. b.bb_label) (bb::rest)) ==>
    ?bb'.
      lookup_block bb.bb_label
        (FST (rewrite_inline_blocks ops outs ret_lbl (bb::rest) pidx)) =
        SOME bb' /\
      bb'.bb_label = bb.bb_label /\
      bb'.bb_instructions =
        FST (rewrite_inline_insts ops outs ret_lbl bb.bb_instructions pidx)
Proof
  rpt strip_tac >>
  simp[rewrite_inline_blocks_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  simp[lookup_block_def, FIND_thm] >>
  gvs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Triviality rewrite_inline_block_insts[local]:
  !ops outs ret_lbl bb pidx bb' pi'.
    rewrite_inline_block ops outs ret_lbl bb pidx = (bb', pi') ==>
    bb'.bb_label = bb.bb_label /\
    bb'.bb_instructions =
      FST (rewrite_inline_insts ops outs ret_lbl bb.bb_instructions pidx)
Proof
  rpt strip_tac >>
  gvs[rewrite_inline_block_def, LET_THM, UNCURRY]
QED

Theorem lookup_block_rewrite_inline_blocks_ext:
  !ops outs ret_lbl bbs pidx lbl bb.
    lookup_block lbl bbs = SOME bb /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    ?bb' pidx_bb.
      lookup_block lbl
        (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)) = SOME bb' /\
      bb'.bb_label = bb.bb_label /\
      bb'.bb_instructions =
        FST (rewrite_inline_insts ops outs ret_lbl bb.bb_instructions pidx_bb)
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, FIND_thm, rewrite_inline_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  Cases_on `h.bb_label = lbl`
  >- (
    (* Head match: h = bb, substitute *)
    fs[] >>
    qpat_x_assum `h = bb` SUBST_ALL_TAC >>
    drule rewrite_inline_block_insts >> strip_tac >>
    qexistsl_tac [`bb'`, `pidx`] >> simp[FIND_thm])
  >> fs[]
  >>
  (* Tail case: FIND skips bb' (wrong label), searches rest' *)
  drule rewrite_inline_block_insts >> strip_tac >>
  `rest' = FST (rewrite_inline_blocks ops outs ret_lbl bbs pi')` by
    (Cases_on `rewrite_inline_blocks ops outs ret_lbl bbs pi'` >> fs[]) >>
  fs[] >>
  first_x_assum (qspecl_then [`ops`, `outs`, `ret_lbl`, `pi'`, `lbl`, `bb`]
    mp_tac) >>
  simp[lookup_block_def] >>
  strip_tac >>
  qexistsl_tac [`bb''`, `pidx_bb`] >>
  simp[lookup_block_def, FIND_thm]
QED

(* Clone blocks in fn_inl: given a callee block, find the corresponding
   clone block in inline_call_site output. The result has the right
   label and its instructions come from rewrite_inline of clone. *)
Theorem lookup_block_clone_in_fn_inl:
  !prefix ret_lbl caller callee call_lbl call_idx lbl bb.
    lookup_block lbl callee.fn_blocks = SOME bb /\
    lookup_block call_lbl caller.fn_blocks <> NONE /\
    ALL_DISTINCT (fn_labels callee) /\
    ~MEM (STRCAT prefix lbl) (fn_labels caller) /\
    STRCAT prefix lbl <> ret_lbl ==>
    ?bb' pidx_bb.
      lookup_block (STRCAT prefix lbl)
        (inline_call_site prefix ret_lbl caller callee
           call_lbl call_idx).fn_blocks = SOME bb' /\
      bb'.bb_label = STRCAT prefix lbl /\
      bb'.bb_instructions =
        FST (rewrite_inline_insts
          (rotate_invoke_ops
            (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions❲call_idx❳.inst_operands)
          (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions❲call_idx❳.inst_outputs
          ret_lbl
          (MAP (clone_instruction prefix (fn_labels callee))
               bb.bb_instructions)
          pidx_bb)
Proof
  rpt strip_tac >>
  simp[inline_call_site_def, LET_THM] >>
  Cases_on `lookup_block call_lbl caller.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >>
  (* Keep in lookup_block form — don't expand to FIND *)
  `rewritten_blocks = FST (rewrite_inline_blocks
    (rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands)
    x.bb_instructions❲call_idx❳.inst_outputs ret_lbl
    (clone_function prefix callee).fn_blocks 0)` by
    (Cases_on `rewrite_inline_blocks
      (rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands)
      x.bb_instructions❲call_idx❳.inst_outputs ret_lbl
      (clone_function prefix callee).fn_blocks 0` >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Establish lookup in rewritten clone blocks *)
  `ALL_DISTINCT (MAP (\b. b.bb_label)
    (clone_function prefix callee).fn_blocks)` by
    metis_tac[clone_function_all_distinct_labels] >>
  mp_tac (Q.SPECL [`prefix`, `callee`, `lbl`, `bb`]
    lookup_block_clone_function) >> simp[] >> strip_tac >>
  (* Use _ext to get instruction content *)
  mp_tac (Q.SPECL [
    `rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands`,
    `x.bb_instructions❲call_idx❳.inst_outputs`, `ret_lbl`,
    `(clone_function prefix callee).fn_blocks`, `0`,
    `STRCAT prefix lbl`,
    `clone_basic_block prefix (fn_labels callee) bb`]
    lookup_block_rewrite_inline_blocks_ext) >>
  simp[] >> strip_tac >>
  (* Use lookup_block_append: not in replace_block → found in rewrite blocks *)
  simp[lookup_block_append] >>
  `lookup_block (STRCAT prefix lbl)
    (replace_block x.bb_label
      (x with bb_instructions := TAKE call_idx x.bb_instructions ++
        [<|inst_id := 0; inst_opcode := JMP;
           inst_operands :=
             [Label (case (clone_function prefix callee).fn_blocks of
                       [] => "" | eb::v1 => eb.bb_label)];
           inst_outputs := []|>])
      caller.fn_blocks) = NONE` by (
    irule lookup_block_none_not_mem >>
    simp[fn_labels_replace_block] >>
    fs[fn_labels_def]) >>
  simp[] >>
  qexistsl_tac [`bb'`, `pidx_bb`] >>
  gvs[clone_basic_block_def]
QED

(* lookup_block_clone_in_fn_inl specialized to the entry (head) block.
   Returns pidx = 0 (not existential), since rewrite_inline_blocks
   starts its fold at pidx=0 and the head block gets the initial value. *)
Theorem lookup_block_clone_in_fn_inl_head:
  !prefix ret_lbl caller callee call_lbl call_idx.
    fn_has_entry callee /\
    lookup_block call_lbl caller.fn_blocks <> NONE /\
    ALL_DISTINCT (fn_labels callee) /\
    ~MEM (STRCAT prefix (HD callee.fn_blocks).bb_label) (fn_labels caller) /\
    STRCAT prefix (HD callee.fn_blocks).bb_label <> ret_lbl ==>
    ?bb'.
      lookup_block (STRCAT prefix (HD callee.fn_blocks).bb_label)
        (inline_call_site prefix ret_lbl caller callee
           call_lbl call_idx).fn_blocks = SOME bb' /\
      bb'.bb_label = STRCAT prefix (HD callee.fn_blocks).bb_label /\
      bb'.bb_instructions =
        FST (rewrite_inline_insts
          (rotate_invoke_ops
            (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
              ❲call_idx❳.inst_operands)
          (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
              ❲call_idx❳.inst_outputs
          ret_lbl
          (MAP (clone_instruction prefix (fn_labels callee))
               (HD callee.fn_blocks).bb_instructions)
          0)
Proof
  rpt strip_tac >>
  `callee.fn_blocks <> []` by fs[fn_has_entry_def] >>
  simp[inline_call_site_def, LET_THM] >>
  Cases_on `lookup_block call_lbl caller.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >>
  (* Extract rewritten_blocks *)
  `rewritten_blocks = FST (rewrite_inline_blocks
    (rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands)
    x.bb_instructions❲call_idx❳.inst_outputs ret_lbl
    (clone_function prefix callee).fn_blocks 0)` by
    (Cases_on `rewrite_inline_blocks
      (rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands)
      x.bb_instructions❲call_idx❳.inst_outputs ret_lbl
      (clone_function prefix callee).fn_blocks 0` >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
    (clone_function prefix callee).fn_blocks)` by
    metis_tac[clone_function_all_distinct_labels] >>
  (* Use rewrite_inline_blocks_head_pidx on clone blocks *)
  Cases_on `(clone_function prefix callee).fn_blocks`
  >- gvs[clone_function_def, LET_THM] >>
  `h = clone_basic_block prefix (fn_labels callee) (HD callee.fn_blocks)` by
    (Cases_on `callee.fn_blocks` >> gvs[clone_function_def, LET_THM]) >>
  mp_tac (Q.SPECL [
    `rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands`,
    `x.bb_instructions❲call_idx❳.inst_outputs`, `ret_lbl`,
    `h`, `t`, `0`] rewrite_inline_blocks_head_pidx) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Connect via lookup_block_append *)
  simp[lookup_block_append] >>
  `lookup_block (STRCAT prefix (HD callee.fn_blocks).bb_label)
     (replace_block call_lbl
       (x with bb_instructions :=
          TAKE call_idx x.bb_instructions ++
          [<|inst_id := 0; inst_opcode := JMP;
             inst_operands :=
               [Label (clone_basic_block prefix (fn_labels callee)
                  (HD callee.fn_blocks)).bb_label];
             inst_outputs := []|>])
       caller.fn_blocks) = NONE` by (
    irule lookup_block_none_not_mem >>
    simp[fn_labels_replace_block] >>
    fs[fn_labels_def]) >>
  simp[] >>
  qexists_tac `bb'` >>
  gvs[clone_basic_block_def]
QED

(* ================================================================
   rewrite_inline_insts is pidx-independent when there are no PARAMs.
   This is critical for applying clone_block_sim_thm to non-entry blocks,
   where the accumulated pidx from prior blocks may be non-zero but
   the block has no PARAMs to rewrite.
   ================================================================ *)

Theorem rewrite_inline_inst_no_param:
  !ops outs ret inst pidx pidx'.
    inst.inst_opcode <> PARAM ==>
    FST (rewrite_inline_inst ops outs ret inst pidx) =
    FST (rewrite_inline_inst ops outs ret inst pidx') /\
    SND (rewrite_inline_inst ops outs ret inst pidx) -
      SND (rewrite_inline_inst ops outs ret inst pidx') = pidx - pidx'
Proof
  rpt strip_tac >>
  simp[rewrite_inline_inst_def] >>
  Cases_on `inst.inst_opcode = RET` >> simp[]
QED

Theorem rewrite_inline_insts_pidx_irrel:
  !insts ops outs ret pidx pidx'.
    EVERY (\i. i.inst_opcode <> PARAM) insts ==>
    FST (rewrite_inline_insts ops outs ret insts pidx) =
    FST (rewrite_inline_insts ops outs ret insts pidx')
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt strip_tac >>
  simp[LET_THM] >>
  `FST (rewrite_inline_inst ops outs ret h pidx) =
   FST (rewrite_inline_inst ops outs ret h pidx')` by
    metis_tac[rewrite_inline_inst_no_param] >>
  Cases_on `rewrite_inline_inst ops outs ret h pidx` >>
  Cases_on `rewrite_inline_inst ops outs ret h pidx'` >>
  gvs[] >>
  Cases_on `rewrite_inline_insts ops outs ret insts r` >>
  Cases_on `rewrite_inline_insts ops outs ret insts r'` >>
  gvs[] >>
  first_x_assum (qspecl_then [`ops`, `outs`, `ret`, `r`, `r'`] mp_tac) >>
  gvs[]
QED


(* ================================================================
   Clone block output characterization: all outputs of a
   clone+rewrite block are either prefixed or in invoke_outs.
   Used to discharge the frame hypothesis of clone_execution_sim_ext.
   ================================================================ *)

(* Single instruction: rewrite_inline_inst preserves output boundedness.
   For the RET case, each output is EL i outs where i < LENGTH ret_vals.
   We need LENGTH inst.inst_operands <= LENGTH outs (callee_ret_arity_le). *)
Theorem rewrite_inline_inst_outputs_bounded:
  !ops outs ret inst pidx prefix.
    EVERY (isPREFIX prefix) inst.inst_outputs /\
    (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH outs) ==>
    EVERY (\v. isPREFIX prefix v \/ MEM v outs)
      (FLAT (MAP (\i. i.inst_outputs)
        (FST (rewrite_inline_inst ops outs ret inst pidx))))
Proof
  rpt strip_tac >>
  simp[rewrite_inline_inst_def] >>
  Cases_on `inst.inst_opcode = PARAM` >> simp[]
  >- (IF_CASES_TAC >> simp[] >> fs[EVERY_MEM])
  >> Cases_on `inst.inst_opcode = RET` >> simp[]
  >- (
    simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM,
         indexedListsTheory.MEM_MAPi] >>
    rpt strip_tac >> gvs[] >>
    disj2_tac >> simp[MEM_EL] >>
    qexists_tac `n` >> simp[])
  >> fs[EVERY_MEM]
QED

(* Instruction list: rewrite_inline_insts preserves output boundedness *)
Theorem rewrite_inline_insts_outputs_bounded:
  !insts ops outs ret pidx prefix.
    EVERY (\inst. EVERY (isPREFIX prefix) inst.inst_outputs) insts /\
    EVERY (\inst. inst.inst_opcode = RET ==>
                  LENGTH inst.inst_operands <= LENGTH outs) insts ==>
    EVERY (\v. isPREFIX prefix v \/ MEM v outs)
      (FLAT (MAP (\i. i.inst_outputs)
        (FST (rewrite_inline_insts ops outs ret insts pidx))))
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `rewrite_inline_inst ops outs ret h pidx` >>
  Cases_on `rewrite_inline_insts ops outs ret insts r` >>
  simp[] >>
  simp[EVERY_APPEND] >> rpt conj_tac
  >- (
    `EVERY (\v. isPREFIX prefix v \/ MEM v outs)
       (FLAT (MAP (\i. i.inst_outputs) q))` suffices_by simp[] >>
    `q = FST (rewrite_inline_inst ops outs ret h pidx)` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    irule rewrite_inline_inst_outputs_bounded >> simp[])
  >- (
    `EVERY (\v. isPREFIX prefix v \/ MEM v outs)
       (FLAT (MAP (\i. i.inst_outputs) q'))` suffices_by simp[] >>
    `q' = FST (rewrite_inline_insts ops outs ret insts r)` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    first_x_assum irule >> simp[])
QED

(* Full chain: clone + rewrite outputs are prefixed or in invoke_outs.
   Needs callee_ret_arity_le: all RET operand counts <= LENGTH outs.
   clone_instruction preserves opcode and operands, so the RET condition
   transfers from the original callee instructions. *)
Theorem clone_rewrite_outputs_bounded:
  !insts ops outs ret prefix labels pidx.
    EVERY (\inst. inst.inst_opcode = RET ==>
                  LENGTH inst.inst_operands <= LENGTH outs) insts ==>
    EVERY (\v. isPREFIX prefix v \/ MEM v outs)
      (FLAT (MAP (\i. i.inst_outputs)
        (FST (rewrite_inline_insts ops outs ret
          (MAP (clone_instruction prefix labels) insts) pidx))))
Proof
  rpt strip_tac >>
  irule rewrite_inline_insts_outputs_bounded >>
  simp[EVERY_MAP, EVERY_MEM, clone_instruction_def] >> rpt conj_tac >>
  rpt strip_tac
  >- (fs[EVERY_MEM])
  >- (gvs[MEM_MAP, isPREFIX_STRCAT])
QED

(* ================================================================
   eval_operand through execution_equiv
   ================================================================ *)

(* eval_operand only depends on lookup_var (for Var) or nothing (for Lit/Label).
   execution_equiv gives lookup_var equality for vars outside excl_vars.
   So eval_operand is preserved across execution_equiv states. *)
Theorem eval_operand_execution_equiv:
  !vars op s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  fs[execution_equiv_def]
QED

(* Corollary: if eval_operand op s1 = SOME v and execution_equiv,
   then eval_operand op s2 = SOME v *)
Theorem eval_operand_execution_equiv_SOME:
  !vars op s1 s2 v.
    execution_equiv vars s1 s2 /\
    eval_operand op s1 = SOME v /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s2 = SOME v
Proof
  metis_tac[eval_operand_execution_equiv]
QED

(* ================================================================
   Section 9: Reverse lookup infrastructure
   ================================================================ *)

(* If label is in MAP bb_label, then lookup_block succeeds *)
Theorem mem_labels_lookup_exists:
  !lbl bbs.
    MEM lbl (MAP (\b. b.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  res_tac >> fs[lookup_block_def]
QED

(* Reverse: from lookup in rewritten blocks, recover lookup in original *)
Theorem lookup_block_rewrite_inline_blocks_reverse:
  !ops outs ret_lbl bbs pidx lbl bb'.
    lookup_block lbl
      (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)) = SOME bb' ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  rpt strip_tac >>
  irule mem_labels_lookup_exists >>
  imp_res_tac lookup_block_label >>
  `MEM lbl (MAP (\b. b.bb_label)
    (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx)))` by
    metis_tac[lookup_block_MEM, MEM_MAP] >>
  fs[rewrite_inline_blocks_labels]
QED

(* Reverse lookup: from a prefixed label in MAP clone bbs,
   recover the original block. *)
Theorem lookup_block_map_clone_reverse:
  !prefix labels bbs lbl bb'.
    lookup_block (STRCAT prefix lbl)
      (MAP (clone_basic_block prefix labels) bbs) = SOME bb' ==>
    ?bb. lookup_block lbl bbs = SOME bb /\
         bb' = clone_basic_block prefix labels bb
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, FIND_thm, clone_basic_block_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  (* F case: STRCAT prefix h.bb_label <> STRCAT prefix lbl *)
  `h.bb_label <> lbl` by fs[stringTheory.STRCAT_11] >>
  simp[] >> strip_tac >>
  (* Fold FIND back to lookup_block for IH match *)
  qpat_x_assum `FIND _ _ = SOME _` mp_tac >>
  simp[GSYM lookup_block_def] >> strip_tac >>
  first_x_assum drule >> simp[clone_basic_block_def]
QED

(* Reverse lookup in clone_function *)
Theorem lookup_block_clone_function_reverse:
  !prefix callee lbl bb'.
    lookup_block (STRCAT prefix lbl)
      (clone_function prefix callee).fn_blocks = SOME bb' ==>
    ?bb. lookup_block lbl callee.fn_blocks = SOME bb /\
         bb' = clone_basic_block prefix (fn_labels callee) bb
Proof
  rpt strip_tac >>
  fs[clone_function_def, LET_THM] >>
  irule lookup_block_map_clone_reverse >>
  first_assum ACCEPT_TAC
QED

(* ================================================================
   Reverse lookup in inline_call_site output:
   given a clone block at STRCAT prefix lbl in fn_inl, recover the
   original callee block and instruction structure.

   Strategy: use forward lookup_block_clone_in_fn_inl for the
   instruction structure, then show uniqueness of lookup.
   ================================================================ *)
(* Helper: lookup of a clone label in fn_inl falls through to rewritten blocks.
   The conclusion existentially quantifies ops/outs since inline_call_site_def
   binds them internally from the call block. *)
Triviality inline_call_site_clone_in_rewritten[local]:
  !prefix ret_lbl caller callee call_lbl call_idx lbl bb.
    lookup_block (STRCAT prefix lbl)
      (inline_call_site prefix ret_lbl caller callee
         call_lbl call_idx).fn_blocks = SOME bb /\
    ~MEM (STRCAT prefix lbl) (fn_labels caller) /\
    STRCAT prefix lbl <> ret_lbl /\
    lookup_block call_lbl caller.fn_blocks <> NONE ==>
    ?ops outs.
      lookup_block (STRCAT prefix lbl)
        (FST (rewrite_inline_blocks ops outs ret_lbl
           (clone_function prefix callee).fn_blocks 0)) = SOME bb
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_block _ (inline_call_site _ _ _ _ _ _).fn_blocks = _`
    mp_tac >>
  simp[inline_call_site_def, LET_THM] >>
  Cases_on `lookup_block call_lbl caller.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >>
  simp[lookup_block_append] >>
  `lookup_block (STRCAT prefix lbl)
    (replace_block call_lbl
      (x with bb_instructions := TAKE call_idx x.bb_instructions ++
        [<|inst_id := 0; inst_opcode := JMP;
           inst_operands :=
             [Label (case (clone_function prefix callee).fn_blocks of
                       [] => "" | eb::v1 => eb.bb_label)];
           inst_outputs := []|>])
      caller.fn_blocks) = NONE` by (
    irule lookup_block_none_not_mem >>
    simp[fn_labels_replace_block] >> fs[fn_labels_def]) >>
  simp[] >>
  simp[lookup_block_def, FIND_thm] >> strip_tac >>
  qexistsl_tac [
    `rotate_invoke_ops x.bb_instructions❲call_idx❳.inst_operands`,
    `x.bb_instructions❲call_idx❳.inst_outputs`] >>
  gvs[lookup_block_def]
QED

Theorem clone_in_fn_inl_reverse:
  !prefix ret_lbl caller callee call_lbl call_idx lbl bb.
    lookup_block (STRCAT prefix lbl)
      (inline_call_site prefix ret_lbl caller callee
         call_lbl call_idx).fn_blocks = SOME bb /\
    ALL_DISTINCT (fn_labels callee) /\
    ~MEM (STRCAT prefix lbl) (fn_labels caller) /\
    STRCAT prefix lbl <> ret_lbl /\
    lookup_block call_lbl caller.fn_blocks <> NONE ==>
    ?bb_callee pidx_bb.
      lookup_block lbl callee.fn_blocks = SOME bb_callee /\
      bb.bb_label = STRCAT prefix lbl /\
      bb.bb_instructions =
        FST (rewrite_inline_insts
          (rotate_invoke_ops
            (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
              ❲call_idx❳.inst_operands)
          (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
            ❲call_idx❳.inst_outputs
          ret_lbl
          (MAP (clone_instruction prefix (fn_labels callee))
               bb_callee.bb_instructions)
          pidx_bb)
Proof
  rpt strip_tac >>
  (* Step 1: Get lookup in rewritten clone blocks *)
  drule_all inline_call_site_clone_in_rewritten >> strip_tac >>
  (* Step 2: Recover callee block *)
  drule lookup_block_rewrite_inline_blocks_reverse >> strip_tac >>
  drule lookup_block_clone_function_reverse >> strip_tac >>
  qexists_tac `bb''` >>
  (* Step 3: Forward lemma gives instruction structure + lookup determinism *)
  mp_tac (Q.SPECL [`prefix`, `ret_lbl`, `caller`, `callee`,
    `call_lbl`, `call_idx`, `lbl`, `bb''`]
    lookup_block_clone_in_fn_inl) >> simp[]
QED

(* ================================================================
   Section 10: Opcode preservation through clone/rewrite
   ================================================================ *)

(* clone_instruction preserves inst_opcode *)
Theorem clone_instruction_opcode:
  !prefix labels inst.
    (clone_instruction prefix labels inst).inst_opcode = inst.inst_opcode
Proof
  simp[clone_instruction_def]
QED

(* rewrite_inline_insts preserves the no-PHI property *)
Theorem rewrite_inline_insts_no_phi:
  !ops outs ret insts pidx.
    EVERY (\inst. inst.inst_opcode <> PHI) insts ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (FST (rewrite_inline_insts ops outs ret insts pidx))
Proof
  Induct_on `insts` >>
  simp[rewrite_inline_insts_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >>
  simp[EVERY_APPEND] >> conj_tac
  >- (
    (* inst_list from rewrite_inline_inst h *)
    imp_res_tac rewrite_inline_inst_opcode >>
    Cases_on `h.inst_opcode = PARAM`
    >- (Cases_on `pidx < LENGTH ops` >> gvs[])
    >- (Cases_on `h.inst_opcode = RET`
        >- (gvs[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >> gvs[])
        >- gvs[]))
  >- (
    `rest_list = FST (rewrite_inline_insts ops outs ret insts pi')` by
      (Cases_on `rewrite_inline_insts ops outs ret insts pi'` >> gvs[]) >>
    gvs[])
QED


val _ = export_theory();
