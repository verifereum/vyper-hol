(*
 * Run-block decomposition at a non-terminator instruction.
 *
 * Key lemmas:
 *   run_block_reaches_split — run_block decomposes at reached state
 *   run_block_truncated_at_k — truncated block execution
 *   run_block_decompose_at — one-step expansion at reached instruction
 *)

Theory functionInlinerBlockSplit
Ancestors venomExecSemantics venomInst venomExecProps

open listTheory rich_listTheory venomStateTheory
     venomExecSemanticsTheory venomInstTheory venomExecPropsTheory

(* Define: state after processing k non-terminator instructions *)
Definition run_block_reaches_def:
  (run_block_reaches fuel ctx bb s 0 = SOME s) /\
  (run_block_reaches fuel ctx bb s (SUC k) =
    case get_instruction bb s.vs_inst_idx of
      NONE => NONE
    | SOME inst =>
      if is_terminator inst.inst_opcode then NONE
      else
        case step_inst fuel ctx inst s of
          OK s' => run_block_reaches fuel ctx bb
                     (s' with vs_inst_idx := SUC s.vs_inst_idx) k
        | _ => NONE)
End

(* run_block_reaches_split: if prefix succeeds, run_block decomposes *)
Theorem run_block_reaches_split:
  !k fuel ctx bb s s_k.
    run_block_reaches fuel ctx bb s k = SOME s_k ==>
    run_block fuel ctx bb s = run_block fuel ctx bb s_k
Proof
  Induct_on `k`
  >- simp[run_block_reaches_def]
  >>
  rpt strip_tac >>
  fs[run_block_reaches_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  rename1 `_ = SOME inst` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `_ = OK s'` >>
  first_x_assum drule >> strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_block_def])) >>
  simp[]
QED

(* run_block_reaches gives inst_idx *)
Theorem run_block_reaches_inst_idx:
  !k fuel ctx bb s s_k.
    run_block_reaches fuel ctx bb s k = SOME s_k ==>
    s_k.vs_inst_idx = s.vs_inst_idx + k
Proof
  Induct_on `k`
  >- (simp[run_block_reaches_def] >> rpt strip_tac >> gvs[])
  >>
  rpt strip_tac >>
  fs[run_block_reaches_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  rename1 `_ = SOME inst` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `_ = OK s'` >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac step_inst_preserves_inst_idx >>
  gvs[is_terminator_def] >> simp[]
QED

(* Decompose run_block_reaches (SUC k) = SOME into its components *)
Theorem run_block_reaches_SUC:
  !k fuel ctx bb s s_k.
    run_block_reaches fuel ctx bb s (SUC k) = SOME s_k ==>
    ?inst s'. get_instruction bb s.vs_inst_idx = SOME inst /\
              ~is_terminator inst.inst_opcode /\
              step_inst fuel ctx inst s = OK s' /\
              run_block_reaches fuel ctx bb
                (s' with vs_inst_idx := SUC s.vs_inst_idx) k = SOME s_k
Proof
  rpt strip_tac >>
  fs[run_block_reaches_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >>
  Cases_on `step_inst fuel ctx x s` >> gvs[] >>
  metis_tac[]
QED

(* run_block_reaches only depends on instructions at indices
   inst_idx .. inst_idx+k-1. Two blocks with same instructions
   at those positions give the same result. *)
Theorem run_block_reaches_agree:
  !k fuel ctx bb1 bb2 s.
    (!i. s.vs_inst_idx + i < s.vs_inst_idx + k ==>
         get_instruction bb1 (s.vs_inst_idx + i) =
         get_instruction bb2 (s.vs_inst_idx + i)) ==>
    run_block_reaches fuel ctx bb1 s k =
    run_block_reaches fuel ctx bb2 s k
Proof
  Induct_on `k`
  >- simp[run_block_reaches_def]
  >>
  rpt strip_tac >>
  simp[run_block_reaches_def] >>
  `get_instruction bb1 s.vs_inst_idx =
   get_instruction bb2 s.vs_inst_idx` by (
    first_x_assum (qspec_then `0` mp_tac) >> simp[]
  ) >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  Cases_on `get_instruction bb2 s.vs_inst_idx` >> simp[] >>
  rename1 `_ = SOME inst` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `_ = OK s'` >>
  first_x_assum irule >>
  rpt strip_tac >>
  imp_res_tac step_inst_preserves_inst_idx >>
  gvs[is_terminator_def] >>
  `s.vs_inst_idx + (i + 1) < s.vs_inst_idx + SUC k` by decide_tac >>
  first_x_assum (qspec_then `i + 1` mp_tac) >>
  simp[arithmeticTheory.ADD1]
QED

(* Truncated block: TAKE k ++ [term] agrees with bb on first k instructions *)
Theorem run_block_reaches_take_agree:
  !k fuel ctx bb s term.
    s.vs_inst_idx = 0 /\
    k <= LENGTH bb.bb_instructions ==>
    run_block_reaches fuel ctx bb s k =
    run_block_reaches fuel ctx
      (bb with bb_instructions := TAKE k bb.bb_instructions ++ [term]) s k
Proof
  rpt strip_tac >>
  irule (GSYM run_block_reaches_agree) >>
  rpt strip_tac >>
  simp[get_instruction_def] >>
  `i < k` by decide_tac >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `i < LENGTH (TAKE k bb.bb_instructions ++ [term])` by
    simp[LENGTH_TAKE, LENGTH_APPEND] >>
  simp[] >>
  simp[EL_APPEND1, EL_TAKE, LENGTH_TAKE]
QED

(* After run_block_reaches, running truncated block from s_k processes term *)
Theorem run_block_truncated_at_k:
  !k fuel ctx bb s s_k term.
    run_block_reaches fuel ctx bb s k = SOME s_k /\
    s.vs_inst_idx = 0 /\
    k <= LENGTH bb.bb_instructions /\
    is_terminator term.inst_opcode ==>
    run_block fuel ctx
      (bb with bb_instructions := TAKE k bb.bb_instructions ++ [term]) s =
    (case step_inst fuel ctx term s_k of
       OK s' => if s'.vs_halted then Halt s' else OK s'
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s'
     | Error e => Error e)
Proof
  rpt strip_tac >>
  qabbrev_tac `bb_trunc = bb with bb_instructions :=
    TAKE k bb.bb_instructions ++ [term]` >>
  (* run_block_reaches for truncated block gives s_k *)
  `run_block_reaches fuel ctx bb_trunc s k = SOME s_k` by (
    `run_block_reaches fuel ctx bb_trunc s k =
     run_block_reaches fuel ctx bb s k` by (
      qunabbrev_tac `bb_trunc` >>
      irule (GSYM run_block_reaches_take_agree) >> simp[]
    ) >>
    simp[]
  ) >>
  (* run_block decomposes at s_k *)
  imp_res_tac run_block_reaches_split >>
  (* Now: run_block bb_trunc s = run_block bb_trunc s_k *)
  `run_block fuel ctx bb_trunc s = run_block fuel ctx bb_trunc s_k` by
    metis_tac[] >>
  simp[] >>
  (* s_k.vs_inst_idx = k *)
  `s_k.vs_inst_idx = k` by
    (imp_res_tac run_block_reaches_inst_idx >> gvs[]) >>
  (* At s_k, get_instruction bb_trunc gives term *)
  ONCE_REWRITE_TAC[run_block_def] >>
  `get_instruction bb_trunc s_k.vs_inst_idx = SOME term` by (
    qunabbrev_tac `bb_trunc` >>
    simp[get_instruction_def, LENGTH_TAKE, LENGTH_APPEND] >>
    simp[EL_APPEND2, LENGTH_TAKE]
  ) >>
  simp[]
QED

(* Full block decomposition: run_block on bb from 0 decomposes at
   instruction k (a non-terminator) as:
   prefix (reaches s_k) + step_inst at k + tail from inst_idx k+1 *)
(* Full block decomposition: run_block decomposes at the reached state *)
Theorem run_block_decompose_at:
  !k fuel ctx bb s s_k.
    run_block_reaches fuel ctx bb s k = SOME s_k /\
    s_k.vs_inst_idx < LENGTH bb.bb_instructions ==>
    run_block fuel ctx bb s =
    (let inst = EL s_k.vs_inst_idx bb.bb_instructions in
     case step_inst fuel ctx inst s_k of
       OK s' =>
         if is_terminator inst.inst_opcode then
           if s'.vs_halted then Halt s' else OK s'
         else
           run_block fuel ctx bb (s' with vs_inst_idx := SUC s_k.vs_inst_idx)
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s'
     | Error e => Error e)
Proof
  rpt strip_tac >> simp[LET_THM] >>
  imp_res_tac run_block_reaches_split >>
  `run_block fuel ctx bb s = run_block fuel ctx bb s_k` by metis_tac[] >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_block_def])) >>
  `get_instruction bb s_k.vs_inst_idx =
   SOME (EL s_k.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  pop_assum (fn eq => REWRITE_TAC[eq, optionTheory.option_case_def]) >>
  BETA_TAC >> REFL_TAC
QED

(* Helper: extract inner reaches from SUC case *)
Theorem run_block_reaches_SUC_OK[local]:
  !k fuel ctx bb s inst sn.
    run_block_reaches fuel ctx bb s (SUC k) = NONE /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK sn ==>
    run_block_reaches fuel ctx bb
      (sn with vs_inst_idx := SUC s.vs_inst_idx) k = NONE
Proof
  rpt strip_tac >>
  imp_res_tac step_inst_preserves_inst_idx >>
  fs[run_block_reaches_def, is_terminator_def]
QED

(* Generalized: works for any starting inst_idx *)
Theorem run_block_reaches_none_run_block_agree_gen[local]:
  !k fuel ctx bb1 bb2 s.
    run_block_reaches fuel ctx bb1 s k = NONE /\
    (!i. i < k ==>
         get_instruction bb1 (s.vs_inst_idx + i) =
         get_instruction bb2 (s.vs_inst_idx + i)) ==>
    run_block fuel ctx bb1 s = run_block fuel ctx bb2 s
Proof
  Induct_on `k` >- simp[run_block_reaches_def] >>
  rpt strip_tac >>
  `get_instruction bb1 s.vs_inst_idx =
   get_instruction bb2 s.vs_inst_idx` by (
    first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  (* Unroll both run_blocks *)
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_block_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[run_block_def])) >>
  (* get_instruction matches for both blocks *)
  Cases_on `get_instruction bb1 s.vs_inst_idx` >- fs[] >>
  rename1 `_ = SOME inst` >>
  `get_instruction bb2 s.vs_inst_idx = SOME inst` by fs[] >>
  fs[] >>
  Cases_on `is_terminator inst.inst_opcode` >- simp[] >>
  simp[] >>
  (* Now both sides: case step_inst ... of OK => recurse | _ => result *)
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  (* Only OK case survives — non-OK cases are identical on both sides *)
  rename1 `_ = OK sn` >>
  drule_all run_block_reaches_SUC_OK >> strip_tac >>
  imp_res_tac step_inst_preserves_inst_idx >>
  `sn.vs_inst_idx = s.vs_inst_idx` by fs[is_terminator_def] >>
  fs[] >>
  first_x_assum irule >> fs[] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem run_block_reaches_none_run_block_agree:
  !k fuel ctx bb1 bb2 s.
    s.vs_inst_idx = 0 /\
    run_block_reaches fuel ctx bb1 s k = NONE /\
    (!i. i < k ==>
         get_instruction bb1 i = get_instruction bb2 i) ==>
    run_block fuel ctx bb1 s = run_block fuel ctx bb2 s
Proof
  rpt strip_tac >>
  irule run_block_reaches_none_run_block_agree_gen >>
  qexists_tac `k` >> simp[]
QED

(* Corollary: TAKE k ++ [any_term] gives same run_block as bb
   when run_block_reaches fails at k *)
Theorem run_block_prefix_fail_take:
  !k fuel ctx bb s term.
    s.vs_inst_idx = 0 /\
    k <= LENGTH bb.bb_instructions /\
    run_block_reaches fuel ctx bb s k = NONE ==>
    run_block fuel ctx bb s =
    run_block fuel ctx
      (bb with bb_instructions := TAKE k bb.bb_instructions ++ [term]) s
Proof
  rpt strip_tac >>
  match_mp_tac run_block_reaches_none_run_block_agree >>
  qexists_tac `k` >> simp[] >>
  rpt strip_tac >>
  simp[get_instruction_def, EL_APPEND1, EL_TAKE, LENGTH_TAKE,
       LENGTH_APPEND]
QED

(* When prefix fails and all instructions before k are non-terminators,
   run_block returns non-OK.
   Generalized over inst_idx for the induction. *)
Theorem run_block_reaches_none_non_ok_gen[local]:
  !k fuel ctx bb s.
    run_block_reaches fuel ctx bb s k = NONE /\
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < s.vs_inst_idx + k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    !s'. run_block fuel ctx bb s <> OK s'
Proof
  Induct_on `k` >- simp[run_block_reaches_def] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
  `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by (
    res_tac >> simp[]) >>
  `get_instruction bb s.vs_inst_idx =
     SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  (* Unroll run_block_reaches SUC case *)
  qpat_x_assum `run_block_reaches _ _ _ _ (SUC _) = NONE` mp_tac >>
  simp[run_block_reaches_def] >>
  (* Case split on step_inst *)
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >> strip_tac >>
  (* All cases: unroll run_block one step *)
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  (* OK case only survives: step_inst = OK, run_block recurses *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!i. _ <= i /\ i < _ ==> _` irule >> simp[]
QED

Theorem run_block_reaches_none_non_ok:
  !k fuel ctx bb s.
    s.vs_inst_idx = 0 /\
    run_block_reaches fuel ctx bb s k = NONE /\
    k <= LENGTH bb.bb_instructions /\
    (!i. i < k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    !s'. run_block fuel ctx bb s <> OK s'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`k`, `fuel`, `ctx`, `bb`, `s`]
    run_block_reaches_none_non_ok_gen) >>
  simp[]
QED

val _ = export_theory();
