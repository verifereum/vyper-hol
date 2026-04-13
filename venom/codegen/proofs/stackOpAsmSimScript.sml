(*
 * Stack Operation -> Asm Simulation
 *
 * Per-asm-instruction AsmOK lemmas and composition.
 * Shows that non-terminal asm instructions (AsmPush, AsmPushLabel,
 * AsmLabel, AsmOp for POP/DUP/SWAP/MLOAD/MSTORE) always produce AsmOK
 * under appropriate conditions.
 *
 * KEY LEMMA: asm_steps_all_ok -- if each instruction in a non-jump block
 * produces AsmOK when reached, then asm_steps on the block produces AsmOK.
 *)


Theory stackOpAsmSim
Ancestors
  asmSem planExec codegenRel asmIR stackOpSim stackModel list rich_list arithmetic
Libs
  BasicProvers

(* Shared tactic for asm_step dispatch resolution *)
val asm_dispatch_ss = srw_ss();
val asm_dispatch_thms = [asm_step_def, asm_step_op_def,
  asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
  asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
  asm_step_copy_def, asm_step_context_def,
  dup_table_def, swap_table_def, log_table_def];

(* ===== Per-instruction AsmOK lemmas ===== *)

(* AsmPush always succeeds *)
Theorem asm_step_push_ok:
  !lo o2pc bs s.
    asm_step lo o2pc (AsmPush bs) s =
    AsmOK (asm_next (s with as_stack :=
      word_of_bytes F (0w:bytes32) (REVERSE bs) :: s.as_stack))
Proof
  simp[asm_step_def]
QED

(* AsmPushLabel succeeds when label exists *)
Theorem asm_step_pushlabel_ok:
  !lo o2pc l off s.
    FLOOKUP lo l = SOME off ==>
    asm_step lo o2pc (AsmPushLabel l) s =
    AsmOK (asm_next (s with as_stack := n2w off :: s.as_stack))
Proof
  simp[asm_step_def]
QED

(* AsmPushOfst succeeds when label exists *)
Theorem asm_step_pushofst_ok:
  !lo o2pc l delta off s.
    FLOOKUP lo l = SOME off ==>
    asm_step lo o2pc (AsmPushOfst l delta) s =
    AsmOK (asm_next (s with as_stack := n2w (off + delta) :: s.as_stack))
Proof
  simp[asm_step_def]
QED

(* AsmLabel always succeeds *)
Theorem asm_step_label_ok:
  !lo o2pc l s.
    asm_step lo o2pc (AsmLabel l) s = AsmOK (asm_next s)
Proof
  simp[asm_step_def]
QED

(* AsmOp "POP" succeeds when stack non-empty *)
Theorem asm_step_pop_ok:
  !lo o2pc (s1:asm_state).
    s1.as_stack <> [] ==>
    ?stk. asm_step lo o2pc (AsmOp "POP") s1 =
            AsmOK (asm_next (s1 with as_stack := stk)) /\
          LENGTH stk + 1 = LENGTH s1.as_stack
Proof
  rpt strip_tac >> Cases_on `s1.as_stack` >> fs[] >>
  simp[asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def,
       asm_pop_def] >>
  qexists_tac `t` >> simp[]
QED

(* AsmOp DUP: case-split on n for concrete dispatch resolution *)
Theorem asm_step_dup_ok:
  !lo o2pc n (s1:asm_state).
    n < 16 /\ n < LENGTH s1.as_stack ==>
    asm_step lo o2pc (AsmOp (dup_name (n + 1))) s1 =
    AsmOK (asm_next (s1 with as_stack :=
      EL n s1.as_stack :: s1.as_stack))
Proof
  rpt strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
   n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/
   n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/
   n = 12 \/ n = 13 \/ n = 14 \/ n = 15` by decide_tac >>
  gvs[dup_name_def] >>
  SIMP_TAC asm_dispatch_ss (asm_dispatch_thms @ [asm_dup_def, asm_next_def]) >>
  fs[]
QED

(* AsmOp SWAP: case-split on n for concrete dispatch resolution *)
Theorem asm_step_swap_ok:
  !lo o2pc n (s1:asm_state).
    0 < n /\ n <= 16 /\ n < LENGTH s1.as_stack ==>
    asm_step lo o2pc (AsmOp (swap_name n)) s1 =
    AsmOK (asm_next (s1 with as_stack :=
      LUPDATE (HD s1.as_stack) n (LUPDATE (EL n s1.as_stack) 0 s1.as_stack)))
Proof
  rpt strip_tac >>
  `n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/
   n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/
   n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/
   n = 13 \/ n = 14 \/ n = 15 \/ n = 16` by decide_tac >>
  gvs[swap_name_def] >>
  SIMP_TAC asm_dispatch_ss
    (asm_dispatch_thms @ [asm_swap_def, asm_next_def, LET_THM]) >>
  fs[]
QED

(* AsmOp "MLOAD" succeeds when stack non-empty *)
Theorem asm_step_mload_ok:
  !lo o2pc (s1:asm_state).
    s1.as_stack <> [] ==>
    ?s2. asm_step lo o2pc (AsmOp "MLOAD") s1 = AsmOK s2 /\
         s2.as_pc = s1.as_pc + 1 /\
         LENGTH s2.as_stack = LENGTH s1.as_stack
Proof
  rpt strip_tac >> Cases_on `s1.as_stack` >> fs[] >>
  simp[asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def,
       asm_mload_def, LET_THM, asm_next_def]
QED

(* AsmOp "MSTORE" succeeds when stack has >= 2 elements *)
Theorem asm_step_mstore_ok:
  !lo o2pc (s1:asm_state).
    LENGTH s1.as_stack >= 2 ==>
    ?s2. asm_step lo o2pc (AsmOp "MSTORE") s1 = AsmOK s2 /\
         s2.as_pc = s1.as_pc + 1 /\
         LENGTH s2.as_stack + 2 = LENGTH s1.as_stack
Proof
  rpt strip_tac >>
  `?v1 v2 rest. s1.as_stack = v1 :: v2 :: rest` by (
    Cases_on `s1.as_stack` >> fs[] >>
    Cases_on `t` >> fs[]
  ) >>
  simp[asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def,
       asm_mstore_def, LET_THM, asm_next_def]
QED

(* ===== Terminal instruction steps ===== *)

Theorem asm_step_stop:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "STOP") s =
    AsmHalt (s with as_returndata := [])
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_invalid:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "INVALID") s =
    AsmFault (s with as_returndata := [])
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_jumpi:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "JUMPI") s = asm_jumpi o2pc s
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_iszero:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "ISZERO") s =
    asm_unop (\x. b2w (x = 0w)) s
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_return:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "RETURN") s = asm_return_op s
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_revert:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "REVERT") s = asm_revert_op s
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

Theorem asm_step_selfdestruct:
  !lo o2pc (s:asm_state).
    asm_step lo o2pc (AsmOp "SELFDESTRUCT") s = asm_selfdestruct s
Proof
  SIMP_TAC asm_dispatch_ss asm_dispatch_thms
QED

(* ===== Composition: sequential all-ok execution ===== *)

(* Helper: step (SUC n) = step 0 then step n from result *)
Theorem asm_steps_suc_ok[local]:
  !lo o2pc prog (s1:asm_state) s2 n.
    s1.as_pc < LENGTH prog /\
    asm_step lo o2pc (EL s1.as_pc prog) s1 = AsmOK s2 ==>
    asm_steps lo o2pc prog (SUC n) s1 = asm_steps lo o2pc prog n s2
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[asm_steps_def] >>
  `~(s1.as_pc >= LENGTH prog)` by decide_tac >>
  ASM_REWRITE_TAC[] >>
  SIMP_TAC (srw_ss()) []
QED

(* Key composition lemma: if each instruction produces AsmOK when reached,
   then asm_steps on the block produces AsmOK.
   Requires non-JUMP/JUMPI for PC advance. *)
Theorem asm_steps_all_ok:
  !n lo o2pc prog (s1:asm_state) insts.
    asm_block_at prog s1.as_pc insts /\
    n <= LENGTH insts /\
    EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI") insts /\
    (!i si. i < n /\ asm_steps lo o2pc prog i s1 = AsmOK si ==>
            ?si'. asm_step lo o2pc (EL i insts) si = AsmOK si') ==>
    ?s2. asm_steps lo o2pc prog n s1 = AsmOK s2
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  (* Facts from asm_block_at *)
  `s1.as_pc + LENGTH insts <= LENGTH prog /\
   (!j. j < LENGTH insts ==> EL (s1.as_pc + j) prog = EL j insts)` by
    fs[asm_block_at_def] >>
  `s1.as_pc < LENGTH prog` by decide_tac >>
  `0 < LENGTH insts` by decide_tac >>
  `EL s1.as_pc prog = EL 0 insts` by (res_tac >> fs[]) >>
  (* Step 0 produces AsmOK *)
  `?s0'. asm_step lo o2pc (EL 0 insts) s1 = AsmOK s0'` by (
    qpat_assum `!i si. i < SUC n /\ _ ==> _`
      (qspecl_then [`0`, `s1`] mp_tac) >>
    simp[asm_steps_def]
  ) >>
  (* PC advances by 1 *)
  `EL 0 insts <> AsmOp "JUMP" /\ EL 0 insts <> AsmOp "JUMPI"` by
    (Cases_on `insts` >> fs[EVERY_DEF]) >>
  `s0'.as_pc = s1.as_pc + 1` by
    metis_tac[asm_step_pc_advance] >>
  (* SUC n steps from s1 = n steps from s0' *)
  `asm_step lo o2pc (EL s1.as_pc prog) s1 = AsmOK s0'` by
    ASM_REWRITE_TAC[] >>
  drule_all asm_steps_suc_ok >> disch_tac >>
  (* Suffices: ?s2. asm_steps n s0' = AsmOK s2 *)
  `?s2. asm_steps lo o2pc prog n s0' = AsmOK s2` suffices_by
    metis_tac[] >>
  (* Apply IH *)
  first_x_assum match_mp_tac >>
  qexists_tac `TL insts` >>
  rpt conj_tac
  >- (Cases_on `insts` >> fs[asm_block_at_cons])
  >- (Cases_on `insts` >> fs[])
  >- (Cases_on `insts` >> fs[])
  >- (rpt strip_tac >>
      (* asm_steps (SUC i) s1 = AsmOK si by transitivity *)
      qpat_assum `!i si. i < SUC n /\ _ ==> _`
        (qspecl_then [`SUC i`, `si`] mp_tac) >>
      impl_tac >- (
        conj_tac >- decide_tac >>
        (* asm_steps (SUC i) s1 = asm_steps i s0' = AsmOK si *)
        qpat_assum `!n'. asm_steps _ _ _ (SUC n') s1 = _`
          (qspec_then `i` (SUBST1_TAC)) >>
        FIRST_ASSUM ACCEPT_TAC
      ) >>
      strip_tac >>
      `EL (SUC i) insts = EL i (TL insts)` by
        (Cases_on `insts` >> fs[]) >>
      metis_tac[]
  )
QED

(* One terminal step from asm_block_at *)
Theorem asm_one_step_result:
  !lo o2pc prog (s:asm_state) name result.
    asm_block_at prog s.as_pc [AsmOp name] /\
    asm_step lo o2pc (AsmOp name) s = result /\
    (?s'. result = AsmHalt s' \/ result = AsmRevert s' \/
          result = AsmFault s') ==>
    asm_steps lo o2pc prog 1 s = result
Proof
  rpt strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[asm_steps_def] >>
  fs[asm_block_at_def]
QED
