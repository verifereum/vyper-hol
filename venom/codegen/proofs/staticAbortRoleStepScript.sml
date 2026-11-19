(* Concrete interpretation of a pending instruction row. *)
Theory staticAbortRoleStep
Ancestors
  staticAbortStraight staticAbortTerminal asmOpSim stackOpAsmSim genBlockSim
  asmIR asmSem asmSymSem asmOptimizer finite_map words list rich_list pred_set arithmetic

Theorem straight_preserves_stack_tail[local]:
  static_abort_straight name m /\
  asm_step lo otp (AsmOp name) t = AsmOK u ==>
  DROP m u.as_stack = DROP (asm_op_arity name) t.as_stack
Proof
  simp[static_abort_straight_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `asm_step _ _ _ _ = _` mp_tac >>
  (* Reduce the dispatcher in order, without unfolding unused branches. *)
  simp[asm_step_def, asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV asm_op_arity_def THENC EVAL)) >>
  simp[asm_pop_def, asm_mstore_def, asm_mstore8_def, asm_mcopy_def,
       asm_copy_to_mem_def, asm_returndatacopy_def, asm_extcodecopy_def,
       asm_binop_def, asm_unop_def, asm_ternop_def, asm_mload_def,
       asm_sload_def, asm_tload_def, asm_sha3_def, asm_push_val_def,
       asm_gas_def, asm_state_unop_def, asm_next_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Theorem role_tail_slot[local]:
  DROP m bs = DROP a ss /\ m <= k /\ k < LENGTH bs /\
  k-m+a < LENGTH ss ==>
  EL k bs = EL (k-m+a) ss
Proof
  strip_tac >>
  `k-m+m = k` by decide_tac >>
  metis_tac[listTheory.EL_DROP]
QED

Theorem role_step_dup[local]:
  ALOOKUP dup_table name = SOME n /\ n < LENGTH t.as_stack ==>
  asm_step lo otp (AsmOp name) t =
    AsmOK (asm_next (t with as_stack := EL n t.as_stack :: t.as_stack))
Proof
  simp[dup_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[] >> simp[asm_step_def, asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  simp[dup_table_def, asm_dup_def]
QED

Theorem role_step_swap[local]:
  ALOOKUP swap_table name = SOME n /\ 0 < n /\ n < LENGTH t.as_stack ==>
  ?u. asm_step lo otp (AsmOp name) t = AsmOK u /\
      u.as_pc = t.as_pc+1 /\ u.as_call_ctx = t.as_call_ctx /\
      u.as_requests = t.as_requests /\ LENGTH u.as_stack = LENGTH t.as_stack /\
      !k. k < LENGTH u.as_stack ==>
        EL k u.as_stack = EL (if k=0 then n else if k=n then 0 else k) t.as_stack
Proof
  simp[swap_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[] >> simp[asm_step_def, asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  simp[dup_table_def, swap_table_def] >>
  simp[asm_swap_def, asm_next_def] >>
  rpt strip_tac >> simp[EL_LUPDATE] >>
  Cases_on `k = 0` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem role_step_branch[local]:
  (name = "JUMP" \/ name = "JUMPI") /\
  asm_op_arity name <= LENGTH t.as_stack /\
  FLOOKUP otp (w2n (EL 0 t.as_stack)) = SOME dest ==>
  ?u. asm_step lo otp (AsmOp name) t = AsmOK u /\
      u.as_pc = (if name = "JUMPI" /\ EL 1 t.as_stack = 0w
                 then t.as_pc+1 else dest) /\
      u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
      u.as_stack = DROP (asm_op_arity name) t.as_stack
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `_ <= LENGTH _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >> strip_tac >>
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] >>
  simp[asm_step_jump, asm_step_jumpi, asm_jump_def, asm_jumpi_def,
       asm_next_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV asm_op_arity_def THENC EVAL)) >>
  gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem role_terminal_dispatch[local]:
  (name = "INVALID" \/
   (name = "REVERT" /\ 2 <= LENGTH t.as_stack) \/
   (MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
    t.as_call_ctx.cc_static /\ asm_op_arity name <= LENGTH t.as_stack)) ==>
  ?u. (asm_step lo otp (AsmOp name) t = AsmRevert u \/
       asm_step lo otp (AsmOp name) t = AsmFault u) /\
      u.as_requests = t.as_requests
Proof
  strip_tac
  >- simp[asm_step_invalid]
  >- (fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] >>
      gvs[stackOpAsmSimTheory.asm_step_revert, asm_revert_op_def]) >>
  `asm_step lo otp (AsmOp name) t = AsmFault (t with as_returndata := [])` by
    (irule static_abort_terminal_dispatch >> simp[]) >> simp[]
QED

Theorem role_shape_transfer[local]:
  !src fresh bnew (x:num#num) t.
  !lo. lo = SND(compute_label_offsets p) ==>
  !otp. otp = build_offset_to_pc p ==>
  !shaped. shaped = (\i (s:asm_state).
    s.as_pc = pc i /\ LENGTH s.as_stack = height i /\
    s.as_call_ctx = cc /\ s.as_requests = req /\
    (need i ==> s.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                  FLOOKUP otp off = SOME dest /\ EL k s.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
      (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w))) ==>
  shaped x t /\
  u.as_pc = pc y /\ LENGTH u.as_stack = height y /\
  u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
  (need y ==> cc.cc_static) /\
  (!k l origin. tag y k = SOME(l,origin) ==>
    k < height y /\ origin < LENGTH p /\
    (EL origin p = AsmPushLabel l \/
     (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
    ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
               FLOOKUP otp off = SOME dest) /\
  (!k a. k < height y /\ src k = SOME a /\ a < height x ==>
     EL k u.as_stack = EL a t.as_stack) /\
  (!k l origin. fresh k = SOME(l,origin) ==>
     ?off. FLOOKUP lo l = SOME off /\ EL k u.as_stack = (n2w off:bytes32)) /\
  (!k. bnew k ==> EL k u.as_stack = 0w \/ EL k u.as_stack = 1w) /\
  (!k l origin. tag y k = SOME(l,origin) ==>
     k < height y /\ (fresh k = SOME(l,origin) \/
     ?a. src k = SOME a /\ a < height x /\ tag x a = SOME(l,origin))) /\
  (!k. boolean y k ==> k < height y /\
     (bnew k \/ ?a. src k = SOME a /\ a < height x /\ boolean x a)) ==>
  shaped y u
Proof
  CONV_TAC (REDEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `(!k l origin. tag y k = SOME(l,origin) ==>
      ?off. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
            EL k u.as_stack = (n2w off:bytes32)) /\
   (!k. boolean y k ==> EL k u.as_stack = 0w \/ EL k u.as_stack = 1w)` by
    (metis_tac[]) >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!k l origin. tag y k = SOME(l,origin) ==> _ /\ origin < LENGTH p /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!k l origin. tag y k = SOME(l,origin) ==> ?off. _`
    (drule_then strip_assume_tac) >>
  gvs[]
QED

Theorem role_step_straight[local]:
  static_abort_straight name m /\ asm_op_arity name <= LENGTH t.as_stack ==>
  asm_step lo otp (AsmOp name) t = AsmFault (t with as_returndata := []) \/
  ?u. asm_step lo otp (AsmOp name) t = AsmOK u /\
      u.as_pc = t.as_pc+1 /\ u.as_call_ctx = t.as_call_ctx /\
      u.as_requests = t.as_requests /\
      LENGTH u.as_stack = LENGTH t.as_stack - asm_op_arity name + m /\
      !k. m <= k /\ k < LENGTH u.as_stack ==>
        EL k u.as_stack = EL (k-m+asm_op_arity name) t.as_stack
Proof
  strip_tac >> drule_all static_abort_straight_dispatch >>
  disch_then (qspecl_then [`otp`,`lo`] strip_assume_tac)
  >- (disj2_tac >> qexists `t'` >> simp[] >> rpt strip_tac >>
      `DROP m t'.as_stack = DROP (asm_op_arity name) t.as_stack` by
        metis_tac[straight_preserves_stack_tail] >>
      `k-m+asm_op_arity name = k+asm_op_arity name-m` by decide_tac >>
      `k-m+asm_op_arity name < LENGTH t.as_stack` by decide_tac >>
      `k < LENGTH t'.as_stack` by decide_tac >>
      metis_tac[role_tail_slot]) >>
  simp[]
QED

Theorem pending_role_step:
  !lo. lo = SND(compute_label_offsets p) ==>
  !otp. otp = build_offset_to_pc p ==>
  !S. S = (\(i:num#num) (s:asm_state).
    s.as_pc = pc i /\ LENGTH s.as_stack = height i /\
    s.as_call_ctx = cc /\ s.as_requests = req /\
    (need i ==> s.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                  FLOOKUP otp off = SOME dest /\ EL k s.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
      (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w))) ==>
  !ins. ins = EL (pc x) p ==>
  !hi. hi = height x ==>
  !fall. fall = (?y. edge x y /\ pc y = pc x+1) ==>
  !taken. taken = (?y. edge x y /\
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
      FLOOKUP otp off = SOME(pc y)) ==>
  pc x < LENGTH p /\ S x t /\
  (!y. edge x y ==>
    (!hj. hj = height y ==>
     !inherit. inherit = (\src fresh bnew.
       (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
            ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
       (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
     case ins of
       AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
     | AsmPush bs => hj = hi+1 /\
         inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
           (\k. k=0 /\ !s u. asm_step lo otp (AsmPush bs) s = AsmOK u ==>
                    (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
     | AsmPushLabel l => hj = hi+1 /\
         inherit (\k. if k=0 then NONE else SOME(k-1))
                 (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
     | AsmPushOfst l d => hj = hi+1 /\
         inherit (\k. if k=0 then NONE else SOME(k-1))
                 (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
     | AsmOp name =>
         (case ALOOKUP dup_table name of
            SOME n => n < hi /\ hj = hi+1 /\
              inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
          | NONE => case ALOOKUP swap_table name of
              SOME n => 0 < n /\ n < hi /\ hj = hi /\
                inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                        (\k. NONE) (\k. F)
            | NONE =>
                !a. a = asm_op_arity name ==>
                !m. m = hj + a - hi ==>
                a <= hi /\ hj = m+(hi-a) /\
                ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
                inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                  (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                    !s u. LENGTH s.as_stack=hi /\ asm_step lo otp ins s=AsmOK u ==>
                          (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
     | _ => F) /\ (need y ==> cc.cc_static) /\
     (!k l origin. tag y k = SOME(l,origin) ==>
       k < height y /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                  FLOOKUP otp off = SOME dest)) /\
  (case ins of
     AsmLabel l => fall
   | AsmPush bs => fall
   | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ fall
   | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ fall
   | AsmOp name =>
       (name = "INVALID" \/ (name = "REVERT" /\ 2 <= hi) \/
        (MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
         cc.cc_static /\ asm_op_arity name <= hi)) \/
       (case ALOOKUP dup_table name of
          SOME n => n < hi /\ fall
        | NONE => case ALOOKUP swap_table name of
            SOME n => 0 < n /\ n < hi /\ fall
          | NONE =>
              (name = "JUMP" /\ 1 <= hi /\ taken) \/
              (name = "JUMPI" /\ 2 <= hi /\ fall /\ taken) \/
              (?m. static_abort_straight name m /\ asm_op_arity name <= hi /\
                   fall /\ !y. edge x y ==> height y = hi-asm_op_arity name+m))
   | _ => F) ==>
  (?u. (asm_steps lo otp p 1 t = AsmRevert u \/
        asm_steps lo otp p 1 t = AsmFault u) /\ u.as_requests = req) \/
  (?y u. edge x y /\ asm_steps lo otp p 1 t = AsmOK u /\ S y u)
Proof
  CONV_TAC (REDEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) >>
  strip_tac >>
  qpat_x_assum `!y. edge x y ==> _` (mk_asm "edges") >>
  `t.as_pc < LENGTH p` by (asm_rewrite_tac[]) >>
  drule_then (rewrite_tac o single) asm_step_one >>
  qpat_assum `t.as_pc = pc x` (rewrite_tac o single) >>
  Cases_on `EL (pc x) p` >>
  qpat_x_assum `asm_inst_CASE _ _ _ _ _ _ _ _ _`
    (CHECK_ASSUME_TAC o BETA_RULE o REWRITE_RULE [asmIRTheory.asm_inst_case_def]) >>
  FIRST [rename1 `EL (pc x) p = AsmOp name` >> suspend "op",
         rename1 `EL (pc x) p = AsmPush bs` >> suspend "push",
         rename1 `EL (pc x) p = AsmPushLabel l` >> suspend "label_push",
         rename1 `EL (pc x) p = AsmPushOfst l delta` >> suspend "offset_push",
         rename1 `EL (pc x) p = AsmLabel l` >> suspend "label"]
QED

(* Instantiate only the three stack-flow maps.  Matching determines the
   program, observation functions, destination occurrence and result. *)
fun transfer_role src fresh bnew =
  match_mp_tac
    (CONV_RULE (REDEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV))
      (Q.SPECL [src,fresh,bnew] role_shape_transfer)) >>
  qexistsl [`x`,`t`];

fun select_role_edge rules =
  asm_x "edges" (qspec_then `y` mp_tac) >>
  asm_rewrite_tac [asmIRTheory.asm_inst_case_def] >> BETA_TAC >>
  asm_rewrite_tac (optionTheory.option_case_def :: rules) >> BETA_TAC >> strip_tac;

Resume pending_role_step[label]:
  qpat_x_assum `?y. edge x y /\ pc y = pc x+1` (qx_choose_then `y` strip_assume_tac) >>
  select_role_edge [] >> disj2_tac >> qexistsl [`y`,`asm_next t`] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- simp[asm_step_label_ok] >>
  transfer_role `\k. SOME k` `\k. NONE` `\k. F` >>
  simp[asm_next_def]
  >> (metis_tac[])
QED

fun choose_role_fall v =
  qpat_x_assum `?z. edge x z /\ pc z = pc x+1` (qx_choose_then v strip_assume_tac);

fun normal_role_result u step =
  disj2_tac >> qexistsl [`y`,u] >> conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- simp[step];

Resume pending_role_step[push]:
  choose_role_fall `y` >> select_role_edge [] >>
  normal_role_result
    `asm_next (t with as_stack := word_of_bytes F (0w:bytes32) (REVERSE bs) :: t.as_stack)`
    asm_step_push_ok >>
  transfer_role `\k. if k=0 then NONE else SOME(k-1)` `\k. NONE`
    `\k. k=0 /\ !s u. asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
           (AsmPush bs) s = AsmOK u ==> EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w` >>
  fs[asm_step_push_ok, asm_next_def, AllCaseEqs(), EL_CONS, PRE_SUB1] >>
  metis_tac[]
QED

Resume pending_role_step[label_push]:
  qpat_x_assum `IS_SOME _ /\ _` strip_assume_tac >>
  Cases_on `FLOOKUP (SND(compute_label_offsets p)) l` >>
  qpat_x_assum `IS_SOME _` mp_tac >> simp[] >>
  rename1 `FLOOKUP (SND(compute_label_offsets p)) l = SOME off` >>
  select_role_edge [] >>
  normal_role_result `asm_next (t with as_stack := n2w off :: t.as_stack)` asm_step_pushlabel_ok >>
  transfer_role `\k. if k=0 then NONE else SOME(k-1)`
    `\k. if k=0 then SOME(l:string,pc (x:num#num):num) else NONE` `\k. F` >>
  simp[asm_next_def, AllCaseEqs(), EL_CONS, PRE_SUB1] >> metis_tac[]
QED

Resume pending_role_step[offset_push]:
  qpat_x_assum `IS_SOME _ /\ _` strip_assume_tac >>
  Cases_on `FLOOKUP (SND(compute_label_offsets p)) l` >>
  qpat_x_assum `IS_SOME _` mp_tac >> simp[] >>
  rename1 `FLOOKUP (SND(compute_label_offsets p)) l = SOME off` >>
  select_role_edge [] >>
  normal_role_result `asm_next (t with as_stack := n2w (off + delta) :: t.as_stack)` asm_step_pushofst_ok >>
  transfer_role `\k. if k=0 then NONE else SOME(k-1)`
    `\k. if k=0 /\ (delta:num)=0 then SOME(l:string,pc (x:num#num):num) else NONE` `\k. F` >>
  simp[asm_next_def, AllCaseEqs(), EL_CONS, PRE_SUB1] >> metis_tac[]
QED

val terminal_role =
  disj1_tac >> qpat_assum `t.as_requests = req` (rewrite_tac o single o GSYM) >>
  irule role_terminal_dispatch >> asm_x "terminal" mp_tac >> asm_rewrite_tac [];

val reduce_normal_role =
  asm_x "normal" mp_tac >> asm_rewrite_tac [optionTheory.option_case_def] >> BETA_TAC;

val swap_role =
  rename1 `ALOOKUP swap_table name = SOME n` >> reduce_normal_role >>
  DISCH_THEN (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `y` strip_assume_tac))) >>
  select_role_edge [] >>
  `n < LENGTH t.as_stack` by simp[] >>
  drule_all role_step_swap >>
  disch_then (qspecl_then [`build_offset_to_pc p`, `SND(compute_label_offsets p)`]
                          (qx_choose_then `u` strip_assume_tac)) >>
  normal_role_result `u` TRUTH >>
  transfer_role `\k. SOME(if k=0 then (n:num) else if k=n then 0 else k)` `\k. NONE` `\k. F` >>
  simp[] >> metis_tac[];

val branch_arms =
  DISCH_THEN (DISJ_CASES_THEN2 (mk_asm "jump")
    (DISJ_CASES_THEN2 (mk_asm "jumpi") (mk_asm "straight")));

val straight_role =
  asm_x "straight" (qx_choose_then `m`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (qx_choose_then `y` strip_assume_tac) assume_tac)))) >>
  select_role_edge [] >>
  `asm_op_arity name <= LENGTH t.as_stack` by simp[] >>
  qpat_assum `!z. edge x z ==> height z = _` (drule_then assume_tac) >>
  `height y + asm_op_arity name - height x = m` by decide_tac >>
  drule_all role_step_straight >>
  disch_then (qspecl_then [`build_offset_to_pc p`, `SND(compute_label_offsets p)`]
    (DISJ_CASES_THEN2 assume_tac (qx_choose_then `u` strip_assume_tac)))
  >- (disj1_tac >> qexists `t with as_returndata := []` >> simp[]) >>
  normal_role_result `u` TRUTH >>
  transfer_role `\k. if k<(m:num) then NONE else SOME(k-m+asm_op_arity name)` `\k. NONE`
    `\k. k=0 /\ (m:num)=1 /\ asm_returns_zero_or_one (AsmOp name) /\
          !s u. LENGTH s.as_stack=height (x:num#num) /\
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmOp name) s = AsmOK u ==> EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w` >>
  fs[AllCaseEqs()] >> metis_tac[];

val choose_role_taken =
  qx_choose_then `taken` (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `lab` (qx_choose_then `orig` (qx_choose_then `off` strip_assume_tac))));

Resume pending_role_step[op]:
  qpat_x_assum `_ \/ (case ALOOKUP dup_table name of NONE => _ | SOME n => _)`
    (DISJ_CASES_THEN2 (mk_asm "terminal") (mk_asm "normal"))
  >- terminal_role >>
  reverse (Cases_on `ALOOKUP dup_table name`)
  >- (rename1 `ALOOKUP dup_table name = SOME n` >> reduce_normal_role >>
      DISCH_THEN (CONJUNCTS_THEN2 assume_tac (qx_choose_then `y` strip_assume_tac)) >>
      select_role_edge [] >>
      normal_role_result
        `asm_next (t with as_stack := EL n t.as_stack :: t.as_stack)` role_step_dup >>
      transfer_role `\k. SOME(if k=0 then (n:num) else k-1)` `\k. NONE` `\k. F` >>
      simp[asm_next_def] >>
      rpt conj_tac
      >~ [`EL _ (_::_)`]
      >- (rpt strip_tac >> Cases_on `k` >> simp[]) >>
      metis_tac[]) >>
  reverse (Cases_on `ALOOKUP swap_table name`) >- swap_role >>
  reduce_normal_role >> reverse branch_arms >- straight_role >>
  (asm_x "jumpi" (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (qx_choose_then `fall` strip_assume_tac) choose_role_taken)))
   ORELSE asm_x "jump" (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac choose_role_taken))) >>
  `asm_op_arity name <= LENGTH t.as_stack` by
    simp[EVAL ``asm_op_arity "JUMP"``, EVAL ``asm_op_arity "JUMPI"``] >>
  `EL 0 t.as_stack = (n2w off:bytes32)` by
    (qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
       (drule_then strip_assume_tac) >> fs[]) >>
  `FLOOKUP (build_offset_to_pc p) (w2n (EL 0 t.as_stack)) = SOME (pc taken)` by
    simp[w2n_n2w, LESS_MOD] >>
  (SUBGOAL_THEN ``name = "JUMP" \/ name = "JUMPI"`` ASSUME_TAC >- simp[]) >>
  drule_all role_step_branch >>
  disch_then (qspec_then `SND(compute_label_offsets p)`
    (qx_choose_then `u` strip_assume_tac)) >>
  qpat_x_assum `name = "JUMP" \/ name = "JUMPI"` kall_tac >>
  (reverse (qsuff_tac `?y. edge x y /\ pc y = u.as_pc`)
   >- (Cases_on `name = "JUMPI" /\ EL 1 t.as_stack = 0w` >>
       fs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `y` strip_assume_tac) >>
  select_role_edge
    [EVAL ``ALOOKUP dup_table "JUMP"``, EVAL ``ALOOKUP dup_table "JUMPI"``,
     EVAL ``ALOOKUP swap_table "JUMP"``, EVAL ``ALOOKUP swap_table "JUMPI"``] >>
  `height y + asm_op_arity name - height x = 0` by simp[] >>
  `height y = height x - asm_op_arity name` by simp[] >>
  normal_role_result `u` TRUTH >>
  transfer_role `\k. SOME(k+asm_op_arity name)` `\k. NONE` `\k. F` >>
  gvs[listTheory.LENGTH_DROP, listTheory.EL_DROP] >> metis_tac[]
QED

Finalise pending_role_step
