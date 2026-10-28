(* TOP-LEVEL: finite paths of generated blocks and instruction prefixes imply
   frag_exec in the real containing function. The path can revisit loop blocks
   and stop inside the open continuation. No alternative evaluator is used. *)
Theory fragBlockPath
Ancestors
  fragExec exprLoweringProps compileEnv venomExecSemantics venomExecProofs
  venomState venomInst relation list rich_list arithmetic

(* A completed block transfers control to a block without leading PHIs.
   The lowering emits no PHIs; the premise is checked against the actual
   destination block rather than assumed for an unrelated block list. *)
Definition fragment_jump_def:
  fragment_jump ctx func ss out <=>
    ?fuel bb next_bb.
      lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
      exec_block fuel ctx bb ss = OK out /\
      lookup_block out.vs_current_bb func.fn_blocks = SOME next_bb /\
      phi_prefix_length next_bb.bb_instructions = 0
End

(* A prefix runs within the current block and stops before its terminator. *)
Definition fragment_prefix_def:
  fragment_prefix func ss out <=>
    ?bb insts result.
      lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX insts (DROP ss.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
      run_inst_seq insts ss = OK result /\
      out = result with vs_inst_idx := ss.vs_inst_idx + LENGTH insts
End

Definition fragment_step_def:
  fragment_step ctx func ss out <=>
    fragment_jump ctx func ss out \/ fragment_prefix func ss out
End

Definition fragment_path_def:
  fragment_path ctx func = RTC (fragment_step ctx func)
End

Theorem fragment_jump_continue:
  !ctx func ss out tail_fuel result.
    fragment_jump ctx func ss out /\
    run_from tail_fuel ctx func out = result /\ (!e. result <> Error e) ==>
    ?fuel. run_from fuel ctx func ss = result
Proof
  rpt gen_tac >> strip_tac >> fs[fragment_jump_def] >>
  rename1 `exec_block block_fuel ctx bb ss = OK out` >>
  `out.vs_inst_idx = 0 /\ ~out.vs_halted` by
    (conj_tac >- (drule_all exec_block_OK_inst_idx_0 >> simp[]) >>
     drule_all exec_block_OK_not_halted >> simp[]) >>
  `run_blocks (SUC tail_fuel) ctx func out = result` by
    (mp_tac (Q.SPECL [`tail_fuel`, `ctx`, `func`, `out`, `next_bb`]
       run_blocks_run_from_no_phi) >> simp[]) >>
  `exec_block (MAX block_fuel (SUC tail_fuel)) ctx bb ss = OK out` by
    (irule (cj 2 fuel_mono) >> simp[] >>
     qexists_tac `block_fuel` >> simp[MAX_DEF]) >>
  `run_blocks (MAX block_fuel (SUC tail_fuel)) ctx func out = result` by
    (irule (cj 3 fuel_mono) >> simp[] >>
     qexists_tac `SUC tail_fuel` >> simp[MAX_DEF]) >>
  qexists_tac `MAX block_fuel (SUC tail_fuel)` >> simp[run_from_def]
QED

Theorem run_inst_seq_continue:
  !insts ss out fuel ctx func bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX insts (DROP ss.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
    run_inst_seq insts ss = OK out ==>
    run_from fuel ctx func ss =
      run_from fuel ctx func
        (out with vs_inst_idx := ss.vs_inst_idx + LENGTH insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`insts`, `ss`, `fuel`, `ctx`, `bb`]
    exec_block_run_inst_seq) >> impl_tac >- simp[] >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `out` mp_tac) >> simp[] >> strip_tac >>
  simp[run_from_def]
QED

Theorem fragment_prefix_continue:
  !ctx func ss out fuel.
    fragment_prefix func ss out ==>
    run_from fuel ctx func ss = run_from fuel ctx func out
Proof
  rpt gen_tac >> strip_tac >> fs[fragment_prefix_def] >>
  drule_all run_inst_seq_continue >> simp[]
QED

Theorem fragment_step_continue:
  !ctx func ss out tail_fuel result.
    fragment_step ctx func ss out /\
    run_from tail_fuel ctx func out = result /\ (!e. result <> Error e) ==>
    ?fuel. run_from fuel ctx func ss = result
Proof
  rpt gen_tac >> simp[fragment_step_def] >> strip_tac
  >- (drule_all fragment_jump_continue >> simp[]) >>
  drule_all fragment_prefix_continue >>
  disch_then (qspecl_then [`ctx`, `tail_fuel`] assume_tac) >>
  qexists_tac `tail_fuel` >> simp[]
QED

Theorem fragment_path_continue:
  !ctx func ss out.
    fragment_path ctx func ss out ==>
    !tail_fuel result.
      run_from tail_fuel ctx func out = result /\ (!e. result <> Error e) ==>
      ?fuel. run_from fuel ctx func ss = result
Proof
  gen_tac >> gen_tac >> rewrite_tac[fragment_path_def] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `tail_fuel` >> simp[]) >>
  MAP_EVERY qx_gen_tac [`ss_start`, `ss_mid`, `ss_final`] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail_fuel result. _`
    (qspecl_then [`tail_fuel`, `result`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all fragment_step_continue >> simp[]
QED

Theorem frag_exec_fragment_path:
  !ctx cs cs' P Q R.
    (!func ss.
      fn_has_code cs cs' func /\ P ss /\
      ss.vs_current_bb = cs.cs_current_bb /\
      ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
      ?out. Q out /\ out.vs_current_bb = cs'.cs_current_bb /\
        out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
        fragment_path ctx func ss out) ==>
    frag_exec ctx cs cs' P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_def] >>
  MAP_EVERY qx_gen_tac [`func`, `ss`] >> strip_tac >>
  qpat_x_assum `!func ss. _` (qspecl_then [`func`, `ss`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  disj1_tac >> goal_assum drule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `out`] fragment_path_continue) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`fuel`, `run_from fuel ctx func out`] mp_tac) >> simp[]
QED

Theorem fragment_path_refl[simp]:
  !ctx func ss. fragment_path ctx func ss ss
Proof
  simp[fragment_path_def]
QED

Theorem fragment_path_trans:
  !ctx func ss mid out.
    fragment_path ctx func ss mid /\ fragment_path ctx func mid out ==>
    fragment_path ctx func ss out
Proof
  rpt gen_tac >> simp[fragment_path_def] >> strip_tac >>
  irule RTC_RTC >> qexists_tac `mid` >> simp[]
QED

Theorem fragment_path_prefix:
  !ctx func ss out bb insts.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX insts (DROP ss.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
    run_inst_seq insts ss = OK out ==>
    fragment_path ctx func ss
      (out with vs_inst_idx := ss.vs_inst_idx + LENGTH insts)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[fragment_path_def] >>
  irule RTC_SINGLE >> rewrite_tac[fragment_step_def] >> disj2_tac >>
  rewrite_tac[fragment_prefix_def] >> qexistsl_tac [`bb`, `insts`, `out`] >> simp[]
QED

Theorem fragment_path_emitted:
  !ctx func cs cs' ss out.
    fn_has_code cs cs' func /\ same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs') /\
    run_inst_seq (emitted_insts cs cs') ss = OK out ==>
    fragment_path ctx func ss (out with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
    out.vs_current_bb = cs'.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX cs'.cs_current_insts bb.bb_instructions` by
    fs[fn_has_code_def, same_blocks_def] >>
  `isPREFIX (emitted_insts cs cs') (DROP ss.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX cs'.cs_current_insts bb.bb_instructions` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `l` >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => PURE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `out.vs_current_bb = ss.vs_current_bb` by
    (mp_tac (Q.SPECL [`emitted_insts cs cs'`, `ss`, `0`, `ctx`, `bb`]
       exec_block_run_inst_seq) >> impl_tac >- simp[] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `out` mp_tac) >> simp[]) >>
  conj_tac
  >- (mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `out`, `bb`, `emitted_insts cs cs'`]
        fragment_path_prefix) >> simp[]) >>
  fs[same_blocks_def]
QED

Theorem fragment_jump_step:
  !ctx func ss out bb next_bb inst.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb ss.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ step_inst_base inst ss = OK out /\
    ~out.vs_halted /\
    lookup_block out.vs_current_bb func.fn_blocks = SOME next_bb /\
    phi_prefix_length next_bb.bb_instructions = 0 ==>
    fragment_jump ctx func ss out
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (drule_all step_inst_base_OK_not_INVOKE >> simp[]) >>
  rewrite_tac[fragment_jump_def] >> qexistsl_tac [`0`, `bb`, `next_bb`] >>
  simp[Once exec_block_def, step_inst_non_invoke]
QED

Theorem fragment_path_jump:
  !ctx func ss out.
    fragment_jump ctx func ss out ==> fragment_path ctx func ss out
Proof
  simp[fragment_path_def] >> rpt strip_tac >>
  irule RTC_SINGLE >> simp[fragment_step_def]
QED

Theorem get_instruction_suffix_last:
  !bb start prefix inst.
    DROP start bb.bb_instructions = prefix ++ [inst] ==>
    get_instruction bb (start + LENGTH prefix) = SOME inst
Proof
  rpt gen_tac >> DISCH_TAC >>
  `LENGTH prefix + 1 = LENGTH bb.bb_instructions - start` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `start + LENGTH prefix < LENGTH bb.bb_instructions` by decide_tac >>
  `EL (start + LENGTH prefix) bb.bb_instructions = inst` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``\is:instruction list. EL (LENGTH (prefix:instruction list)) is``) >>
     simp[EL_DROP, EL_APPEND2]) >>
  simp[get_instruction_def]
QED

Theorem exec_block_prefix_terminator:
  !prefix inst ss mid out fuel ctx bb.
    DROP ss.vs_inst_idx bb.bb_instructions = prefix ++ [inst] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
    run_inst_seq prefix ss = OK mid /\ is_terminator inst.inst_opcode /\
    step_inst_base inst (mid with vs_inst_idx := ss.vs_inst_idx + LENGTH prefix) = OK out /\
    ~out.vs_halted ==>
    mid.vs_current_bb = ss.vs_current_bb /\ exec_block fuel ctx bb ss = OK out
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `ss`, `fuel`, `ctx`, `bb`] exec_block_run_inst_seq) >>
  impl_tac >- simp[IS_PREFIX_APPEND] >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `mid` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (drule_all step_inst_base_OK_not_INVOKE >> simp[]) >>
  `get_instruction bb (ss.vs_inst_idx + LENGTH prefix) = SOME inst` by
    (irule get_instruction_suffix_last >> first_assum ACCEPT_TAC) >>
  fs[] >> simp[Once exec_block_def, step_inst_non_invoke]
QED

Theorem fragment_path_block:
  !ctx func ss mid out bb next_bb prefix inst.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    DROP ss.vs_inst_idx bb.bb_instructions = prefix ++ [inst] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
    run_inst_seq prefix ss = OK mid /\ is_terminator inst.inst_opcode /\
    step_inst_base inst (mid with vs_inst_idx := ss.vs_inst_idx + LENGTH prefix) = OK out /\
    ~out.vs_halted /\
    lookup_block out.vs_current_bb func.fn_blocks = SOME next_bb /\
    phi_prefix_length next_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss out
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `inst`, `ss`, `mid`, `out`, `0`, `ctx`, `bb`]
    exec_block_prefix_terminator) >> impl_tac >- simp[] >> strip_tac >>
  irule fragment_path_jump >> rewrite_tac[fragment_jump_def] >>
  qexistsl_tac [`0`, `bb`, `next_bb`] >> simp[]
QED

(* A bounded loop supplies one path per iteration. Its invariant can track
   the encoded prefix, untouched input payloads, allocation cells and SSA
   freshness. The iteration count is independent of execution fuel. *)
Theorem fragment_path_loop:
  !n ctx func loop_inv ss.
    loop_inv 0 ss /\
    (!i state. i < n /\ loop_inv i state ==>
      ?next. fragment_path ctx func state next /\ loop_inv (SUC i) next) ==>
    ?out. fragment_path ctx func ss out /\ loop_inv n out
Proof
  Induct_on `n`
  >- (rpt gen_tac >> strip_tac >> qexists_tac `ss` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?mid. fragment_path ctx func ss mid /\ loop_inv n mid` by
    (qpat_x_assum `!ctx func loop_inv ss. _` irule >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i state. _` irule >> simp[]) >>
  qpat_x_assum `!i state. _` (qspecl_then [`n`, `mid`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `loop_inv (SUC n) ss_final` >>
  qexists_tac `ss_final` >> simp[] >>
  irule fragment_path_trans >> qexists_tac `mid` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed block-path theorem: " ^ name)
  end)
  (DB.thms "fragBlockPath")
