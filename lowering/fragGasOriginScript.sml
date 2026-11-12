(* Prefix marks are fixed by raw compilation's explicit GAS sites.
   The recorder and memory check use the very same instruction fuel. *)
Theory fragGasOrigin
Ancestors
  gasEvents gasEventsFuel gasEventsContext gasCount fragGasMode fragGasPath fragGasPathMem fragGasFocus
  fragExec fragExecMem memSafeRun unitTransformDefs
  venomExecSemantics venomInst venomState list arithmetic pred_set

Definition gas_origin_edge_def:
  gas_origin_edge memory explicit ctx func s marks r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      marks = MAP (\key. key IN explicit)
        (gas_events_step fuel ctx func.fn_name inst s) /\
      (memory ==> revert_forward_at bb s.vs_inst_idx \/
                  mem_safe_step fuel ctx inst s) /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx)) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb func.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions)) \/
       (?lbl. is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
              middle = OK (jump_to lbl s) /\ r = middle) \/
       (exit_result middle /\ r = middle))
End

Inductive gas_origin_path:
  (!memory explicit ctx func s.
     ~s.vs_halted ==>
     gas_origin_path memory explicit ctx func s [] (OK s)) /\
  (!memory explicit ctx func s left mid right r.
     gas_origin_edge memory explicit ctx func s left (OK mid) /\
     gas_origin_path memory explicit ctx func mid right r ==>
     gas_origin_path memory explicit ctx func s (left ++ right) r) /\
  (!memory explicit ctx func s marks r.
     gas_origin_edge memory explicit ctx func s marks r /\
     exit_result r ==>
     gas_origin_path memory explicit ctx func s marks r)
End

Inductive gas_origin_focus:
  (!memory explicit ctx func s marks t.
     gas_origin_path memory explicit ctx func s marks (OK t) ==>
     gas_origin_focus memory explicit (ctx,func) s marks (func,t)) /\
  (!memory explicit ctx func s left mid right leaf t.
     gas_origin_path memory explicit ctx func s left (OK mid) /\
     gas_origin_focus memory explicit (ctx,func) mid right (leaf,t) ==>
     gas_origin_focus memory explicit (ctx,func) s (left ++ right) (leaf,t)) /\
  (!memory explicit ctx func s callee entered marks leaf t.
     gas_invoke_entry (ctx,func) s callee entered /\
     gas_origin_focus memory explicit (ctx,callee) entered marks (leaf,t) ==>
     gas_origin_focus memory explicit (ctx,func) s marks (leaf,t))
End

Theorem gas_path_edge_zero_origin:
  gas_path_edge ctx func s 0 r ==>
  gas_origin_edge F explicit ctx func s [] r
Proof
  rewrite_tac[gas_path_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (qx_choose_then `fuel` (qx_choose_then `bb`
    (qx_choose_then `inst` (qx_choose_then `middle` mp_tac)))) >>
  ntac 4 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >>
  `gas_events_step fuel ctx func.fn_name inst s = []` by
    metis_tac[cj 1 gas_events_length, LENGTH_NIL] >>
  rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[]
QED

Theorem gas_path_mem_edge_zero_origin:
  gas_path_mem_edge ctx func s 0 r ==>
  gas_origin_edge memory explicit ctx func s [] r
Proof
  rewrite_tac[gas_path_mem_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (qx_choose_then `fuel` (qx_choose_then `bb`
    (qx_choose_then `inst` (qx_choose_then `middle` mp_tac)))) >>
  ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >>
  `gas_events_step fuel ctx func.fn_name inst s = []` by
    metis_tac[cj 1 gas_events_length, LENGTH_NIL] >>
  rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[]
QED

Theorem gas_mem_edge_origin:
  gas_path_mem_edge ctx func s n r /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) ==>
  gas_origin_edge memory explicit ctx func s [(func.fn_name,id) IN explicit] r
Proof
  strip_tac >>
  qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_path_mem_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (qx_choose_then `fuel` (qx_choose_then `bb'`
    (qx_choose_then `inst` (qx_choose_then `middle` mp_tac)))) >>
  ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `inst = mk_inst id GAS [] [out]` by metis_tac[optionTheory.SOME_11] >>
  rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`fuel`, `bb'`, `inst`, `middle`] >>
  gvs[gas_events_step_def, mk_inst_def, is_terminator_def]
QED

Theorem gas_origin_edge_erase:
  gas_origin_edge memory explicit ctx func s marks r ==>
  gas_path_edge ctx func s (LENGTH marks) r /\
  (memory ==> gas_path_mem_edge ctx func s (LENGTH marks) r)
Proof
  rewrite_tac[gas_origin_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (qx_choose_then `fuel` (qx_choose_then `bb`
    (qx_choose_then `inst` (qx_choose_then `middle` mp_tac)))) >>
  ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_tac >>
  `LENGTH marks = gas_count_step fuel ctx inst s` by
    simp[gas_events_length] >>
  (conj_tac
   >- (rewrite_tac[gas_path_edge_def] >> conj_tac >- simp[] >>
       map_every qexists_tac [`fuel`, `bb`, `inst`, `middle`] >>
       gvs[] >> metis_tac[]) >>
   strip_tac >> rewrite_tac[gas_path_mem_edge_def] >>
   conj_tac >- simp[] >>
   map_every qexists_tac [`fuel`, `bb`, `inst`, `middle`] >>
   gvs[] >> metis_tac[])
QED

Theorem gas_origin_path_erase:
  !memory explicit ctx func s marks r.
    gas_origin_path memory explicit ctx func s marks r ==>
    gas_marked_path memory ctx func s (LENGTH marks) r
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `memory` >> gvs[gas_marked_path_def, LENGTH_APPEND] >>
  metis_tac[gas_origin_edge_erase, gas_path_rules, gas_path_mem_rules]
QED

Theorem gas_origin_focus_erase:
  !memory explicit p s marks q.
    gas_origin_focus memory explicit p s marks q ==>
    gas_focus_path memory p s (LENGTH marks) q
Proof
  ho_match_mp_tac gas_origin_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[LENGTH_APPEND] >>
  metis_tac[gas_origin_path_erase, gas_focus_path_rules]
QED

Theorem gas_path_zero_origin:
  !ctx func s n r.
    gas_path ctx func s n r ==>
    n = 0 ==> gas_origin_path F explicit ctx func s [] r
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[gas_path_edge_zero_origin, gas_origin_path_rules, APPEND_NIL]
QED

Theorem gas_path_mem_zero_origin:
  !ctx func s n r.
    gas_path_mem ctx func s n r ==>
    n = 0 ==> gas_origin_path memory explicit ctx func s [] r
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[gas_path_mem_edge_zero_origin, gas_origin_path_rules, APPEND_NIL]
QED

(* With no reached GAS reads, every fixed origin set gives the empty marks. *)
Theorem gas_marked_path_zero_origin:
  !memory explicit ctx func s r.
    gas_marked_path memory ctx func s 0 r ==>
    gas_origin_path memory explicit ctx func s [] r
Proof
  Cases_on `memory` >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_zero_origin, gas_path_mem_zero_origin]
QED

(* An origin path to an OK state continues along any origin path from it. *)
Theorem gas_origin_path_append:
  !memory explicit ctx func s left r.
    gas_origin_path memory explicit ctx func s left r ==>
    !mid right r'.
      r = OK mid /\ gas_origin_path memory explicit ctx func mid right r' ==>
      gas_origin_path memory explicit ctx func s (left ++ right) r'
Proof
  ho_match_mp_tac gas_origin_path_ind >> rw[] >> gvs[exit_result_def] >>
  metis_tac[gas_origin_path_rules, APPEND_ASSOC]
QED

Theorem gas_origin_events_extend[local]:
  n <= m /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  run_from n ctx func s = r /\ exit_result r ==>
  run_from m ctx func s = r /\
  gas_events_block m ctx func.fn_name bb s ++
    (case exec_block m ctx bb s of
       OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
     | _ => []) =
  gas_events_block n ctx func.fn_name bb s ++
    (case exec_block n ctx bb s of
       OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
     | _ => [])
Proof
  strip_tac >>
  `!e. exec_block n ctx bb s <> Error e` by
    (Cases_on `exec_block n ctx bb s` >> gvs[run_from_def, exit_result_def]) >>
  `exec_block m ctx bb s = exec_block n ctx bb s /\
   gas_events_block m ctx func.fn_name bb s =
     gas_events_block n ctx func.fn_name bb s` by
    metis_tac[cj 2 gas_events_fuel_extension] >>
  conj_tac
  >- metis_tac[gas_run_from_fuel_mono, exit_result_not_error] >>
  simp[] >> Cases_on `exec_block n ctx bb s` >> simp[] >>
  rename1 `exec_block n ctx bb s = OK u` >>
  Cases_on `u.vs_halted` >> simp[] >>
  `!e. run_blocks n ctx func u <> Error e` by
    (gvs[run_from_def] >> metis_tac[exit_result_not_error]) >>
  metis_tac[cj 3 gas_events_fuel_extension]
QED

(* A terminating continuation rules out the raw-jump edge's PHI prefix;
   the entered-block alternative already carries its actual PHI evaluation. *)
Theorem gas_origin_edge_events_continue:
  gas_origin_edge memory explicit ctx func s left (OK t) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME target /\
  run_from n ctx func t = r /\ exit_result r ==>
  ?m bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    run_from m ctx func s = r /\
    MAP (\key. key IN explicit)
      (gas_events_block m ctx func.fn_name bb s ++
       case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) =
    left ++ MAP (\key. key IN explicit)
      (gas_events_block n ctx func.fn_name target t ++
       case exec_block n ctx target t of
         OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
       | _ => [])
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def])
QED

Resume gas_origin_edge_events_continue[within]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  `stepped.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `bb = target` by gvs[] >> gvs[] >>
  `!e. exec_block n ctx bb
      (stepped with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
    (Cases_on `exec_block n ctx bb
      (stepped with vs_inst_idx := SUC s.vs_inst_idx)` >>
     gvs[run_from_def, exit_result_def]) >>
  drule_all gas_events_istep_continue >>
  disch_then (qspecl_then [`func.fn_name`, `n`] strip_assume_tac) >>
  gvs[] >>
  `!e. exec_block m ctx bb s <> Error e` by metis_tac[] >>
  `exec_block (MAX m n) ctx bb s = exec_block m ctx bb s /\
   gas_events_block (MAX m n) ctx func.fn_name bb s =
     gas_events_block m ctx func.fn_name bb s` by
    simp[cj 2 gas_events_fuel_extension, arithmeticTheory.MAX_LE] >>
  qexists_tac `MAX m n` >>
  Cases_on `exec_block n ctx bb
    (stepped with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[run_from_def, MAP_APPEND, APPEND_ASSOC] >>
  rename1 `exec_block n ctx bb
    (stepped with vs_inst_idx := SUC s.vs_inst_idx) = OK u` >>
  Cases_on `u.vs_halted` >> gvs[] >>
  `!e. run_blocks n ctx func u <> Error e` by metis_tac[exit_result_not_error] >>
  `run_blocks (MAX m n) ctx func u = run_blocks n ctx func u /\
   gas_events_blocks (MAX m n) ctx func u = gas_events_blocks n ctx func u` by
    simp[cj 3 gas_events_fuel_extension, arithmeticTheory.MAX_LE] >>
  simp[]
QED

Resume gas_origin_edge_events_continue[enter]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  rename1 `lookup_block stepped.vs_current_bb func.fn_blocks = SOME entered_bb` >>
  `entered.vs_current_bb = stepped.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `target = entered_bb` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `lookup_block entered.vs_current_bb _ = _` kall_tac >>
  gvs[] >>
  rename1 `eval_phis stepped target.bb_instructions = OK entered` >>
  `step_inst (SUC (MAX fuel n)) ctx inst s = OK stepped /\
   gas_events_step (SUC (MAX fuel n)) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    (qspecl_then [`fuel`, `ctx`, `func.fn_name`, `inst`, `s`,
       `SUC (MAX fuel n)`] mp_tac (cj 1 gas_events_fuel_extension) >>
     simp[arithmeticTheory.MAX_DEF]) >>
  `lookup_block
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions).vs_current_bb
     func.fn_blocks = SOME target` by simp[] >>
  `n <= MAX fuel n` by simp[] >>
  qmatch_asmsub_abbrev_tac `exit_result (run_from n ctx func entry)` >>
  `run_from n ctx func entry = run_from n ctx func entry` by simp[] >>
  drule_all gas_origin_events_extend >> strip_tac >>
  unabbrev_all_tac >>
  qexists_tac `SUC (MAX fuel n)` >>
  `run_blocks (SUC (MAX fuel n)) ctx func stepped =
    run_from (MAX fuel n) ctx func
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule run_blocks_run_from >> simp[]) >>
  conj_tac
  >- (simp[run_from_def, Once exec_block_def] >>
      gvs[run_from_def]) >>
  simp[Once gas_events_block_def, Once exec_block_def] >>
  simp[Once gas_events_blocks_def, MAP_APPEND, APPEND_ASSOC]
QED

Resume gas_origin_edge_events_continue[jump]:
  `?dest. lookup_block lbl func.fn_blocks = SOME dest /\
     phi_prefix_length dest.bb_instructions = 0` by
    (irule run_from_jump_target >> simp[] >> metis_tac[exit_result_not_error]) >>
  `dest = target` by gvs[jump_to_def] >> gvs[] >>
  `eval_phis (jump_to lbl s) dest.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  `step_inst (SUC n) ctx inst s = OK (jump_to lbl s)` by
    gvs[step_inst_non_invoke] >>
  `gas_events_step (SUC n) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    simp[gas_events_step_def] >>
  `jump_to lbl s with vs_inst_idx := 0 = jump_to lbl s` by
    simp[jump_to_def] >>
  qexists_tac `SUC n` >> conj_tac
  >- (irule run_from_jump_result >>
      simp[] >> metis_tac[step_inst_non_invoke, exit_result_not_error]) >>
  simp[Once gas_events_block_def, Once exec_block_def, jump_to_def] >>
  simp[Once gas_events_blocks_def, GSYM jump_to_def, MAP_APPEND, APPEND_ASSOC]
QED
Finalise gas_origin_edge_events_continue

(* Execution and the recorded sites share one fuel, including INVOKE callees. *)
Theorem gas_origin_path_events:
  gas_origin_path memory explicit ctx func s marks r /\ exit_result r ==>
  ?fuel bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    run_from fuel ctx func s = r /\
    marks = MAP (\key. key IN explicit)
      (gas_events_block fuel ctx func.fn_name bb s ++
       case exec_block fuel ctx bb s of
         OK s' => if s'.vs_halted then [] else gas_events_blocks fuel ctx func s'
       | _ => [])
Proof
  `!memory explicit ctx func s marks r.
    gas_origin_path memory explicit ctx func s marks r ==>
    exit_result r ==>
    ?fuel bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      run_from fuel ctx func s = r /\
      marks = MAP (\key. key IN explicit)
        (gas_events_block fuel ctx func.fn_name bb s ++
         case exec_block fuel ctx bb s of
           OK u => if u.vs_halted then [] else gas_events_blocks fuel ctx func u
         | _ => [])` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac
  >- simp[exit_result_def]
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      drule_all gas_origin_edge_events_continue >>
      disch_then (qx_choose_then `combined_fuel`
        (qx_choose_then `start_bb` strip_assume_tac)) >>
      qexistsl_tac [`combined_fuel`, `start_bb`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  rw[gas_origin_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >>
      simp[run_from_def, Once exec_block_def, Once gas_events_block_def] >>
      simp[Once exec_block_def]) >>
  qexists_tac `fuel` >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  simp[run_from_def, Once exec_block_def, Once gas_events_block_def] >>
      simp[Once exec_block_def]
QED
