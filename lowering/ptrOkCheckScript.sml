(* Soundness of vyperCompiler's ptr_ok_check: a unit without DALLOCA that
 * passes it has every function pointer-confined (ptrDiscipline's fn_ptr_ok),
 * with the pointer parameters it computes.
 *
 * TOP-LEVEL:
 *   pv_closure_set -- a closed list closure is pointer_derived_vars
 *   fn_ptr_ok_check_sound, ptr_ok_check_sound
 *)
Theory ptrOkCheck
Ancestors
  vyperCompiler ptrDiscipline pointerConfinedDefs unitShapeDefs
  codegenReadyCompute venomInst list pred_set While


(* ===== The closure ===== *)


Theorem pointer_use_step_cong[local]:
  !fn l1 l2. set l1 = set l2 ==>
             pointer_use_step fn l1 = pointer_use_step fn l2
Proof
  rpt strip_tac >>
  `!v. MEM v l1 <=> MEM v l2` by fs[EXTENSION] >>
  simp[pointer_use_step_def]
QED

Theorem pointer_use_step_step_cong[local]:
  !fn l1 l2. set l1 = set l2 ==>
    (pointer_use_step_step fn l1 = NONE <=>
     pointer_use_step_step fn l2 = NONE) /\
    !a b. pointer_use_step_step fn l1 = SOME a /\
          pointer_use_step_step fn l2 = SOME b ==> set a = set b
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v l1 <=> MEM v l2` by fs[EXTENSION] >>
  drule_then (qspec_then `fn` assume_tac) pointer_use_step_cong >>
  simp[pointer_use_step_step_def] >> rw[] >> gvs[]
QED

Theorem pointer_use_vars_fuel_owhile[local]:
  !n fn l0 l.
    set l = set l0 /\
    pointer_use_step_step fn (pointer_use_vars_fuel n fn l0) = NONE ==>
    ?r. OWHILE ISL (\v. case pointer_use_step_step fn (OUTL v) of
                          NONE => INR (OUTL v)
                        | SOME vs => INL vs) (INL l) = SOME (INR r) /\
        set r = set (pointer_use_vars_fuel n fn l0)
Proof
  Induct >> rpt strip_tac
  >- (gvs[pointer_use_vars_fuel_def] >>
      `pointer_use_step_step fn l = NONE` by
        metis_tac[pointer_use_step_step_cong] >>
      ONCE_REWRITE_TAC [OWHILE_THM] >> simp[] >>
      ONCE_REWRITE_TAC [OWHILE_THM] >> simp[]) >>
  Cases_on `pointer_use_step_step fn l0` >> gvs[pointer_use_vars_fuel_def]
  >- (`pointer_use_step_step fn l = NONE` by
        metis_tac[pointer_use_step_step_cong] >>
      ONCE_REWRITE_TAC [OWHILE_THM] >> simp[] >>
      ONCE_REWRITE_TAC [OWHILE_THM] >> simp[]) >>
  rename1 `pointer_use_step_step fn l0 = SOME vs0` >>
  `?vs. pointer_use_step_step fn l = SOME vs /\ set vs = set vs0` by
    (Cases_on `pointer_use_step_step fn l` >>
     metis_tac[pointer_use_step_step_cong, optionTheory.NOT_NONE_SOME]) >>
  ONCE_REWRITE_TAC [OWHILE_THM] >> simp[]
QED

Theorem pv_closure_set:
  !fn roots vs. pv_closure fn roots = SOME vs ==>
                pointer_derived_vars fn (set roots) = set vs
Proof
  rw[pv_closure_def, pointer_derived_vars_def, pointer_use_vars_def] >>
  qspecl_then [`LENGTH (fn_insts fn) + 1`, `fn`, `roots`,
               `SET_TO_LIST (set roots)`] mp_tac pointer_use_vars_fuel_owhile >>
  simp[SET_TO_LIST_INV] >> strip_tac >> simp[]
QED

(* ===== The roots ===== *)

Theorem MEM_opcode_root_list[local]:
  !opc fn out.
    MEM out (opcode_root_list opc fn) <=>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = opc /\
           inst_output inst = SOME out
Proof
  simp[opcode_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac
  >- (Cases_on `inst.inst_opcode = opc` >> gvs[] >>
      Cases_on `inst_output inst` >> gvs[] >>
      qexists_tac `inst` >> simp[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem MEM_param_root_list[local]:
  !pl fn out.
    MEM out (param_root_list pl fn) <=>
    ?inst idx. MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
               inst.inst_operands = [Lit idx] /\ MEM (w2n idx) pl /\
               inst_output inst = SOME out
Proof
  simp[param_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac
  >- (Cases_on `inst.inst_opcode = PARAM` >> gvs[] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      rename1 `inst.inst_operands = op1::rest` >>
      Cases_on `op1` >> gvs[] >> Cases_on `rest` >> gvs[] >>
      Cases_on `inst_output inst` >> gvs[] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      qexists_tac `inst` >> gvs[] >> Cases_on `MEM (w2n idx) pl` >> gvs[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem ptr_roots_lists[local]:
  !PL fn.
    let ar = opcode_root_list ALLOCA fn in
    let pr = opcode_root_list DALLOCA fn ++ param_root_list (PL fn.fn_name) fn in
      set (ar ++ pr) = ptr_roots (\nm. set (PL nm)) fn /\
      set ar = alloca_roots fn /\
      set (FILTER (\v. ~MEM v ar) pr) =
        ptr_roots (\nm. set (PL nm)) fn DIFF alloca_roots fn
Proof
  rw[EXTENSION, ptr_roots_def, alloca_roots_def, MEM_FILTER,
     MEM_opcode_root_list, MEM_param_root_list] >>
  metis_tac[]
QED

(* ===== Soundness ===== *)

Theorem invoke_args_ok_mem[local]:
  !args pl pv k j v.
    invoke_args_ok pl pv k args /\ j < LENGTH args /\
    EL j args = Var v /\ MEM v pv ==> MEM (k + j) pl
Proof
  Induct >> simp[invoke_args_ok_def] >> rpt strip_tac >>
  Cases_on `j` >> gvs[] >>
  first_x_assum drule_all >> simp[arithmeticTheory.ADD1]
QED

Theorem two_var_case[local]:
  !ops P. (case ops of [Var u; Var w] => P u w | _ => F) <=>
          ?u w. ops = [Var u; Var w] /\ P u w
Proof
  rpt gen_tac >> Cases_on `ops` >- simp[] >>
  rename1 `op1::rest` >> Cases_on `op1` >> simp[] >>
  Cases_on `rest` >- simp[] >>
  rename1 `op2::rest2` >> Cases_on `op2` >> simp[] >>
  Cases_on `rest2` >> simp[]
QED

Theorem ptr_cmp_exempt_alt[local]:
  !pv inst. ptr_cmp_exempt pv inst <=>
            (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
             inst.inst_opcode = EQ) /\
            ?u w. inst.inst_operands = [Var u; Var w] /\ MEM u pv /\ MEM w pv
Proof
  rw[ptr_cmp_exempt_def, two_var_case]
QED

Theorem addr_operand_is_alt[local]:
  !v inst. addr_operand_is v inst <=>
           ?ops. (mem_write_ops inst = SOME ops \/
                  mem_read_ops inst = SOME ops) /\ ops.iao_ofst = Var v
Proof
  rw[addr_operand_is_def] >>
  Cases_on `mem_write_ops inst` >> Cases_on `mem_read_ops inst` >> simp[] >>
  metis_tac[]
QED

Theorem ptr_use_ok_check_sound[local]:
  !PL pv inst. ptr_use_ok_check PL pv inst ==>
               ptr_use_ok (\nm. set (PL nm)) (set pv) inst
Proof
  rw[ptr_use_ok_check_def, ptr_use_ok_def]
  >- (Cases_on `decode_invoke inst` >> gvs[] >>
      rename1 `decode_invoke inst = SOME call` >> PairCases_on `call` >> gvs[] >>
      rpt strip_tac >> drule_all invoke_args_ok_mem >> simp[]) >>
  fs[EVERY_MEM] >> first_x_assum drule >> simp[] >>
  impl_tac
  >- (simp[ptr_cmp_exempt_alt] >> strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[]) >>
  simp[addr_operand_is_alt] >> rpt strip_tac >> gvs[ptr_cmp_exempt_alt]
QED

Theorem lit_case[local]:
  !ops P. (case ops of [Lit idx] => P idx | _ => F) <=>
          ?idx. ops = [Lit idx] /\ P idx
Proof
  rpt gen_tac >> Cases_on `ops` >- simp[] >>
  rename1 `op1::rest` >> Cases_on `op1` >> simp[] >>
  Cases_on `rest` >> simp[]
QED

Theorem pv_def_check_sound[local]:
  !pl ar pv inst v.
    pv_def_check pl ar pv inst /\ MEM v inst.inst_outputs /\ MEM v pv ==>
    inst.inst_opcode = ALLOCA \/
    ((inst.inst_opcode = DALLOCA \/
      (inst.inst_opcode = PARAM /\
       ?idx. inst.inst_operands = [Lit idx] /\ MEM (w2n idx) pl)) /\
     ~MEM v ar) \/
    (is_pointer_preserving_op inst.inst_opcode /\
     ?u. MEM (Var u) inst.inst_operands /\ MEM u pv)
Proof
  rpt strip_tac >> fs[pv_def_check_def, EVERY_MEM] >>
  first_x_assum drule_all >> simp[lit_case, EXISTS_MEM] >>
  strip_tac >> gvs[] >>
  Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem fn_ptr_ok_check_sound_aux[local]:
  !PL fn pv pva pvo ar.
    pointer_derived_vars fn (ptr_roots (\nm. set (PL nm)) fn) = set pv /\
    pointer_derived_vars fn (alloca_roots fn) = set pva /\
    pointer_derived_vars fn
      (ptr_roots (\nm. set (PL nm)) fn DIFF alloca_roots fn) = set pvo /\
    set ar = alloca_roots fn /\
    fn.fn_forced_alloc_positions = FEMPTY /\
    (!inst. MEM inst (fn_insts fn) ==>
            inst_ptr_ok_check PL pv inst /\ affine_check pv inst /\
            phi_check pv inst /\ write_excl_check pva pvo inst /\
            pv_def_check (PL fn.fn_name) ar pv inst) ==>
    fn_ptr_ok (\nm. set (PL nm)) fn
Proof
  rpt gen_tac >> strip_tac >>
  `!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
             MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  simp[fn_ptr_ok_def, fn_pv_def, affine_pointer_ops_def,
       phi_pv_all_var_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >>
      simp[inst_ptr_ok_check_def] >> strip_tac >> conj_tac
      >- (rpt strip_tac >> fs[EVERY_MEM] >> res_tac >> fs[]) >>
      conj_tac
      >- (rpt strip_tac >>
          `EXISTS (\op. case op of Var v => MEM v pv | _ => F)
             inst.inst_operands` by
            (simp[EXISTS_MEM] >> qexists `Var v` >> simp[]) >>
          `EVERY (\op. case op of Label _ => F | _ => T)
             inst.inst_operands` by gvs[] >>
          fs[EVERY_MEM] >> res_tac >> fs[]) >>
      irule ptr_use_ok_check_sound >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `affine_check pv inst` by metis_tac[] >>
      gvs[affine_check_def] >> rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      `phi_check pv inst` by metis_tac[] >>
      gvs[phi_check_def, EXISTS_MEM, EVERY_MEM, PULL_EXISTS] >>
      first_x_assum drule >> simp[] >> strip_tac >> rpt strip_tac
      >- (first_x_assum drule >> simp[]) >>
      first_x_assum drule >> Cases_on `op` >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `write_excl_check pva pvo inst` by metis_tac[] >>
      gvs[write_excl_check_def]) >>
  rpt gen_tac >> strip_tac >>
  `pv_def_check (PL fn.fn_name) ar pv inst` by metis_tac[] >>
  drule_all pv_def_check_sound >> qpat_x_assum `set ar = _` (SUBST1_TAC o SYM) >>
  simp[]
QED

Theorem fn_ptr_ok_check_sound:
  !PL fn. fn_ptr_ok_check PL fn ==> fn_ptr_ok (\nm. set (PL nm)) fn
Proof
  rpt gen_tac >> simp_tac std_ss [fn_ptr_ok_check_def, LET_THM] >>
  Cases_on `pv_closure fn (opcode_root_list ALLOCA fn ++
              (opcode_root_list DALLOCA fn ++
               param_root_list (PL fn.fn_name) fn))` >>
  simp_tac std_ss [] >>
  Cases_on `pv_closure fn (opcode_root_list ALLOCA fn)` >>
  simp_tac std_ss [] >>
  Cases_on `pv_closure fn (FILTER (\v. ~MEM v (opcode_root_list ALLOCA fn))
              (opcode_root_list DALLOCA fn ++
               param_root_list (PL fn.fn_name) fn))` >>
  simp[] >> strip_tac >>
  qspecl_then [`PL`, `fn`] mp_tac ptr_roots_lists >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  irule fn_ptr_ok_check_sound_aux >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rename1 `pv_closure fn (opcode_root_list ALLOCA fn ++ _) = SOME pv_all` >>
  rename1 `pv_closure fn (opcode_root_list ALLOCA fn) = SOME pv_a` >>
  rename1 `pv_closure fn (FILTER _ _) = SOME pv_o` >>
  qexistsl_tac [`opcode_root_list ALLOCA fn`, `pv_all`, `pv_a`, `pv_o`] >>
  imp_res_tac pv_closure_set >>
  conj_tac >- fs[EVERY_MEM] >>
  rpt conj_tac >> metis_tac[]
QED

(* With no PHIs, reachable_inst is the identity, and for a well-formed
   function cfg_analyze marks exactly the reachable blocks. *)
Theorem fn_reachable_blocks_reachable_fn:
  !fn. wf_function fn /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) ==>
       fn_reachable_blocks fn = reachable_fn fn
Proof
  rw[fn_reachable_blocks_def, reachable_fn_def,
     ir_function_component_equality] >>
  `!bb. MEM bb fn.fn_blocks ==>
        bb with bb_instructions :=
          MAP (reachable_inst fn bb.bb_label) bb.bb_instructions = bb` by
    (rw[basic_block_component_equality] >>
     `MAP (reachable_inst fn bb.bb_label) bb.bb_instructions =
      MAP (\x. x) bb.bb_instructions` suffices_by simp[] >>
     simp[MAP_EQ_f] >> rpt strip_tac >>
     irule (cj 3 reachable_inst_fields) >>
     fs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `!bbs. (!bb. MEM bb bbs ==> MEM bb fn.fn_blocks) ==>
     FILTER (\bb. cfg_reachable_of (cfg_analyze fn) bb.bb_label) bbs =
     MAP (\bb. bb with bb_instructions :=
                 MAP (reachable_inst fn bb.bb_label) bb.bb_instructions)
       (FILTER (\bb. fn_reachable fn bb.bb_label) bbs)` suffices_by simp[] >>
  Induct >> rw[] >>
  gvs[codegenReadyComputeTheory.fn_reachable_cfg_analyze, DISJ_IMP_THM,
      FORALL_AND_THM]
QED

Theorem ptr_ok_check_sound:
  !ctx. ptr_ok_check ctx /\ ~ctx_has_dalloca ctx ==>
        EVERY (\fn. fn_ptr_ok (\nm. set (ctx_ptr_param_list ctx nm)) fn /\
                    fn_ptr_ok (\nm. set (ctx_ptr_param_list ctx nm))
                      (reachable_fn fn))
          ctx.ctx_functions
Proof
  rpt strip_tac >>
  `EVERY (\fn. fn_ptr_ok_check (ctx_ptr_param_list ctx) fn /\
               wf_function fn /\
               EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
               fn_ptr_ok_check (ctx_ptr_param_list ctx)
                 (fn_reachable_blocks fn)) ctx.ctx_functions`
    by gvs[ptr_ok_check_def, ctx_has_dalloca_def] >>
  qpat_x_assum `ptr_ok_check _` kall_tac >>
  qpat_x_assum `~ctx_has_dalloca _` kall_tac >>
  rw[EVERY_MEM] >> fs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  `fn_reachable_blocks fn = reachable_fn fn` by
    simp[fn_reachable_blocks_reachable_fn, EVERY_MEM] >>
  gvs[] >> imp_res_tac fn_ptr_ok_check_sound >> simp[]
QED
