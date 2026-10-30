(* Operand counts preserved by restoration and incremented by duplication.
   TOP-LEVEL: emit_one_input_inventory_mono, emit_one_input_inventory_inc. *)
Theory operandInventory
Ancestors
  doDupModel doSwapSim planWf stackPlanGen stackPlanOps stackPlanTypes stackModel
  list rich_list finite_map arithmetic
Libs pairLib

(* Shared count interface for input preparation and reorder budgets. *)
Theorem elem_count_snoc:
  !x y (xs : 'a list).
    LIST_ELEM_COUNT x (SNOC y xs) =
    LIST_ELEM_COUNT x xs + LIST_ELEM_COUNT x [y]
Proof
  gen_tac >> gen_tac >> Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
QED

Theorem do_dup_spilled_unchanged:
  !(ps : plan_state) dist.
    (SND (do_dup dist ps)).ps_spilled = ps.ps_spilled
Proof
  metis_tac[do_dup_spilled]
QED

Theorem do_dup_inventory_count:
  !(ps : plan_state) dist x.
    dist < LENGTH ps.ps_stack ==>
    LIST_ELEM_COUNT x (SND (do_dup dist ps)).ps_stack +
      (if x IN FDOM (SND (do_dup dist ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) +
      (if x = stack_peek dist ps.ps_stack then 1 else 0)
Proof
  rpt strip_tac >> drule_then assume_tac do_dup_stack_exact >>
  simp[do_dup_spilled_unchanged, LIST_ELEM_COUNT_THM] >>
  Cases_on `x = stack_peek dist ps.ps_stack` >>
  simp[LIST_ELEM_COUNT_DEF]
QED

Theorem do_restore_inventory_count:
  !(ps : plan_state) op off x.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    LIST_ELEM_COUNT x (SND (do_restore op ps)).ps_stack +
      (if x IN FDOM (SND (do_restore op ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  simp[do_restore_def, stack_push_def, elem_count_snoc,
       LIST_ELEM_COUNT_THM] >>
  Cases_on `x = op` >> gvs[flookup_thm, LIST_ELEM_COUNT_DEF]
QED

Theorem stack_get_depth_push_inventory:
  !op stk. stack_get_depth op (stack_push op stk) = SOME 0
Proof
  rw[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]
QED

Theorem stack_get_depth_restore_inventory:
  !(ps : plan_state) op off.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    stack_get_depth op (SND (do_restore op ps)).ps_stack = SOME 0
Proof
  simp[do_restore_def, stack_get_depth_push_inventory]
QED

Theorem emit_one_input_inventory_mono:
  !opc nl op (ps : plan_state) x.
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x (SND (emit_one_input opc nl op ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
       then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op`
  >- simp[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
           elem_count_snoc, LIST_ELEM_COUNT_THM]
  >- (rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (simp[emit_one_input_def, is_var_operand_def, LET_THM] >>
          Cases_on `MEM v nl` >> simp[]
          >- (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
              rename1 `stack_get_depth _ _ = SOME dist` >>
              `dist < LENGTH ps.ps_stack /\
               stack_peek dist ps.ps_stack = Var v` by
                metis_tac[stack_get_depth_props] >>
              qspecl_then [`ps`, `dist`, `x`] (drule_then assume_tac)
                do_dup_inventory_count >>
              qpat_assum
                `!y. LIST_ELEM_COUNT y (SND (do_dup dist ps)).ps_stack + _ = _`
                (qspec_then `x` assume_tac) >>
              CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
              fs[] >> decide_tac)
          >> simp[])
      >> rename1 `FLOOKUP ps.ps_spilled (Var v) = SOME off` >>
         Cases_on `do_restore (Var v) ps` >>
         rename1 `do_restore (Var v) ps = (restore_ops, psr)` >>
         qspecl_then [`ps`, `Var v`, `off`] mp_tac
           stack_get_depth_restore_inventory >> simp[] >> strip_tac >>
         `0 < LENGTH psr.ps_stack /\ stack_peek 0 psr.ps_stack = Var v` by
           metis_tac[stack_get_depth_props] >>
         qspecl_then [`ps`, `Var v`, `off`, `x`] mp_tac
           do_restore_inventory_count >> simp[] >> strip_tac >>
         Cases_on `MEM v nl`
         >- (qspecl_then [`psr`, `0`, `x`] (drule_then assume_tac)
               do_dup_inventory_count >>
             qpat_assum
               `!y. LIST_ELEM_COUNT y (SND (do_dup 0 psr)).ps_stack + _ = _`
               (qspec_then `x` assume_tac) >>
             Cases_on `do_dup 0 psr` >>
             gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
             decide_tac)
         >> simp[emit_one_input_def, is_var_operand_def, LET_THM])
  >> Cases_on `opc = INVOKE` >>
     gvs[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
         elem_count_snoc, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem stack_peek_eq_EL_REVERSE_inventory:
  !stk d. d < LENGTH stk ==>
    stack_peek d stk = EL d (REVERSE stk)
Proof
  rpt strip_tac >> simp[stack_peek_def, EL_REVERSE] >>
  `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >> simp[]
QED

Theorem stack_get_depth_exists_inventory:
  !op stk. MEM op stk ==> ?d. stack_get_depth op stk = SOME d
Proof
  rpt strip_tac >> Cases_on `stack_get_depth op stk` >> simp[] >>
  fs[stack_get_depth_NONE, MEM_EL] >>
  `LENGTH stk - 1 - n < LENGTH stk` by decide_tac >>
  `stack_peek (LENGTH stk - 1 - n) stk = op` by
    (`LENGTH stk - 1 - (LENGTH stk - 1 - n) = n` by decide_tac >>
     SIMP_TAC std_ss [stack_peek_def] >>
     qpat_assum `LENGTH stk - 1 - (LENGTH stk - 1 - n) = n`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `op = EL n stk` (ACCEPT_TAC o SYM)) >>
  metis_tac[]
QED

Theorem elem_count_mem_pos_inventory:
  !op stk. MEM op stk ==> 1 <= LIST_ELEM_COUNT op stk
Proof
  rpt strip_tac >> drule (iffRL LIST_ELEM_COUNT_MEM) >> decide_tac
QED

Theorem covered_operand_inventory:
  !op (ps : plan_state).
    (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
    1 <= LIST_ELEM_COUNT op ps.ps_stack +
         (if op IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac
  >- (drule elem_count_mem_pos_inventory >> decide_tac)
  >> simp[]
QED
Theorem emit_one_input_inventory_inc:
  !opc nl op (ps : plan_state).
    (~is_var_operand op \/
     ?v. op = Var v /\ MEM v nl /\
         (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled)) ==>
    LIST_ELEM_COUNT op ps.ps_stack +
      (if op IN FDOM ps.ps_spilled then 1 else 0) + 1 <=
    LIST_ELEM_COUNT op (SND (emit_one_input opc nl op ps)).ps_stack +
      (if op IN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
       then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op`
  >- simp[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
           elem_count_snoc, LIST_ELEM_COUNT_THM]
  >- (rename1 `Var v` >> simp[is_var_operand_def] >> disch_then assume_tac >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (`MEM (Var v) ps.ps_stack` by
            metis_tac[flookup_thm] >>
          drule stack_get_depth_exists_inventory >> strip_tac >>
          rename1 `stack_get_depth (Var v) ps.ps_stack = SOME dist` >>
          `dist < LENGTH ps.ps_stack /\
           stack_peek dist ps.ps_stack = Var v` by
            metis_tac[stack_get_depth_props] >>
          qspecl_then [`ps`, `dist`, `Var v`] (drule_then assume_tac)
            do_dup_inventory_count >>
          qpat_assum
            `!z. LIST_ELEM_COUNT (Var z) (SND (do_dup dist ps)).ps_stack + _ = _`
            (qspec_then `v` assume_tac) >>
          Cases_on `do_dup dist ps` >>
          gvs[emit_one_input_def, is_var_operand_def, LET_THM] >> decide_tac)
      >> rename1 `FLOOKUP ps.ps_spilled (Var v) = SOME off` >>
         Cases_on `do_restore (Var v) ps` >>
         rename1 `do_restore (Var v) ps = (restore_ops, psr)` >>
         qspecl_then [`ps`, `Var v`, `off`] mp_tac
           stack_get_depth_restore_inventory >> simp[] >> strip_tac >>
         `0 < LENGTH psr.ps_stack /\ stack_peek 0 psr.ps_stack = Var v` by
           metis_tac[stack_get_depth_props] >>
         qspecl_then [`ps`, `Var v`, `off`, `Var v`] mp_tac
           do_restore_inventory_count >> simp[] >> strip_tac >>
         qspecl_then [`psr`, `0`, `Var v`] (drule_then assume_tac)
           do_dup_inventory_count >>
         qpat_assum
           `!z. LIST_ELEM_COUNT (Var z) (SND (do_dup 0 psr)).ps_stack + _ = _`
           (qspec_then `v` assume_tac) >>
         Cases_on `do_dup 0 psr` >>
         gvs[emit_one_input_def, is_var_operand_def, LET_THM] >> decide_tac)
  >> Cases_on `opc = INVOKE` >>
     gvs[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
         elem_count_snoc, LIST_ELEM_COUNT_THM] >> decide_tac
QED
Theorem emit_one_input_var_not_spilled:
  !opc nl op ps.
    is_var_operand op ==>
    op NOTIN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[is_var_operand_def, emit_one_input_def, LET_THM]
  >> rename1 `Var v` >>
     Cases_on `FLOOKUP ps.ps_spilled (Var v)` >> simp[]
  >- (Cases_on `MEM v nl` >> simp[] >>
      Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
      CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
      gvs[do_dup_spilled_unchanged, flookup_thm])
  >> simp[do_restore_def, flookup_thm] >>
     Cases_on `MEM v nl` >> simp[] >>
     Cases_on `stack_get_depth (Var v)
       (stack_push (Var v) ps.ps_stack)` >>
     CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
     simp[do_dup_spilled_unchanged]
QED

Theorem emit_one_input_preserves_not_spilled:
  !opc nl op ps x.
    x NOTIN FDOM ps.ps_spilled ==>
    x NOTIN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[is_var_operand_def, emit_one_input_def, LET_THM]
  >- (rename1 `FLOOKUP ps.ps_spilled (Var v)` >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)` >> simp[]
      >- (Cases_on `MEM v nl` >> simp[] >>
          Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
          CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
          simp[do_dup_spilled_unchanged])
      >> simp[do_restore_def] >>
         Cases_on `MEM v nl` >> simp[] >>
         Cases_on `stack_get_depth (Var v)
           (stack_push (Var v) ps.ps_stack)` >>
         CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
         simp[do_dup_spilled_unchanged])
  >> Cases_on `opc = INVOKE` >> simp[]
QED

Theorem emit_one_input_nonvar_spilled_unchanged:
  !opc nl op ps.
    ~is_var_operand op ==>
    (SND (emit_one_input opc nl op ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[is_var_operand_def, emit_one_input_def, LET_THM] >>
  Cases_on `opc = INVOKE` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed operand-count proof: " ^ name)
  end) (DB.thms "operandInventory")
