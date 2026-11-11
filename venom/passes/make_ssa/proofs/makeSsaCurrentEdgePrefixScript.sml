Theory makeSsaCurrentEdgePrefix
Ancestors
  makeSsaCurrentEndpointBatch makeSsaCurrentConditionalReadiness
  makeSsaCurrentCopyPrefixRuntime makeSsaCurrentLockstepShape
  makeSsaCurrentForwardReadiness cfgNormSupplySim
  venomExecProofs venomExecSemantics venomState stateFrame list rich_list pred_set option
  venomWfProps

Theorem current_completed_edge_cleaned_prefix_total:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  final = fn with fn_blocks := simplify_current_phis_if T renamed /\
  wf_function final /\ wf_ssa final /\ MEM pred final.fn_blocks /\
  pred.bb_label = before.vs_current_bb /\ EVERY inst_wf pred.bb_instructions /\
  EVERY inst_wf bb.bb_instructions /\ strict_dom_vars_defined final before /\
  fn_reachable final before.vs_current_bb /\
  before.vs_inst_idx <= LENGTH pred.bb_instructions /\
  (!j x. j < before.vs_inst_idx /\ j < LENGTH pred.bb_instructions /\
    MEM x (EL j pred.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x before)) /\
  exec_block fuel C pred before = OK edge /\
  lookup_block edge.vs_current_bb final.fn_blocks = SOME bb /\
  copies = TAKE (phi_prefix_length new.bb_instructions - phi_prefix_length bb.bb_instructions)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) ==>
  ?post done. eval_phis edge bb.bb_instructions = OK post /\
    current_prefix_steps fuel C copies
      (post with vs_inst_idx := phi_prefix_length bb.bb_instructions) done /\
    done.vs_inst_idx = phi_prefix_length new.bb_instructions /\
    done.vs_current_bb = h /\ done.vs_prev_bb = post.vs_prev_bb /\
    execution_frame done = execution_frame post /\
    strict_dom_vars_defined final done /\
    done.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
      MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done))
Proof
  strip_tac >>
  `?post. eval_phis edge bb.bb_instructions = OK post` by
    (irule current_completed_edge_phi_batch_total >> metis_tac[]) >>
  `strict_dom_vars_defined final edge` by
    (irule strict_dom_vars_defined_preserved_from_prefix >>
     conj_tac >- simp[] >>
     qexistsl [`pred`, `C`, `fuel`, `before`] >> simp[] >>
     fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     metis_tac[option_nchotomy, IS_SOME_DEF]) >>
  `strict_dom_vars_defined final post` by
    metis_tac[strict_dom_vars_defined_eval_phis] >>
  `bb.bb_label = h` by
    (`new.bb_label = h` by metis_tac[lookup_block_label] >>
     Cases_on `new.bb_instructions` >>
     simp[makeSsaDefsTheory.simplify_current_phi_block_def] >>
     IF_CASES_TAC >> simp[]) >>
  `post.vs_current_bb = h` by
    metis_tac[eval_phis_preserves_current_bb, lookup_block_label] >>
  drule_all current_cleaned_copy_prefix_ready >> strip_tac >>
  `?done. current_prefix_steps fuel C copies
      (post with vs_inst_idx := phi_prefix_length bb.bb_instructions) done /\
    execution_frame done = execution_frame post /\
    done.vs_current_bb = post.vs_current_bb /\
    done.vs_prev_bb = post.vs_prev_bb /\
    (!x. x IN {x | IS_SOME (lookup_var x post)} UNION
      set (FLAT (MAP (\inst. inst.inst_outputs) copies)) ==>
      IS_SOME (lookup_var x done))` by
    (mp_tac (Q.SPECL [`copies`, `{x | IS_SOME (lookup_var x post)}`,
      `post with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
      current_copy_prefix_total) >> simp[lookup_var_def]) >>
  `LENGTH bb.bb_instructions = LENGTH new.bb_instructions /\
   phi_prefix_length bb.bb_instructions <= phi_prefix_length new.bb_instructions` by
    metis_tac[simplify_current_phi_block_layout] >>
  `phi_prefix_length new.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[phi_prefix_length_le] >>
  `done.vs_inst_idx = phi_prefix_length new.bb_instructions` by
    (drule current_prefix_steps_index >>
     simp[LENGTH_TAKE_EQ, LENGTH_DROP, arithmeticTheory.MIN_DEF] >>
     rw[] >> decide_tac) >>
  `!x. IS_SOME (lookup_var x post) ==> IS_SOME (lookup_var x done)` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `strict_dom_vars_defined final done` by
    (qpat_x_assum `strict_dom_vars_defined final post` mp_tac >>
     simp[venomWfPropsTheory.strict_dom_vars_defined_def] >>
     rpt strip_tac >>
     `v IN FDOM post.vs_vars` by metis_tac[] >>
     `IS_SOME (lookup_var v post)` by
       simp[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     `IS_SOME (lookup_var v done)` by metis_tac[] >>
     fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     Cases_on `v IN FDOM done.vs_vars` >> fs[]) >>
  qexistsl [`post`, `done`] >>
  asm_rewrite_tac [phi_prefix_length_le] >>
  rpt strip_tac >>
  Cases_on `j < phi_prefix_length bb.bb_instructions`
  >- (first_x_assum irule >> irule current_phi_batch_output_defined >>
      qexistsl [`EL j bb.bb_instructions`, `edge`, `bb.bb_instructions`] >>
      conj_tac >- simp[] >> conj_tac
      >- (rewrite_tac[MEM_EL] >> qexists `j` >> simp[EL_TAKE, LENGTH_TAKE_EQ, phi_prefix_length_le] >> metis_tac[EL_TAKE, phi_prefix_length_le]) >>
      simp[]) >>
  `MEM (EL j bb.bb_instructions) copies` by
    (pure_once_rewrite_tac[MEM_EL] >>
     qexists `j - phi_prefix_length bb.bb_instructions` >>
     qpat_assum `copies = _` SUBST1_TAC >>
     pure_rewrite_tac[LENGTH_TAKE_EQ, LENGTH_DROP] >>
     `j - phi_prefix_length bb.bb_instructions <
        phi_prefix_length new.bb_instructions - phi_prefix_length bb.bb_instructions /\
      j - phi_prefix_length bb.bb_instructions <
        LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions` by decide_tac >>
     `j - phi_prefix_length bb.bb_instructions +
       phi_prefix_length bb.bb_instructions = j` by decide_tac >>
     `j - phi_prefix_length bb.bb_instructions < LENGTH (DROP
       (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (pure_rewrite_tac[LENGTH_DROP] >> decide_tac) >>
     conj_tac >- (pure_rewrite_tac[arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac) >>
     qpat_x_assum `bb = simplify_current_phi_block new` kall_tac >>
     simp[EL_TAKE, EL_DROP]) >>
  qpat_x_assum `!x. x IN _ UNION _ ==> _` irule >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_completed_edge_plain_prefix_total:
  wf_function f /\ wf_ssa f /\ MEM pred f.fn_blocks /\
  pred.bb_label = before.vs_current_bb /\ EVERY inst_wf pred.bb_instructions /\
  strict_dom_vars_defined f before /\ fn_reachable f before.vs_current_bb /\
  before.vs_inst_idx <= LENGTH pred.bb_instructions /\
  (!j x. j < before.vs_inst_idx /\ j < LENGTH pred.bb_instructions /\
     MEM x (EL j pred.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x before)) /\
  exec_block fuel C pred before = OK edge /\
  lookup_block edge.vs_current_bb f.fn_blocks = SOME bb /\
  EVERY inst_wf bb.bb_instructions ==>
  ?post. eval_phis edge bb.bb_instructions = OK post /\
    strict_dom_vars_defined f (post with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions /\
    (!j x. j < phi_prefix_length bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
      MEM x (EL j bb.bb_instructions).inst_outputs ==>
      IS_SOME (lookup_var x (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)))
Proof
  strip_tac >>
  `?post. eval_phis edge bb.bb_instructions = OK post` by
    (irule current_completed_edge_phi_batch_total >> metis_tac[]) >>
  `strict_dom_vars_defined f edge` by
    (irule strict_dom_vars_defined_preserved_from_prefix >>
     conj_tac >- simp[] >>
     qexistsl [`pred`, `C`, `fuel`, `before`] >> simp[] >>
     fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     metis_tac[option_nchotomy, IS_SOME_DEF]) >>
  `strict_dom_vars_defined f post` by
    metis_tac[strict_dom_vars_defined_eval_phis] >>
  qexists `post` >> simp[strict_dom_vars_defined_inst_idx, phi_prefix_length_le, lookup_var_def] >>
  rpt strip_tac >>
  `IS_SOME (lookup_var x post)` suffices_by simp[lookup_var_def] >>
  irule current_phi_batch_output_defined >>
  qexistsl [`EL j bb.bb_instructions`, `edge`, `bb.bb_instructions`] >>
  conj_tac >- simp[] >> conj_tac
  >- (rewrite_tac[MEM_EL] >> qexists `j` >>
      simp[EL_TAKE, LENGTH_TAKE_EQ, phi_prefix_length_le]) >> simp[]
QED
