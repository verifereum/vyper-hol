Theory exprSimAbiEncodeObliviousLabels
Ancestors
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousContext
  exprSimAbiEncodeLabelProvenance fragExec compileEnv list rich_list
  arithmetic emitHelperProps abiEncoder emitHelper context
  exprSimAbiEncodeObliviousSimulation

Definition opened_labels_def:
  opened_labels a b =
    if NULL (emitted_blocks a b) then []
    else MAP (\bb. bb.bb_label) (REVERSE (FRONT (emitted_blocks a b))) ++
         [b.cs_current_bb]
End

Theorem opened_labels_open:
  !a b. b.cs_blocks = a.cs_blocks ==> opened_labels a b = []
Proof
  simp[opened_labels_def, emitted_blocks_def]
QED

Theorem opened_labels_closed:
  !a b front tail.
    b.cs_blocks = front ++
      [<| bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ tail |>] ++ a.cs_blocks ==>
    opened_labels a b = MAP (\bb. bb.bb_label) (REVERSE front) ++
                        [b.cs_current_bb]
Proof
  simp[opened_labels_def, emitted_blocks_def, TAKE_APPEND,
       TAKE_LENGTH_TOO_LONG, FRONT_APPEND]
QED

Theorem opened_labels_compose:
  !a b c. entry_shape a b /\ entry_shape b c ==>
    opened_labels a c = opened_labels a b ++ opened_labels b c
Proof
  rw[entry_shape_def]
  >> simp[opened_labels_def, emitted_blocks_def, TAKE_APPEND,
          TAKE_LENGTH_TOO_LONG, FRONT_APPEND, REVERSE_APPEND,
          MAP_APPEND, APPEND_ASSOC]
  >> `LENGTH front' + 1 - (LENGTH front + (LENGTH front' + 1)) = 0`
       by decide_tac
  >> `LENGTH front' + 1 - (LENGTH front + (LENGTH front' + 2)) = 0`
       by decide_tac
  >> simp[FRONT_APPEND, REVERSE_APPEND, MAP_APPEND, APPEND_ASSOC]
QED

Definition label_step_def:
  label_step a b <=>
    entry_shape a b /\ a.cs_next_label <= b.cs_next_label /\
    ALL_DISTINCT (opened_labels a b) /\
    EVERY (enc_label_between a.cs_next_label b.cs_next_label)
          (opened_labels a b)
End

Definition label_action_def:
  label_action m <=> !a x b. m a = (x,b) ==> label_step a b
End

Theorem label_step_refl:
  !a. label_step a a
Proof
  simp[label_step_def, entry_shape_refl, opened_labels_open]
QED

Theorem label_step_trans:
  !a b c. label_step a b /\ label_step b c ==> label_step a c
Proof
  rw[label_step_def]
  >- metis_tac[entry_shape_trans]
  >- (drule_all opened_labels_compose >> disch_then SUBST1_TAC
      >> simp[ALL_DISTINCT_APPEND]
      >> gvs[EVERY_MEM, enc_label_between_def]
      >> rpt strip_tac >> res_tac >> gvs[]
      >> imp_res_tac fresh_label_output_inj >> gvs[])
  >> drule_all opened_labels_compose >> disch_then SUBST1_TAC
  >> simp[EVERY_APPEND, EVERY_MEM]
  >> gvs[EVERY_MEM]
  >> conj_tac >> rpt strip_tac
  >- (irule enc_label_between_mono
      >> qexistsl_tac [`b.cs_next_label`, `a.cs_next_label`] >> simp[])
  >> irule enc_label_between_mono
  >> qexistsl_tac [`c.cs_next_label`, `b.cs_next_label`] >> simp[]
QED

Theorem label_step_current_excluded:
  !a b. label_step a b ==>
    ~MEM b.cs_current_bb
       (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))
Proof
  rw[label_step_def]
  >> Cases_on `NULL (emitted_blocks a b)`
  >- gvs[NULL_EQ]
  >> gvs[opened_labels_def, ALL_DISTINCT_APPEND, MEM_MAP]
  >> metis_tac[MEM_REVERSE]
QED

Theorem label_action_return:
  !x. label_action (comp_return x)
Proof
  simp[label_action_def, comp_return_def, label_step_refl]
QED

Theorem label_action_bind:
  !m f. label_action m /\ (!x. label_action (f x)) ==>
    label_action (comp_bind m f)
Proof
  rw[label_action_def, comp_bind_def]
  >> Cases_on `m a` >> gvs[] >> metis_tac[label_step_trans]
QED

Theorem label_action_ignore_bind:
  !m n. label_action m /\ label_action n ==>
    label_action (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, label_action_bind]
QED

Theorem label_action_static_info:
  !dst src ei. label_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei`
  >> simp[label_action_def, compile_abi_encode_static_info_def,
          compile_abi_encode_static_def, emit_op_def, emit_void_def,
          emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def]
  >> rpt strip_tac >> gvs[]
  >> simp[label_step_def, opened_labels_open, entry_shape_def]
  >> metis_tac[APPEND_ASSOC]
QED

Theorem entry_action_run_shape:
  !m a x b. entry_action m /\ m a = (x,b) ==> entry_shape a b
Proof
  rw[entry_action_def]
  >> `entry_shape a a` by simp[entry_shape_refl]
  >> `LENGTH (MAP (\i. i.inst_id) a.cs_current_insts) =
      LENGTH a.cs_current_insts` by simp[]
  >> metis_tac[]
QED

Theorem label_action_static_loop:
  !dst src ei asz msz len.
    label_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rw[label_action_def]
  >> `entry_shape a b` by
       metis_tac[entry_action_run_shape, entry_action_static_loop]
  >> simp[label_step_def]
  >> qpat_x_assum `compile_abi_encode_dyn_static_loop _ _ _ _ _ _ _ = _` mp_tac
  >> simp[compile_abi_encode_dyn_static_loop_def,
    compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def]
  >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule (SRULE[enc_label_flat_def] enc_label_flat_static_info)
  >> strip_tac
  >> qpat_x_assum `compile_abi_encode_static_info _ _ _ _ = _` kall_tac
  >> gvs[]
  >> simp[opened_labels_def, emitted_blocks_def, enc_label_between_three,
          ADD1]
  >> rpt conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]
QED


Theorem enc_label_between_disjoint:
  !lo mid hi x y.
    enc_label_between lo mid x /\ enc_label_between mid hi y ==> x <> y
Proof
  rw[enc_label_between_def]
  >> strip_tac >> drule fresh_label_output_inj >> simp[]
QED

Theorem enc_label_between_not_mem:
  !lo mid hi l xs.
    enc_label_between lo mid l /\ EVERY (enc_label_between mid hi) xs ==>
    ~MEM l xs
Proof
  simp[EVERY_MEM] >> metis_tac[enc_label_between_disjoint]
QED

Theorem label_step_reserved_close:
  !a m b c l.
    label_step a m /\ label_step m b /\ entry_shape b c /\
    c.cs_next_label = b.cs_next_label /\ opened_labels b c = [l] /\
    enc_label_between a.cs_next_label m.cs_next_label l /\
    ~MEM l (opened_labels a m) ==>
    label_step a c
Proof
  rpt strip_tac
  >> `label_step a b` by metis_tac[label_step_trans]
  >> `~MEM l (opened_labels m b)` by
       (irule enc_label_between_not_mem
        >> qexistsl_tac [`b.cs_next_label`, `a.cs_next_label`, `m.cs_next_label`]
        >> gvs[label_step_def])
  >> `opened_labels a b = opened_labels a m ++ opened_labels m b` by
       (irule opened_labels_compose >> gvs[label_step_def])
  >> `opened_labels a c = opened_labels a b ++ [l]` by
       (gvs[label_step_def] >> drule_all opened_labels_compose >> simp[])
  >> gvs[label_step_def]
  >> simp[ALL_DISTINCT_APPEND, EVERY_APPEND]
  >> conj_tac >- metis_tac[entry_shape_trans]
  >> irule enc_label_between_mono
  >> qexistsl_tac [`m.cs_next_label`, `a.cs_next_label`] >> simp[]
QED

Theorem label_action_dyn_loop_step:
  !ei. (!dst src. label_action (compile_abi_encode_to_buf dst src ei)) ==>
    !dst src asz msz len.
      label_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rpt strip_tac >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp[label_action_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def]
  >> rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> qpat_x_assum `!dst src. _` (mp_tac o SRULE[label_action_def])
  >> disch_then drule >> strip_tac
  >> qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac
  >> qmatch_asmsub_abbrev_tac `label_step sm sc`
  >> `label_step a sm` by
       (simp[Abbr `sm`, label_step_def, opened_labels_def, emitted_blocks_def,
             enc_label_between_three, ADD1]
        >> conj_tac
        >- (qpat_x_assum `label_step _ sc` kall_tac
            >> rewrite_tac[entry_shape_def] >> disj2_tac
            >> simp_tac pure_ss [compile_state_accfupds]
            >> qmatch_goalsub_abbrev_tac `hdr :: entry :: a.cs_blocks`
            >> qexists_tac `[hdr]` >> simp[Abbr `entry`, APPEND_ASSOC])
        >> strip_tac >> drule fresh_label_output_inj >> simp[])
  >> irule label_step_reserved_close
  >> qexistsl_tac [`sc`, `fresh_label_output "enc_dyn_exit" (a.cs_next_label + 2)`, `sm`]
  >> simp[]
  >> reverse conj_tac
  >- (simp[Abbr `sm`, opened_labels_def, emitted_blocks_def, ADD1,
           enc_label_between_three]
      >> rewrite_tac[entry_shape_def] >> disj2_tac >> qexists_tac `[]`
      >> simp[APPEND_ASSOC])
  >> simp[Abbr `sm`, opened_labels_def, emitted_blocks_def, ADD1]
  >> rpt conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]
QED
