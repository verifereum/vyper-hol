Theory exprSimAbiEncodeObliviousContext
Ancestors
  exprSimAbiGasBridge fragExec list rich_list compileEnv emitHelper context

Definition entry_shape_def:
  entry_shape (a:compile_state) (s:compile_state) <=>
    (s.cs_blocks = a.cs_blocks /\
     s.cs_current_bb = a.cs_current_bb /\
     ?tail. s.cs_current_insts = a.cs_current_insts ++ tail) \/
    (?front tail.
       s.cs_blocks = front ++
         [<| bb_label := a.cs_current_bb;
             bb_instructions := a.cs_current_insts ++ tail |>] ++ a.cs_blocks)
End

Definition entry_action_def:
  entry_action (m:compile_state -> 'a # compile_state) <=>
    !a s x t L ids.
      entry_shape a s /\ m s = (x,t) /\
      LENGTH ids = LENGTH a.cs_current_insts ==>
      entry_shape a t /\
      m (start_swap a L ids s) = (x,start_swap a L ids t)
End

Theorem entry_shape_refl:
  !a. entry_shape a a
Proof
  rw[entry_shape_def] >> disj1_tac >> qexists_tac `[]` >> simp[]
QED

Theorem start_swap_initial:
  !a L ids. start_swap a L ids a = start_relabel L ids a
Proof
  simp[start_swap_def, start_relabel_def, emitted_blocks_def]
QED

Theorem entry_action_oblivious:
  !m. entry_action m ==> frag_start_oblivious m
Proof
  rw[entry_action_def, frag_start_oblivious_def]
  >> metis_tac[entry_shape_refl, start_swap_initial]
QED

Theorem start_swap_open:
  !a s tail L ids.
    s.cs_blocks = a.cs_blocks /\
    s.cs_current_insts = a.cs_current_insts ++ tail ==>
    start_swap a L ids s =
      s with <| cs_current_bb := L;
        cs_current_insts := MAP (\id. mk_inst id NOP [] []) ids ++ tail |>
Proof
  simp[start_swap_def, emitted_blocks_def, DROP_APPEND]
QED

Theorem start_swap_closed:
  !a s front tail L ids.
    s.cs_blocks = front ++
      [<| bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ tail |>] ++ a.cs_blocks ==>
    start_swap a L ids s = s with cs_blocks := front ++
      [<| bb_label := L;
          bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++ tail |>] ++
      a.cs_blocks
Proof
  rpt strip_tac
  >> simp[start_swap_def, emitted_blocks_def, TAKE_APPEND, DROP_APPEND,
          FRONT_APPEND, LAST_APPEND, TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG]
QED

Theorem entry_shape_emit:
  !a s i. entry_shape a s ==>
    entry_shape a (s with cs_current_insts := s.cs_current_insts ++ [i])
Proof
  rw[entry_shape_def]
  >- (disj1_tac >> simp[] >> qexists_tac `tail ++ [i]` >> simp[APPEND_ASSOC])
  >> disj2_tac >> metis_tac[]
QED

Theorem start_swap_emit:
  !a s i L ids. entry_shape a s ==>
    start_swap a L ids (s with cs_current_insts := s.cs_current_insts ++ [i]) =
    (start_swap a L ids s) with
      cs_current_insts := (start_swap a L ids s).cs_current_insts ++ [i]
Proof
  rw[entry_shape_def]
  >- ( `LENGTH a.cs_current_insts -
          (LENGTH tail + LENGTH a.cs_current_insts) = 0` by decide_tac
       >> simp[start_swap_def, emitted_blocks_def, DROP_APPEND, APPEND_ASSOC])
  >> simp[start_swap_def, emitted_blocks_def, TAKE_APPEND, DROP_APPEND,
          FRONT_APPEND, LAST_APPEND, TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG]
QED

Theorem entry_shape_new_block:
  !a s l. entry_shape a s ==>
    entry_shape a (SND (new_block l s))
Proof
  rw[entry_shape_def, new_block_def]
  >- (disj2_tac >> qexistsl_tac [`[]`, `tail`] >> simp[])
  >> disj2_tac
  >> qexistsl_tac [`<| bb_label := s.cs_current_bb;
                       bb_instructions := s.cs_current_insts |> :: front`, `tail`]
  >> simp[]
QED

Theorem start_swap_new_block:
  !a s l L ids. entry_shape a s ==>
    start_swap a L ids (SND (new_block l s)) =
    SND (new_block l (start_swap a L ids s))
Proof
  rw[entry_shape_def]
  >> simp[start_swap_def, emitted_blocks_def, new_block_def,
          TAKE_APPEND, DROP_APPEND, FRONT_APPEND, LAST_APPEND,
          TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, DROP_APPEND,
          TAKE_def, FRONT_DEF, LAST_DEF]
  >> `SUC (LENGTH front + (LENGTH a.cs_blocks + 1)) -
       (LENGTH front + (LENGTH a.cs_blocks + 2)) = 0` by decide_tac
  >> simp[FRONT_APPEND, LAST_APPEND, DROP_APPEND]
QED

Theorem entry_shape_counters:
  !a s nv nl ni. entry_shape a s ==>
    entry_shape a (s with <| cs_next_var := nv; cs_next_label := nl;
                            cs_next_id := ni |>)
Proof
  simp[entry_shape_def]
QED

Theorem start_swap_counters:
  !a s nv nl ni L ids.
    start_swap a L ids
      (s with <| cs_next_var := nv; cs_next_label := nl; cs_next_id := ni |>) =
    (start_swap a L ids s) with
      <| cs_next_var := nv; cs_next_label := nl; cs_next_id := ni |>
Proof
  rpt gen_tac >> simp[start_swap_def, emitted_blocks_def]
  >> IF_CASES_TAC >> simp[]
QED

Theorem entry_action_return:
  !x. entry_action (comp_return x)
Proof
  simp[entry_action_def, comp_return_def]
QED

Theorem entry_action_emit:
  !i. entry_action (emit i)
Proof
  rw[entry_action_def, emit_def]
  >- metis_tac[entry_shape_emit]
  >> simp[GSYM start_swap_emit]
QED

Theorem entry_action_new_block_unit:
  !l. entry_action (comp_ignore_bind (new_block l) (comp_return ()))
Proof
  rw[entry_action_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
     new_block_def]
  >- (drule entry_shape_new_block >> simp[new_block_def])
  >> drule start_swap_new_block >> simp[new_block_def]
QED

(* Exercise both the first closure and a later closure at the same origin. *)
Theorem start_swap_two_blocks:
  !a s l1 l2 L ids. entry_shape a s ==>
    start_swap a L ids (SND (new_block l2 (SND (new_block l1 s)))) =
    SND (new_block l2 (SND (new_block l1 (start_swap a L ids s))))
Proof
  rpt strip_tac
  >> simp[start_swap_new_block, entry_shape_new_block]
QED

Theorem entry_action_bind:
  !m k. entry_action m /\ (!v. entry_action (k v)) ==>
    entry_action (comp_bind m k)
Proof
  rw[entry_action_def, comp_bind_def]
  >> Cases_on `m s` >> gvs[]
  >> qpat_x_assum `!a s x t L ids. _` (drule_all_then (qspec_then `L` strip_assume_tac))
  >> qpat_x_assum `!v a s x t L ids. _` (drule_all_then (qspec_then `L` strip_assume_tac))
  >> simp[]
QED

Theorem entry_action_ignore_bind:
  !m k. entry_action m /\ entry_action k ==>
    entry_action (comp_ignore_bind m k)
Proof
  simp[comp_ignore_bind_def, entry_action_bind]
QED

Theorem entry_action_fresh_var:
  entry_action fresh_var
Proof
  rw[entry_action_def, fresh_var_def]
  >- gvs[entry_shape_def]
  >> simp[start_swap_def, emitted_blocks_def]
  >> IF_CASES_TAC >> simp[]
QED

Theorem entry_action_fresh_id:
  entry_action fresh_id
Proof
  rw[entry_action_def, fresh_id_def]
  >- gvs[entry_shape_def]
  >> simp[start_swap_def, emitted_blocks_def]
  >> IF_CASES_TAC >> simp[]
QED

Theorem entry_action_fresh_label:
  !suffix. entry_action (fresh_label suffix)
Proof
  rw[entry_action_def, fresh_label_def]
  >- gvs[entry_shape_def]
  >> simp[start_swap_def, emitted_blocks_def]
  >> IF_CASES_TAC >> simp[]
QED

Theorem entry_action_emit_inst:
  !opc ops outs. entry_action (emit_inst opc ops outs)
Proof
  rw[emit_inst_def]
  >> irule entry_action_bind
  >> simp[entry_action_fresh_id, entry_action_emit]
QED

Theorem entry_action_emit_void:
  !opc ops. entry_action (emit_void opc ops)
Proof
  rw[emit_void_def]
  >> irule entry_action_bind
  >> simp[entry_action_fresh_id, entry_action_emit]
QED

Theorem entry_action_emit_op:
  !opc ops. entry_action (emit_op opc ops)
Proof
  rw[emit_op_def]
  >> irule entry_action_bind >> simp[entry_action_fresh_id]
  >> gen_tac >> irule entry_action_bind >> simp[entry_action_fresh_var]
  >> gen_tac >> irule entry_action_ignore_bind
  >> simp[entry_action_emit, entry_action_return]
QED

Theorem entry_action_alloc_buffer:
  !size. entry_action (compile_alloc_buffer size)
Proof
  rw[compile_alloc_buffer_def]
  >> irule entry_action_bind
  >> simp[entry_action_emit_op, entry_action_return]
QED

Theorem entry_action_new_block:
  !l k. entry_action k ==>
    entry_action (comp_ignore_bind (new_block l) k)
Proof
  rpt strip_tac
  >> `comp_ignore_bind (new_block l) k =
      comp_ignore_bind (comp_ignore_bind (new_block l) (comp_return ())) k`
       by (simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
                FUN_EQ_THM, pairTheory.FORALL_PROD] >> gen_tac >>
           Cases_on `new_block l x` >> simp[])
  >> pop_assum SUBST1_TAC
  >> irule entry_action_ignore_bind
  >> simp[entry_action_new_block_unit]
QED
