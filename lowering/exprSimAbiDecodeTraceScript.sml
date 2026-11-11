Theory exprSimAbiDecodeTrace
Ancestors
  exprSimAbiGasBridge fragExec compileEnv venomInst list rich_list

(* Proof-only histories: none of these operations is used by the compiler. *)
Datatype:
  decode_event = DecodeEmit instruction | DecodeSwitch string
End

Definition decode_step_def:
  (decode_step (DecodeEmit i) s =
    s with cs_current_insts := s.cs_current_insts ++ [i]) /\
  (decode_step (DecodeSwitch l) s =
    s with <| cs_blocks :=
      <| bb_label := s.cs_current_bb;
         bb_instructions := s.cs_current_insts |> :: s.cs_blocks;
      cs_current_bb := l; cs_current_insts := [] |> )
End

Definition decode_replay_def:
  (decode_replay [] s = s) /\
  (decode_replay (e::es) s = decode_replay es (decode_step e s))
End

Definition decode_core_def:
  decode_core s = s with <| cs_blocks := []; cs_current_bb := "";
                            cs_current_insts := [] |>
End

Definition decode_history_def:
  decode_history n h = n with <| cs_blocks := h.cs_blocks;
    cs_current_bb := h.cs_current_bb; cs_current_insts := h.cs_current_insts |>
End

Definition decode_certificate_def:
  decode_certificate (m : 'a compiler) <=>
    !s. ?x es n. !h. decode_core h = decode_core s ==>
      m h = (x, decode_history n (decode_replay es h))
End

Theorem decode_replay_append:
  !es fs s. decode_replay (es ++ fs) s =
    decode_replay fs (decode_replay es s)
Proof
  Induct >> simp[decode_replay_def]
QED

Theorem decode_replay_core:
  !es s. decode_core (decode_replay es s) = decode_core s
Proof
  Induct >> simp[decode_replay_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[decode_step_def, decode_core_def]
QED

Theorem decode_history_core:
  decode_core (decode_history n h) = decode_core n
Proof
  simp[decode_core_def, decode_history_def]
QED

Theorem decode_history_id:
  decode_history s s = s
Proof
  Cases_on `s` >> simp[decode_history_def, compile_state_component_equality]
QED

Theorem decode_step_history:
  !e n h. decode_step e (decode_history n h) =
    decode_history n (decode_step e h)
Proof
  Cases >> simp[decode_step_def, decode_history_def]
QED

Theorem decode_replay_history:
  !es n h. decode_replay es (decode_history n h) =
    decode_history n (decode_replay es h)
Proof
  Induct >> simp[decode_replay_def, decode_step_history]
QED

Theorem decode_step_extends:
  !e s. cs_extends s (decode_step e s)
Proof
  Cases >> rw[decode_step_def, cs_extends_def]
QED

Theorem decode_replay_extends:
  !es s. cs_extends s (decode_replay es s)
Proof
  Induct >> simp[decode_replay_def, cs_extends_refl] >>
  metis_tac[cs_extends_trans, decode_step_extends]
QED

Theorem decode_step_swap:
  !e sa sb L ids. cs_extends sa sb ==>
    decode_step e (start_swap sa L ids sb) =
    start_swap sa L ids (decode_step e sb)
Proof
  Cases >> rpt gen_tac >>
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new` >>
  gvs[start_swap_def, decode_step_def, emitted_blocks_def,
      FRONT_DEF, LAST_DEF, DROP_APPEND, TAKE_LENGTH_APPEND,
      compile_state_component_equality, basic_block_component_equality,
      arithmeticTheory.ADD1, IS_PREFIX_APPEND] >>
  `LENGTH sa.cs_current_insts -
    (LENGTH l + LENGTH sa.cs_current_insts) = 0` by decide_tac >> simp[]
QED

Theorem decode_replay_swap:
  !es sa sb L ids. cs_extends sa sb ==>
    decode_replay es (start_swap sa L ids sb) =
    start_swap sa L ids (decode_replay es sb)
Proof
  Induct >> simp[decode_replay_def] >> rpt strip_tac >>
  simp[decode_step_swap] >> first_x_assum irule >>
  metis_tac[cs_extends_trans, decode_step_extends]
QED

Theorem decode_swap_refl:
  start_swap s L ids s = start_relabel L ids s
Proof
  simp[start_swap_def, start_relabel_def, emitted_blocks_def]
QED

Theorem decode_replay_relabel:
  decode_replay es (start_relabel L ids s) =
    start_swap s L ids (decode_replay es s)
Proof
  rewrite_tac[GSYM decode_swap_refl] >>
  irule decode_replay_swap >> simp[cs_extends_refl]
QED

Theorem decode_swap_history:
  start_swap s L ids (decode_history n h) =
    decode_history n (start_swap s L ids h)
Proof
  simp[start_swap_def, emitted_blocks_def, decode_history_def] >>
  Cases_on `NULL (TAKE (LENGTH h.cs_blocks - LENGTH s.cs_blocks) h.cs_blocks)` >>
  simp[decode_history_def]
QED

Theorem decode_history_extends:
  cs_extends s (decode_history n h) <=> cs_extends s h
Proof
  simp[cs_extends_def, decode_history_def]
QED

Theorem decode_certificate_appends:
  decode_certificate m ==> cs_appends m
Proof
  rw[decode_certificate_def, cs_appends_def] >>
  first_x_assum (qspec_then `st` strip_assume_tac) >>
  first_x_assum (qspec_then `st` mp_tac) >>
  simp[] >> strip_tac >> gvs[decode_history_extends, decode_replay_extends]
QED

Theorem decode_certificate_oblivious:
  decode_certificate m ==> frag_start_oblivious m
Proof
  rw[decode_certificate_def, frag_start_oblivious_def] >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >>
  `decode_core (start_relabel L ids sa) = decode_core sa` by
    simp[decode_core_def, start_relabel_def] >>
  first_assum (qspec_then `sa` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `start_relabel L ids sa` mp_tac) >>
  simp[decode_replay_relabel, decode_swap_history] >> gvs[]
QED

(* These probes retain arbitrary old blocks and arbitrary prefix lengths. *)
Theorem decode_replay_zero_switch_probe:
  decode_replay [DecodeEmit i] s =
    s with cs_current_insts := s.cs_current_insts ++ [i]
Proof
  simp[decode_replay_def, decode_step_def]
QED

Theorem decode_replay_one_switch_probe:
  decode_replay [DecodeEmit i; DecodeSwitch l; DecodeEmit j] s =
    s with <|cs_blocks :=
      <|bb_label := s.cs_current_bb;
        bb_instructions := s.cs_current_insts ++ [i]|> :: s.cs_blocks;
      cs_current_bb := l; cs_current_insts := [j]|>
Proof
  simp[decode_replay_def, decode_step_def]
QED

Theorem decode_replay_two_switch_probe:
  decode_replay
    [DecodeEmit i; DecodeSwitch l; DecodeEmit j; DecodeSwitch k] s =
    s with <|cs_blocks :=
      <|bb_label := l; bb_instructions := [j]|> ::
      <|bb_label := s.cs_current_bb;
        bb_instructions := s.cs_current_insts ++ [i]|> :: s.cs_blocks;
      cs_current_bb := k; cs_current_insts := []|>
Proof
  simp[decode_replay_def, decode_step_def]
QED
