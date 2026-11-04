Theory makeSsaCurrentOrdinary
Ancestors
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomExecSemantics venomState
  stateFrame venomInst list rich_list

Theorem current_rename_operands_map:
  !ops. rename_current_operands rs ops =
    MAP (\op. case op of Var v => Var (latest_current_name rs v) | _ => op) ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def]
QED

Theorem current_eval_operand_agree:
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars [op]) st st' ==>
  eval_operand (HD (rename_current_operands rs [op])) st' = eval_operand op st
Proof
  Cases_on `op` >>
  simp[rename_current_operands_def, operand_vars_def, operand_var_def,
       current_name_agree_def, eval_operand_def] >> rpt strip_tac >>
  qpat_x_assum `execution_frame _ = _`
    (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >>
  simp[execution_frame_def]
QED

Theorem current_eval_operand_occurrence:
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars ops) st st' /\ MEM op ops ==>
  eval_operand (HD (rename_current_operands rs [op])) st' = eval_operand op st
Proof
  strip_tac >> irule current_eval_operand_agree >> simp[] >>
  irule current_name_agree_mono >> goal_assum $ drule_at Any >>
  `?xs ys. ops = xs ++ op::ys` by metis_tac[MEM_SPLIT] >>
  gvs[] >> simp[operand_vars_def] >>
  Cases_on `operand_var op` >> simp[]
QED

Theorem current_rename_operands_length[simp]:
  LENGTH (rename_current_operands rs ops) = LENGTH ops
Proof
  simp[current_rename_operands_map]
QED

Theorem current_rename_operands_take:
  rename_current_operands rs (TAKE n ops) = TAKE n (rename_current_operands rs ops)
Proof
  simp[current_rename_operands_map, MAP_TAKE]
QED

Theorem current_rename_operands_drop:
  rename_current_operands rs (DROP n ops) = DROP n (rename_current_operands rs ops)
Proof
  simp[current_rename_operands_map, MAP_DROP]
QED

Theorem current_rename_operands_reverse:
  rename_current_operands rs (REVERSE ops) = REVERSE (rename_current_operands rs ops)
Proof
  simp[current_rename_operands_map, MAP_REVERSE]
QED

Theorem current_rename_operands_el:
  n < LENGTH ops ==>
  EL n (rename_current_operands rs ops) =
    HD (rename_current_operands rs [EL n ops])
Proof
  simp[current_rename_operands_map, EL_MAP]
QED

Theorem current_rename_operands_pointwise:
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars ops) st st' ==>
  LIST_REL (\op op'. eval_operand op st = eval_operand op' st')
    ops (rename_current_operands rs ops)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  simp[current_rename_operands_el] >>
  metis_tac[current_eval_operand_occurrence, EL_MEM]
QED

Theorem current_rename_operands_extract_labels:
  !ops. extract_labels (rename_current_operands rs ops) = extract_labels ops
Proof
  Induct >> simp[rename_current_operands_def, extract_labels_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, extract_labels_def]
QED

Theorem current_rename_operand_literal[simp]:
  rename_current_operands rs [Lit w] = [Lit w]
Proof
  simp[rename_current_operands_def]
QED

Theorem current_rename_operand_label[simp]:
  rename_current_operands rs [Label l] = [Label l]
Proof
  simp[rename_current_operands_def]
QED

Definition current_write_compatible_def:
  current_write_compatible rs rt x y demand <=>
    latest_current_name rt x = y /\
    (!v. MEM v demand /\ v <> x ==>
      latest_current_name rt v = latest_current_name rs v /\
      latest_current_name rt v <> y)
End

Definition current_before_outputs_def:
  current_before_outputs outs demand = FILTER (\v. ~MEM v outs) demand
End

Definition current_outputs_compatible_def:
  (current_outputs_compatible rs [] rt ys demand <=> rs = rt /\ ys = []) /\
  (current_outputs_compatible rs (x::xs) rt ys demand <=>
    ?y zs mid. ys = y::zs /\
      current_write_compatible rs mid x y (current_before_outputs xs demand) /\
      current_outputs_compatible mid xs rt zs demand)
End

Theorem current_write_agree:
  current_write_compatible rs rt x y demand /\
  current_name_agree rs (FILTER (\v. v <> x) demand) st st' ==>
  current_name_agree rt demand (update_var x w st) (update_var y w st')
Proof
  simp[current_write_compatible_def, current_name_agree_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = x` >> gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem current_before_outputs_cons:
  current_before_outputs (x::xs) demand =
    FILTER (\v. v <> x) (current_before_outputs xs demand)
Proof
  simp[current_before_outputs_def, FILTER_FILTER] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem current_outputs_compatible_length:
  !xs rs rt ys demand. current_outputs_compatible rs xs rt ys demand ==>
    LENGTH xs = LENGTH ys
Proof
  Induct >> simp[current_outputs_compatible_def] >> rpt strip_tac >>
  res_tac >> simp[]
QED

Theorem current_outputs_fold_agree:
  !xs rs rt ys vals st st' demand.
    current_outputs_compatible rs xs rt ys demand /\
    LENGTH xs = LENGTH vals /\
    current_name_agree rs (current_before_outputs xs demand) st st' ==>
    current_name_agree rt demand
      (FOLDL (\s (x,w). update_var x w s) st (ZIP (xs,vals)))
      (FOLDL (\s (x,w). update_var x w s) st' (ZIP (ys,vals)))
Proof
  Induct >> simp[current_outputs_compatible_def, current_before_outputs_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `vals` >> gvs[] >>
  first_x_assum irule >> simp[] >> qexists_tac `mid` >> simp[] >>
  irule current_write_agree >> qexists_tac `rs` >>
  gvs[current_before_outputs_def, FILTER_FILTER]
QED

Theorem current_bind_outputs_agree:
  current_outputs_compatible rs outs rt outs' demand /\
  current_name_agree rs (current_before_outputs outs demand) st st' ==>
  (bind_outputs outs vals st = NONE <=> bind_outputs outs' vals st' = NONE) /\
  (!t t'. bind_outputs outs vals st = SOME t /\
          bind_outputs outs' vals st' = SOME t' ==>
          current_name_agree rt demand t t')
Proof
  strip_tac >>
  drule current_outputs_compatible_length >> strip_tac >>
  simp[bind_outputs_def] >>
  rpt strip_tac >> gvs[] >> irule current_outputs_fold_agree >>
  metis_tac[]
QED

Theorem current_outputs_fold_frame:
  !writes st.
    execution_frame (FOLDL (\s (x,w). update_var x w s) st writes) =
      execution_frame st /\
    state_frame (FOLDL (\s (x,w). update_var x w s) st writes) = state_frame st
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem current_bind_outputs_frame:
  bind_outputs outs vals st = SOME t ==>
    execution_frame t = execution_frame st /\ state_frame t = state_frame st
Proof
  simp[bind_outputs_def] >>
  strip_tac >> gvs[current_outputs_fold_frame]
QED

(* The first output is dead after the second write, even with duplicate
   source spellings. Intermediate maps, not the final map, label each write. *)
Theorem current_outputs_duplicate_probe:
  latest_current_name mid x = y /\ latest_current_name rt x = z ==>
  current_outputs_compatible rs [x;x] rt [y;z] [x]
Proof
  simp[current_outputs_compatible_def, current_before_outputs_def,
       current_write_compatible_def] >> metis_tac[]
QED

Theorem current_bind_outputs_duplicate_probe:
  latest_current_name mid x = y /\ latest_current_name rt x = z ==>
  current_name_agree rt [x]
    (THE (bind_outputs [x;x] [a;b] st))
    (THE (bind_outputs [y;z] [a;b] st'))
Proof
  simp[bind_outputs_def, current_name_agree_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_outputs_overwrite_probe:
  current_outputs_compatible rs [x] rs [latest_current_name rs x] [x] /\
  current_name_agree rs [x]
    (update_var x w st) (update_var (latest_current_name rs x) w st')
Proof
  simp[current_outputs_compatible_def, current_before_outputs_def,
       current_write_compatible_def, current_name_agree_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem current_bind_outputs_empty_probe:
  bind_outputs [] [] st = SOME st /\
  (current_outputs_compatible rs [] rt ys demand <=> rs = rt /\ ys = [])
Proof
  simp[bind_outputs_def, current_outputs_compatible_def]
QED

(* Malformed ignored outputs cannot license demand killing: NOP does not
   perform the writes advertised in its output field. *)
Theorem current_nop_ignored_output_probe:
  !st.
  current_outputs_compatible ([],[]) ["x"] ([],[("x",["y"])]) ["y"] ["x"] /\
  current_name_agree ([],[]) (current_before_outputs ["x"] ["x"]) st st /\
  step_inst_base
    <|inst_id := 0; inst_opcode := NOP; inst_operands := []; inst_outputs := ["x"]|>
    st = OK st /\
  step_inst_base
    <|inst_id := 0; inst_opcode := NOP; inst_operands := []; inst_outputs := ["y"]|>
    st = OK st /\
  (current_name_agree ([],[("x",["y"])]) ["x"] st st <=>
    lookup_var "x" st = lookup_var "y" st)
Proof
  simp[current_outputs_compatible_def, current_write_compatible_def,
       current_before_outputs_def, current_name_agree_def,
       latest_current_name_def, step_inst_base_def]
QED

Theorem current_nop_post_agreement_fails_probe:
  !st. ~current_name_agree ([],[("x",["y"])]) ["x"]
    (st with vs_vars := FEMPTY |+ ("x",0w) |+ ("y",1w))
    (st with vs_vars := FEMPTY |+ ("x",0w) |+ ("y",1w))
Proof
  simp[current_name_agree_def, latest_current_name_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC
QED
