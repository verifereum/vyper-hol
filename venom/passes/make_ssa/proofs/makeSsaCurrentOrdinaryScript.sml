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
