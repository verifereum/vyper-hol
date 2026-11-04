Theory makeSsaCurrentOrdinary
Ancestors
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomExecSemantics venomState
  stateFrame venomInst venomWf list rich_list venomCallOracleProps
  venomCallOracleDefs pair dretShapeDefs

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

Definition current_result_agree_def:
  current_result_agree rt demand r r' <=>
    case (r,r') of
      (OK st, OK st') => execution_frame st = execution_frame st' /\
        st.vs_current_bb = st'.vs_current_bb /\
        st.vs_prev_bb = st'.vs_prev_bb /\ current_name_agree rt demand st st'
    | (Halt st, Halt st') => execution_frame st = execution_frame st'
    | (Abort a st, Abort a' st') => a = a' /\ execution_frame st = execution_frame st'
    | (IntRet v st, IntRet v' st') => v = v' /\ execution_frame st = execution_frame st'
    | (Error e, Error e') => e = e'
    | _ => F
End

Theorem current_outputs_singleton_compatible:
  current_outputs_compatible rs [x] rt ys demand <=>
    ?y. ys = [y] /\ current_write_compatible rs rt x y demand
Proof
  simp[current_outputs_compatible_def, current_before_outputs_def] >>
  metis_tac[]
QED

Theorem current_result_write_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_write_compatible rs rt x y demand /\
  current_name_agree rs (FILTER (\v. v <> x) demand) st st' ==>
  current_result_agree rt demand
    (OK (update_var x w st)) (OK (update_var y w st'))
Proof
  strip_tac >>
  `current_name_agree rt demand (update_var x w st) (update_var y w st')`
    by (irule current_write_agree >> metis_tac[]) >>
  gvs[current_result_agree_def, update_var_def]
QED

Theorem current_wf_nop_agree:
  inst_wf inst /\ inst.inst_opcode = NOP /\ inst'.inst_opcode = NOP /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> gvs[inst_wf_def] >>
  gvs[current_outputs_compatible_def, current_before_outputs_def] >>
  simp[step_inst_base_def] >> simp[current_result_agree_def]
QED

Theorem current_single_output_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (case inst.inst_outputs of [x] => OK (update_var x w st) | _ => Error e)
    (case inst'.inst_outputs of [y] => OK (update_var y w st') | _ => Error e)
Proof
  strip_tac >> drule current_outputs_compatible_length >> strip_tac >>
  Cases_on `inst.inst_outputs` >-
    gvs[exec_read0_def, current_outputs_compatible_def, current_result_agree_def] >>
  rename1 `inst.inst_outputs = x::xs` >> Cases_on `xs`
  >- (gvs[current_outputs_singleton_compatible] >>
      simp[exec_read0_def] >> irule current_result_write_agree >>
      gvs[current_before_outputs_cons, current_before_outputs_def] >> metis_tac[]) >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `inst'.inst_outputs = y::ys` >> Cases_on `ys` >> gvs[] >>
  simp[exec_read0_def, current_result_agree_def]
QED

Theorem current_exec_pure1_agree:
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (exec_pure1 f inst st) (exec_pure1 f inst' st')
Proof
  strip_tac >>
  drule_all current_rename_operands_pointwise >> strip_tac >>
  Cases_on `inst.inst_operands`
  >- gvs[rename_current_operands_def, exec_pure1_def, current_result_agree_def] >>
  rename1 `inst.inst_operands = op::ops` >> Cases_on `ops`
  >- (gvs[LIST_REL_EL_EQN] >>
      `eval_operand (HD (rename_current_operands rs [op])) st' = eval_operand op st`
        by metis_tac[current_eval_operand_agree] >>
      Cases_on `eval_operand (HD (rename_current_operands rs [op])) st'`
      >- gvs[exec_pure1_def, current_result_agree_def] >>
      gvs[] >> qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM) >>
      simp[exec_pure1_def] >>
      irule current_single_output_agree >>
      simp[] >> metis_tac[]) >>
  gvs[current_rename_operands_map, exec_pure1_def, current_result_agree_def]
QED

Theorem current_exec_read0_agree:
  f st = f st' /\ execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (exec_read0 f inst st) (exec_read0 f inst' st')
Proof
  strip_tac >> simp[exec_read0_def] >>
  irule current_single_output_agree >> metis_tac[]
QED

Theorem current_exec_pure2_agree:
  LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (exec_pure2 f inst st) (exec_pure2 f inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >> rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  simp[exec_pure2_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand b st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_single_output_agree >> metis_tac[]
QED

Theorem current_exec_pure3_agree:
  LENGTH inst.inst_operands = 3 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (exec_pure3 f inst st) (exec_pure3 f inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >> rename1 `inst.inst_operands = [a;b;c]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand c st = _` (assume_tac o SYM) >>
  simp[exec_pure3_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand b st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand c st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_single_output_agree >> metis_tac[]
QED

Theorem current_exec_read1_agree:
  (!w. f w st = f w st') /\ LENGTH inst.inst_operands = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (exec_read1 f inst st) (exec_read1 f inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >> rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  simp[exec_read1_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_single_output_agree >> metis_tac[]
QED

(* ALLOCA's allocation key is an instruction id, so alpha correspondence
   cannot forget ids even when its output names are compatible. *)
Theorem current_alloca_distinct_id_probe:
  !st. ~current_result_agree ([],[]) []
    (exec_alloca
      <|inst_id := 0; inst_opcode := ALLOCA; inst_operands := [Lit 1w]; inst_outputs := ["x"]|>
      (st with vs_allocas := FEMPTY) 1w)
    (exec_alloca
      <|inst_id := 1; inst_opcode := ALLOCA; inst_operands := [Lit 1w]; inst_outputs := ["x"]|>
      (st with vs_allocas := FEMPTY) 1w)
Proof
  simp[exec_alloca_def, finite_mapTheory.FLOOKUP_EMPTY, current_result_agree_def] >>
  rpt strip_tac >>
  qpat_x_assum `execution_frame _ = _`
    (mp_tac o AP_TERM ``\s:venom_state. FLOOKUP s.vs_allocas 0``) >>
  simp[execution_frame_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem current_exec_alloca_agree:
  inst'.inst_id = inst.inst_id /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (exec_alloca inst st sz) (exec_alloca inst' st' sz)
Proof
  strip_tac >>
  `st.vs_allocas = st'.vs_allocas /\ st.vs_alloca_next = st'.vs_alloca_next`
    by (conj_tac >>
        qpat_x_assum `execution_frame _ = _`
          (mp_tac o AP_TERM ``\s:venom_state. (s.vs_allocas,s.vs_alloca_next)``) >>
        simp[execution_frame_def]) >>
  drule current_outputs_compatible_length >> strip_tac >>
  Cases_on `inst.inst_outputs`
  >- gvs[exec_alloca_def, current_outputs_compatible_def, current_result_agree_def] >>
  rename1 `inst.inst_outputs = x::xs` >> Cases_on `xs`
  >- (gvs[current_outputs_singleton_compatible] >>
      simp[exec_alloca_def] >>
      Cases_on `FLOOKUP st'.vs_allocas inst.inst_id`
      >- (simp[] >> irule current_result_write_agree >> simp[] >>
          conj_tac
          >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
              simp[execution_frame_def] >>
              disch_then (mp_tac o AP_TERM
                ``\s:venom_state. s with <|
                  vs_allocas := st'.vs_allocas |+ (inst.inst_id,(st'.vs_alloca_next,w2n sz));
                  vs_alloca_next := st'.vs_alloca_next + w2n sz|>``) >> simp[]) >>
          qexists_tac `rs` >>
          gvs[current_before_outputs_def, current_name_agree_def, lookup_var_def]) >>
      Cases_on `x'` >> simp[] >> irule current_result_write_agree >>
      simp[] >> qexists_tac `rs` >> gvs[current_before_outputs_def]) >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `inst'.inst_outputs = y::ys` >> Cases_on `ys` >> gvs[] >>
  simp[exec_alloca_def, current_result_agree_def]
QED

Theorem current_exec_write2_agree:
  (!a b. current_result_agree rs demand (OK (f a b st)) (OK (f a b st'))) /\
  LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_result_agree rs demand (exec_write2 f inst st) (exec_write2 f inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >> rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  simp[exec_write2_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand b st`
  >- simp[current_result_agree_def] >> simp[]
QED

Theorem current_effect_agree:
  execution_frame t = execution_frame t' /\
  t.vs_current_bb = t'.vs_current_bb /\ t.vs_prev_bb = t'.vs_prev_bb /\
  t.vs_vars = st.vs_vars /\ t'.vs_vars = st'.vs_vars /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (OK t) (OK t')
Proof
  simp[current_result_agree_def, current_name_agree_def, lookup_var_def]
QED

Theorem current_jump_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (OK (jump_to lbl st)) (OK (jump_to lbl st'))
Proof
  simp[current_result_agree_def, jump_to_def, current_name_agree_def,
       lookup_var_def]
QED

Theorem current_jnz_agree:
  inst.inst_operands = [cond; Label yes; Label no] /\
  inst.inst_opcode = JNZ /\ inst'.inst_opcode = JNZ /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `eval_operand (HD (rename_current_operands rs [cond])) st' = eval_operand cond st`
    by (irule current_eval_operand_occurrence >> metis_tac[MEM]) >>
  gvs[current_rename_operands_map] >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operand cond st`
  >- simp[current_result_agree_def] >>
  simp[] >> Cases_on `x = 0w` >> simp[] >>
  irule current_jump_agree >> metis_tac[]
QED

Theorem current_djmp_agree:
  inst.inst_operands = selector::labels /\
  inst.inst_opcode = DJMP /\ inst'.inst_opcode = DJMP /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `eval_operand (HD (rename_current_operands rs [selector])) st' = eval_operand selector st`
    by (irule current_eval_operand_occurrence >> metis_tac[MEM]) >>
  `rename_current_operands rs (selector::labels) =
     HD (rename_current_operands rs [selector])::rename_current_operands rs labels`
    by simp[current_rename_operands_map] >>
  simp[step_inst_base_def, current_rename_operands_extract_labels] >>
  Cases_on `eval_operand selector st`
  >- simp[current_result_agree_def] >>
  Cases_on `extract_labels labels`
  >- simp[current_result_agree_def] >>
  simp[] >> Cases_on `w2n x < LENGTH x'`
  >- (simp[] >> irule current_jump_agree >> metis_tac[]) >>
  simp[current_result_agree_def]
QED

Theorem current_ret_agree:
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_fmp = st'.vs_fmp` by
    (qpat_x_assum `execution_frame _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >>
     simp[execution_frame_def]) >>
  drule_all current_eval_operands_agree >> strip_tac >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands st` >>
  gvs[current_result_agree_def] >>
  Cases_on `x` >> gvs[]
QED

Theorem current_store_effects_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (OK (mstore off w st)) (OK (mstore off w st')) /\
  current_result_agree rs demand (OK (mstore8 off w st)) (OK (mstore8 off w st')) /\
  current_result_agree rs demand (OK (sstore key w st)) (OK (sstore key w st')) /\
  current_result_agree rs demand (OK (tstore key w st)) (OK (tstore key w st'))
Proof
  strip_tac >>
  `st.vs_memory = st'.vs_memory /\ st.vs_accounts = st'.vs_accounts /\
   st.vs_call_ctx = st'.vs_call_ctx /\ st.vs_transient = st'.vs_transient` by
    (rpt conj_tac >> qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state.
        (s.vs_memory,s.vs_accounts,s.vs_call_ctx,s.vs_transient)``) >>
     simp[execution_frame_def]) >>
  rpt conj_tac >> (irule current_effect_agree >>
    simp[mstore_def, mstore8_def, sstore_def, tstore_def] >>
    conj_tac
    >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
        simp[execution_frame_def, venom_state_component_equality]) >>
    qexistsl_tac [`st`,`st'`] >> simp[])
QED

Theorem current_result_bind_outputs_agree:
  current_outputs_compatible rs outs rt outs' demand /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (current_before_outputs outs demand) st st' /\
  bind_outputs outs vals st = SOME t /\ bind_outputs outs' vals st' = SOME t' ==>
  current_result_agree rt demand (OK t) (OK t')
Proof
  strip_tac >>
  `current_name_agree rt demand t t'`
    by metis_tac[current_bind_outputs_agree] >>
  `execution_frame t = execution_frame st /\ state_frame t = state_frame st`
    by metis_tac[current_bind_outputs_frame] >>
  `execution_frame t' = execution_frame st' /\ state_frame t' = state_frame st'`
    by metis_tac[current_bind_outputs_frame] >>
  gvs[current_result_agree_def] >>
  gvs[state_frame_def, venom_state_component_equality]
QED

Theorem current_bump_agree:
  inst.inst_opcode = BUMP /\ inst'.inst_opcode = BUMP /\
  LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  drule current_outputs_compatible_length >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand b st`
  >- simp[current_result_agree_def] >> simp[] >>
  irule current_result_bind_outputs_agree >>
  goal_assum $ drule_at Any >>
  qexistsl_tac [`inst'.inst_outputs`,`[x;word_add x x']`] >>
  simp[bind_outputs_def]
QED

Theorem current_terminal_agree:
  (inst.inst_opcode = STOP \/ inst.inst_opcode = SINK \/ inst.inst_opcode = INVALID) /\
  inst'.inst_opcode = inst.inst_opcode /\ execution_frame st = execution_frame st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> gvs[] >> asm_rewrite_tac[step_inst_base_def] >>
  simp[current_result_agree_def] >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  simp[execution_frame_def, halt_state_def, set_returndata_def,
       venom_state_component_equality]
QED

Theorem current_assert_agree:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst'.inst_opcode = inst.inst_opcode /\ LENGTH inst.inst_operands = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >> simp[current_result_agree_def] >>
  Cases_on `x = 0w` >> simp[current_result_agree_def] >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  simp[execution_frame_def, halt_state_def, revert_state_def, set_returndata_def,
       venom_state_component_equality]
QED

Theorem current_return_agree:
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
  inst'.inst_opcode = inst.inst_opcode /\ LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  `st.vs_memory = st'.vs_memory` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
     simp[execution_frame_def]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >> simp[current_result_agree_def] >>
  Cases_on `eval_operand b st` >> simp[current_result_agree_def] >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  simp[execution_frame_def, halt_state_def, revert_state_def, set_returndata_def,
       venom_state_component_equality]
QED

Theorem current_param_agree:
  (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/ inst.inst_opcode = RETPC_PARAM) /\
  inst'.inst_opcode = inst.inst_opcode /\ inst.inst_operands = [Lit idx] /\
  LENGTH inst.inst_outputs = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_params = st'.vs_params /\ st.vs_return_pc_token = st'.vs_return_pc_token` by
    (conj_tac >> qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. (s.vs_params,s.vs_return_pc_token)``) >>
     simp[execution_frame_def]) >>
  drule current_outputs_compatible_length >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, rename_current_operands_def,
      current_outputs_singleton_compatible] >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `w2n idx < LENGTH st'.vs_params` >> simp[current_result_agree_def, update_var_def] >>
  rewrite_tac[GSYM update_var_def] >> irule current_write_agree >> qexists_tac `rs` >>
  gvs[current_before_outputs_def]
QED

Theorem current_dalloca_agree:
  inst.inst_opcode = DALLOCA /\ inst'.inst_opcode = DALLOCA /\
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  drule current_outputs_compatible_length >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map,
      current_outputs_singleton_compatible] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  `st.vs_fmp = st'.vs_fmp` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >> simp[execution_frame_def]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_result_write_agree >> simp[] >>
  conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexists_tac `rs` >>
  gvs[current_before_outputs_def, current_name_agree_def, lookup_var_def]
QED

Theorem current_exec_ext_call_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (exec_ext_call inst st gas addr value ao az ro rz static)
    (exec_ext_call inst' st' gas addr value ao az ro rz static)
Proof
  strip_tac >>
  `venom_call_request st addr value ao az static =
   venom_call_request st' addr value ao az static`
    by metis_tac[venom_call_request_frame] >>
  qabbrev_tac `rq = venom_call_request st addr value ao az static` >>
  `FST (consume_call_outcome rq (w2n ro) (w2n rz) st) =
   FST (consume_call_outcome rq (w2n ro) (w2n rz) st')`
    by metis_tac[consume_call_outcome_frame, PAIR_EQ] >>
  `execution_frame (SND (consume_call_outcome rq (w2n ro) (w2n rz) st)) =
   execution_frame (SND (consume_call_outcome rq (w2n ro) (w2n rz) st'))`
    by metis_tac[consume_call_outcome_frame_transport] >>
  simp[Abbr `rq`, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  irule current_single_output_agree >>
  simp[Excl "consume_call_outcome_eq"] >>
  rpt conj_tac
  >- (qpat_x_assum `consume_call_outcome _ _ _ st = _` mp_tac >>
      simp[consume_call_outcome_eq] >> strip_tac >> gvs[]) 
  >- (qpat_x_assum `consume_call_outcome _ _ _ st' = _` mp_tac >>
      simp[consume_call_outcome_eq] >> strip_tac >> gvs[]) >>
  qexists_tac `rs` >>
  gvs[consume_call_outcome_eq, current_name_agree_def, lookup_var_def]
QED

Theorem current_setfmp_agree:
  inst.inst_opcode = SETFMP /\ inst'.inst_opcode = SETFMP /\
  LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = [] /\ inst'.inst_outputs = [] /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_effect_agree >> simp[] >>
  conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`st`,`st'`] >> simp[]
QED

Theorem current_sha3_agree:
  inst.inst_opcode = SHA3 /\ inst'.inst_opcode = SHA3 /\
  LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  `st.vs_memory = st'.vs_memory` by
    (qpat_x_assum `execution_frame _ = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >> simp[execution_frame_def]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st`
  >- simp[current_result_agree_def] >>
  Cases_on `eval_operand b st`
  >- simp[current_result_agree_def] >>
  simp[] >> irule current_single_output_agree >> metis_tac[]
QED

Theorem current_extract_result_agree:
  execution_frame st = execution_frame st' ==>
  (extract_venom_result st value off sz result = NONE <=>
   extract_venom_result st' value off sz result = NONE) /\
  (!w t. extract_venom_result st value off sz result = SOME (w,t) ==>
    ?t'. extract_venom_result st' value off sz result = SOME (w,t') /\
      execution_frame t = execution_frame t' /\
      t.vs_vars = st.vs_vars /\ t'.vs_vars = st'.vs_vars /\
      t.vs_current_bb = st.vs_current_bb /\ t'.vs_current_bb = st'.vs_current_bb /\
      t.vs_prev_bb = st.vs_prev_bb /\ t'.vs_prev_bb = st'.vs_prev_bb)
Proof
  strip_tac >> Cases_on `result` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `t` >> simp[] >>
  PairCases_on `h` >> simp[] >>
  Cases_on `x0` >> simp[] >>
  gvs[execution_frame_def, venom_state_component_equality,
      write_memory_with_expansion_def] >>
  Cases_on `y` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_concrete_call_inputs_agree:
  execution_frame st = execution_frame st' ==>
  read_memory off sz st = read_memory off sz st' /\
  st.vs_accounts = st'.vs_accounts /\ st.vs_call_ctx = st'.vs_call_ctx /\
  make_venom_delegatecall_state st target gas calldata code static =
    make_venom_delegatecall_state st' target gas calldata code static /\
  make_venom_create_state st addr gas value code =
    make_venom_create_state st' addr gas value code
Proof
  simp[execution_frame_def, venom_state_component_equality] >> strip_tac >>
  simp[read_memory_def, make_venom_delegatecall_state_def,
       make_venom_create_state_def, venom_to_tx_params_def]
QED

Theorem current_exec_delegatecall_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (exec_delegatecall inst st gas addr ao az ro rz)
    (exec_delegatecall inst' st' gas addr ao az ro rz)
Proof
  strip_tac >> drule current_concrete_call_inputs_agree >> strip_tac >>
  asm_simp_tac (srw_ss()) [exec_delegatecall_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result st 1w _ _ result` >>
  `extract_venom_result st 1w (w2n ro) (w2n rz) result = NONE <=>
   extract_venom_result st' 1w (w2n ro) (w2n rz) result = NONE`
    by metis_tac[current_extract_result_agree] >>
  Cases_on `extract_venom_result st 1w (w2n ro) (w2n rz) result`
  >- (gvs[] >> simp[current_result_agree_def]) >>
  PairCases_on `x` >>
  drule_all (cj 2 current_extract_result_agree) >> strip_tac >> simp[] >>
  irule current_single_output_agree >> simp[] >>
  qexists_tac `rs` >>
  gvs[current_name_agree_def, lookup_var_def]
QED

Theorem current_create_request_agree:
  execution_frame st = execution_frame st' ==>
  venom_create_request st value off sz salt =
    venom_create_request st' value off sz salt
Proof
  simp[execution_frame_def, venom_state_component_equality] >> strip_tac >>
  simp[venom_create_request_def, read_memory_def]
QED

Theorem current_consume_create_agree:
  execution_frame st = execution_frame st' /\
  consume_create_outcome rq st = (w,t) /\
  consume_create_outcome rq st' = (w',t') ==>
  w = w' /\ execution_frame t = execution_frame t' /\
  t.vs_vars = st.vs_vars /\ t'.vs_vars = st'.vs_vars /\
  t.vs_current_bb = st.vs_current_bb /\ t'.vs_current_bb = st'.vs_current_bb /\
  t.vs_prev_bb = st.vs_prev_bb /\ t'.vs_prev_bb = st'.vs_prev_bb
Proof
  simp[consume_create_outcome_eq, execution_frame_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

Theorem current_exec_create_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand
    (exec_create inst st value off sz salt)
    (exec_create inst' st' value off sz salt)
Proof
  strip_tac >>
  drule current_create_request_agree >> strip_tac >>
  Cases_on `w2n sz > 2 * max_code_size`
  >- (drule current_outputs_compatible_length >> strip_tac >>
      Cases_on `inst.inst_outputs` >> Cases_on `inst'.inst_outputs` >>
      gvs[exec_create_def, current_result_agree_def] >>
      rename1 `LENGTH xs = LENGTH ys` >>
      Cases_on `xs` >> Cases_on `ys` >>
      gvs[exec_create_def, current_result_agree_def, halt_state_def,
          set_returndata_def, execution_frame_def,
          venom_state_component_equality, current_name_agree_def, lookup_var_def]) >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st` >>
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st'` >>
  drule_all current_consume_create_agree >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  irule current_single_output_agree >> simp[] >>
  qexists_tac `rs` >>
  gvs[current_name_agree_def, lookup_var_def]
QED

Theorem current_write_memory_agree:
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand
    (OK (write_memory_with_expansion off bytes st))
    (OK (write_memory_with_expansion off bytes st'))
Proof
  strip_tac >> irule current_effect_agree >>
  simp[write_memory_with_expansion_def] >> conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`st`,`st'`] >> simp[]
QED

Theorem current_copy3_agree:
  (opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = RETURNDATACOPY \/
   opc = MCOPY \/ opc = DLOADBYTES) /\
  inst.inst_opcode = opc /\ inst'.inst_opcode = opc /\
  LENGTH inst.inst_operands = 3 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b;c]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand c st = _` (assume_tac o SYM) >>
  `st.vs_call_ctx = st'.vs_call_ctx /\ st.vs_code = st'.vs_code /\
   st.vs_data_section = st'.vs_data_section /\ st.vs_memory = st'.vs_memory /\
   st.vs_returndata = st'.vs_returndata` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand b st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand c st` >- simp[current_result_agree_def]) >>
  simp[mcopy_def]
  >~ [`current_result_agree _ _ (if _ then _ else _) _`]
  >- (IF_CASES_TAC
      >- gvs[current_result_agree_def, halt_state_def, set_returndata_def,
             execution_frame_def, venom_state_component_equality,
             current_name_agree_def, lookup_var_def] >>
      simp[] >> irule current_write_memory_agree >> simp[]) >>
  irule current_write_memory_agree >> simp[]
QED

Theorem current_extcodecopy_agree:
  inst.inst_opcode = EXTCODECOPY /\ inst'.inst_opcode = EXTCODECOPY /\
  LENGTH inst.inst_operands = 4 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b;c;d]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand c st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand d st = _` (assume_tac o SYM) >>
  `st.vs_accounts = st'.vs_accounts` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand b st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand c st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand d st` >- simp[current_result_agree_def]) >>
  simp[] >> irule current_write_memory_agree >> simp[]
QED

Theorem current_eval_operands_subset:
  !ops. execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars allops) st st' /\
  (!op. MEM op ops ==> MEM op allops) ==>
  eval_operands (rename_current_operands rs ops) st' = eval_operands ops st
Proof
  Induct >> simp[rename_current_operands_def, eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand (HD (rename_current_operands rs [h])) st' = eval_operand h st`
    by (irule current_eval_operand_occurrence >> metis_tac[]) >>
  `eval_operands (rename_current_operands rs ops) st' = eval_operands ops st`
    by (first_x_assum irule >> metis_tac[]) >>
  Cases_on `h` >> gvs[rename_current_operands_def, eval_operands_def]
QED

Theorem current_log_agree:
  inst.inst_opcode = LOG /\ inst'.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: rest /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> reverse (Cases_on `LENGTH rest = w2n tc + 2`)
  >- (gvs[rename_current_operands_def] >>
      asm_rewrite_tac[step_inst_base_def] >>
      simp[current_result_agree_def]) >>
  `eval_operand (EL 0 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 0 (REVERSE rest)) st` by
    (`MEM (EL 0 (REVERSE rest)) (REVERSE rest)` by
       (irule EL_MEM >> simp[]) >>
     simp[current_rename_operands_el] >> irule current_eval_operand_occurrence >>
     simp[] >> qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operand (EL 1 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 1 (REVERSE rest)) st` by
    (`MEM (EL 1 (REVERSE rest)) (REVERSE rest)` by
       (irule EL_MEM >> simp[]) >>
     simp[current_rename_operands_el] >> irule current_eval_operand_occurrence >>
     simp[] >> qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operands (rename_current_operands rs (DROP 2 (REVERSE rest))) st' =
   eval_operands (DROP 2 (REVERSE rest)) st` by
    (irule current_eval_operands_subset >> simp[] >>
     qexists_tac `inst.inst_operands` >> gvs[] >>
     rpt strip_tac >> drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  gvs[rename_current_operands_def] >>
  asm_rewrite_tac[step_inst_base_def] >>
  simp[GSYM current_rename_operands_reverse, GSYM current_rename_operands_drop] >>
  (Cases_on `eval_operand (HD (REVERSE rest)) st`
   >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand (EL 1 (REVERSE rest)) st`
   >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operands (DROP 2 (REVERSE rest)) st`
   >- simp[current_result_agree_def]) >>
  simp[] >> irule current_effect_agree >> simp[] >> conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`st`,`st'`] >> simp[]
QED

Theorem current_pack_dret_fields:
  !pairs cursor st ptrs final t.
  pack_dret_dynamic cursor pairs st = (ptrs,final,t) ==>
  t.vs_vars = st.vs_vars /\ t.vs_current_bb = st.vs_current_bb /\
  t.vs_prev_bb = st.vs_prev_bb
Proof
  Induct >> simp[pack_dret_dynamic_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem current_mcopy_frame:
  execution_frame (mcopy dst src sz st) = mcopy dst src sz (execution_frame st)
Proof
  simp[mcopy_def, write_memory_with_expansion_def, execution_frame_def]
QED

Theorem current_pack_dret_frame:
  !pairs cursor st st' ptrs final t ptrs' final' t'.
  execution_frame st = execution_frame st' /\
  pack_dret_dynamic cursor pairs st = (ptrs,final,t) /\
  pack_dret_dynamic cursor pairs st' = (ptrs',final',t') ==>
  ptrs = ptrs' /\ final = final' /\ execution_frame t = execution_frame t'
Proof
  Induct >> simp[pack_dret_dynamic_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `execution_frame (mcopy (w2n cursor) (w2n h0) (w2n h1) st) =
   execution_frame (mcopy (w2n cursor) (w2n h0) (w2n h1) st')` by simp[current_mcopy_frame] >>
  qpat_x_assum `execution_frame st = _` kall_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem current_parse_dret_shape:
  inst'.inst_operands = rename_current_operands rs inst.inst_operands ==>
  parse_dret_shape inst' = parse_dret_shape inst
Proof
  strip_tac >> Cases_on `inst.inst_operands` >>
  simp[parse_dret_shape_def, rename_current_operands_def] >>
  Cases_on `h` >> simp[parse_dret_shape_def, rename_current_operands_def]
QED

Theorem current_dret_agree:
  inst.inst_opcode = DRET /\ inst'.inst_opcode = DRET /\
  inst.inst_outputs = [] /\ inst'.inst_outputs = [] /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule current_parse_dret_shape >> strip_tac >>
  drule_all current_eval_operands_agree >> strip_tac >>
  `st.vs_call_entry_fmp = st'.vs_call_entry_fmp` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_simp_tac (srw_ss()) [step_inst_base_DRET] >>
  Cases_on `parse_dret_shape inst` >- simp[current_result_agree_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_operands inst.inst_operands st`
  >- simp[current_result_agree_def] >> simp[] >>
  Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))`
  >- simp[current_result_agree_def] >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_all current_pack_dret_frame >> strip_tac >>
  simp[current_result_agree_def] >>
  qpat_x_assum `execution_frame _ = execution_frame _` mp_tac >>
  simp[execution_frame_def, venom_state_component_equality]
QED

Theorem current_special_read0_agree:
  (opc = GETFMP \/ opc = INITIAL_FMP) /\
  inst.inst_opcode = opc /\ inst'.inst_opcode = opc /\
  inst.inst_operands = [] /\ inst'.inst_operands = [] /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_fmp = st'.vs_fmp /\ st.vs_initial_fmp = st'.vs_initial_fmp` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  gvs[] >> asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  irule current_single_output_agree >> metis_tac[]
QED

Theorem current_assign_agree:
  inst.inst_opcode = ASSIGN /\ inst'.inst_opcode = ASSIGN /\
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map,
      current_outputs_singleton_compatible] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >- simp[current_result_agree_def] >>
  simp[] >> irule current_result_write_agree >> simp[] >>
  qexists_tac `rs` >> gvs[current_before_outputs_def]
QED

Theorem current_istore_agree:
  inst.inst_opcode = ISTORE /\ inst'.inst_opcode = ISTORE /\
  LENGTH inst.inst_operands = 2 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs demand st st' ==>
  current_result_agree rs demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a;b]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  qpat_x_assum `eval_operand b st = _` (assume_tac o SYM) >>
  asm_rewrite_tac[step_inst_base_def] >>
  (Cases_on `eval_operand a st` >- simp[current_result_agree_def]) >>
  (Cases_on `eval_operand b st` >- simp[current_result_agree_def]) >>
  simp[] >> irule current_effect_agree >>
  simp[istore_def, mstore_def, write_memory_with_expansion_def] >> conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      simp[execution_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`st`,`st'`] >> simp[]
QED

Theorem current_selfdestruct_agree:
  inst.inst_opcode = SELFDESTRUCT /\ inst'.inst_opcode = SELFDESTRUCT /\
  LENGTH inst.inst_operands = 1 /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, LIST_REL_def, current_rename_operands_map] >>
  rename1 `inst.inst_operands = [a]` >>
  qpat_x_assum `eval_operand a st = _` (assume_tac o SYM) >>
  `st.vs_call_ctx = st'.vs_call_ctx /\ st.vs_accounts = st'.vs_accounts` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand a st` >- simp[current_result_agree_def] >>
  simp[current_result_agree_def, halt_state_def, execution_frame_def] >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  simp[execution_frame_def, venom_state_component_equality, set_returndata_def]
QED

Theorem current_result_error_agree[simp]:
  current_result_agree rt demand (Error e) (Error e)
Proof
  simp[current_result_agree_def]
QED

Theorem current_create_agree:
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> drule_all current_rename_operands_pointwise >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >>
  asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  irule current_exec_create_agree >> metis_tac[]
QED

Theorem current_external_call_agree:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL) /\
  inst_wf inst /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >>
  `st.vs_call_ctx = st'.vs_call_ctx`
    by (qpat_x_assum `execution_frame _ = _`
          (mp_tac o AP_TERM ``\s:venom_state. s.vs_call_ctx``) >>
        simp[execution_frame_def]) >>
  drule_all current_rename_operands_pointwise >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, current_rename_operands_map, LIST_REL_def] >>
  strip_tac >>
  rpt (qpat_x_assum `eval_operand _ st = eval_operand _ st'` (assume_tac o SYM)) >>
  asm_rewrite_tac[step_inst_base_def] >> simp[] >>
  qpat_x_assum `inst'.inst_operands = _` kall_tac >>
  rpt (qpat_x_assum `eval_operand _ st' = _` kall_tac) >>
  BasicProvers.TOP_CASE_TAC >>
  pure_asm_rewrite_tac[optionTheory.option_case_def, current_result_error_agree] >>
  rpt (BasicProvers.TOP_CASE_TAC >> pure_asm_rewrite_tac[optionTheory.option_case_def, current_result_error_agree]) >>
  FIRST [irule current_exec_ext_call_agree, irule current_exec_delegatecall_agree] >>
  metis_tac[]
QED


(* Select a single semantic boundary for the concrete opcode. *)
val current_base_dispatch : tactic =
  (fn g as (asms,_) =>
    let
      val eq = valOf (List.find (fn t => is_eq t andalso
        is_const (rhs t) andalso type_of (rhs t) = ``:opcode``) asms)
      val opc = fst (dest_const (rhs eq))
      val pure2 = ["ADD","SUB","MUL","Div","Mod","SDIV","SMOD","Exp",
                   "EQ","LT","GT","SLT","SGT","AND","OR","XOR",
                   "SHL","SHR","SAR","SIGNEXTEND","BYTE","OFFSET"]
      fun pure th = simp[step_inst_base_opcode_eqs] >> irule th >>
        simp[] >> conj_tac >- gvs[inst_wf_def] >> qexists_tac `rs` >> simp[]
      val no_outputs = `inst.inst_outputs = []` by gvs[inst_wf_def] >>
        gvs[current_outputs_compatible_def, current_before_outputs_def]
      fun direct th = irule th >> simp[] >> rpt conj_tac >>
        (fn g => (if is_exists (snd g) then
           qexists_tac `rs` >> simp[] >> gvs[inst_wf_def]
         else gvs[inst_wf_def, current_rename_operands_map]) g)
      val tac =
        if mem opc pure2 then pure current_exec_pure2_agree
        else if mem opc ["ADDMOD","MULMOD"] then pure current_exec_pure3_agree
        else if mem opc ["ISZERO","NOT"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_pure1_agree >>
          simp[] >> qexists_tac `rs` >> simp[]
        else if mem opc ["MLOAD","SLOAD","TLOAD","DLOAD","ILOAD","BLOCKHASH","BLOBHASH","BALANCE","CALLDATALOAD","EXTCODESIZE","EXTCODEHASH"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_read1_agree >>
          simp[] >> conj_tac
          >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
              simp[execution_frame_def, venom_state_component_equality,
                   mload_def, sload_def, tload_def,
                   contract_storage_def, contract_transient_def]) >>
          conj_tac >- gvs[inst_wf_def] >> qexists_tac `rs` >> simp[]
        else if mem opc ["ADDRESS","CALLER","CALLVALUE","GAS","ORIGIN","GASPRICE","CHAINID","COINBASE","TIMESTAMP","NUMBER","PREVRANDAO","GASLIMIT","BASEFEE","BLOBBASEFEE","SELFBALANCE","CALLDATASIZE","RETURNDATASIZE","MEMTOP","CODESIZE"] then
          simp[step_inst_base_opcode_eqs] >> irule current_exec_read0_agree >>
          simp[] >> conj_tac
          >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
              simp[execution_frame_def, venom_state_component_equality]) >>
          qexists_tac `rs` >> simp[]
        else if mem opc ["MSTORE","MSTORE8","SSTORE","TSTORE"] then
          no_outputs >> simp[step_inst_base_opcode_eqs] >>
          irule current_exec_write2_agree >> simp[] >> conj_tac
          >- (rpt gen_tac >>
              irule (cj (if opc = "MSTORE" then 1 else if opc = "MSTORE8" then 2
                         else if opc = "SSTORE" then 3 else 4) current_store_effects_agree) >> simp[]) >>
          gvs[inst_wf_def]
        else if opc = "NOP" then irule current_wf_nop_agree >> metis_tac[]
        else if mem opc ["DLOADBYTES","MCOPY","CODECOPY","CALLDATACOPY","RETURNDATACOPY"] then
          `inst.inst_outputs = []` by gvs[inst_wf_def] >>
          gvs[current_outputs_compatible_def, current_before_outputs_def] >>
          irule current_copy3_agree >> simp[] >> gvs[inst_wf_def]
        else if mem opc ["ASSERT","ASSERT_UNREACHABLE"] then
          no_outputs >> irule current_assert_agree >> simp[] >> gvs[inst_wf_def]
        else if mem opc ["RETURN","REVERT"] then direct current_return_agree
        else if mem opc ["STOP","SINK","INVALID"] then
          irule current_terminal_agree >> simp[]
        else if mem opc ["RET","RETFMP"] then direct current_ret_agree
        else if opc = "ASSIGN" then direct current_assign_agree
        else if opc = "DALLOCA" then direct current_dalloca_agree
        else if opc = "BUMP" then direct current_bump_agree
        else if mem opc ["GETFMP","INITIAL_FMP"] then direct current_special_read0_agree
        else if mem opc ["CREATE","CREATE2"] then direct current_create_agree
        else if mem opc ["CALL","STATICCALL","DELEGATECALL"] then direct current_external_call_agree
        else if opc = "SHA3" then direct current_sha3_agree
        else if opc = "DRET" then no_outputs >> direct current_dret_agree
        else if opc = "EXTCODECOPY" then
          no_outputs >> irule current_extcodecopy_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "ISTORE" then
          no_outputs >> irule current_istore_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "SETFMP" then
          no_outputs >> irule current_setfmp_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "LOG" then no_outputs >>
          irule current_log_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "SELFDESTRUCT" then direct current_selfdestruct_agree
        else if mem opc ["PARAM","FMP_PARAM","RETPC_PARAM"] then
          irule current_param_agree >> simp[] >>
          conj_tac >- gvs[inst_wf_def] >>
          conj_tac >- gvs[inst_wf_def] >> qexists_tac `rs` >> simp[]
        else if opc = "ALLOCA" then
          fs[inst_wf_def] >>
          simp[step_inst_base_opcode_eqs, current_rename_operands_map] >>
          irule current_exec_alloca_agree >> simp[] >> qexists_tac `rs` >> simp[]
        else if opc = "DJMP" then no_outputs >>
          irule current_djmp_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "JNZ" then no_outputs >>
          irule current_jnz_agree >> simp[] >> gvs[inst_wf_def]
        else if opc = "JMP" then no_outputs >>
          fs[inst_wf_def] >>
          simp[step_inst_base_opcode_eqs, current_rename_operands_map] >>
          irule current_jump_agree >> simp[]
        else if opc = "PHI" then gvs[]
        else if opc = "INVOKE" then simp[step_inst_base_opcode_eqs]
        else FAIL_TAC ("unrouted " ^ opc)
    in tac g end);

Theorem current_base_family130[local]:
  MEM inst.inst_opcode [Exp;Div;DELEGATECALL;CREATE;CALLVALUE;CALLER;CALLDATASIZE;
    CALLDATALOAD;CALLDATACOPY;BLOCKHASH;ASSIGN;ASSERT_UNREACHABLE;ASSERT;AND;ALLOCA;ADDMOD;ADD] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family131[local]:
  MEM inst.inst_opcode [DRET;DLOADBYTES;DJMP;DALLOCA;CREATE2;CHAINID;CALL;BYTE;BUMP;BASEFEE;BALANCE;ADDRESS] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family132[local]:
  MEM inst.inst_opcode [EXTCODESIZE;EXTCODEHASH;EXTCODECOPY;EQ;DLOAD;COINBASE;CODESIZE;CODECOPY;BLOBHASH;BLOBBASEFEE] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family140[local]:
  MEM inst.inst_opcode [JNZ;JMP;ISZERO;ISTORE;INVOKE;GETFMP;GAS;FMP_PARAM] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family141[local]:
  MEM inst.inst_opcode [INVALID;INITIAL_FMP;ILOAD;GT;GASPRICE;GASLIMIT] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family150[local]:
  MEM inst.inst_opcode [ORIGIN;OFFSET;NUMBER;NOT;NOP;Mod;MULMOD;MUL;MSTORE;MEMTOP;LOG] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family151[local]:
  MEM inst.inst_opcode [MSTORE8;OR] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family152[local]:
  MEM inst.inst_opcode [MLOAD;MCOPY;LT] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family160[local]:
  MEM inst.inst_opcode [TSTORE;TIMESTAMP;SUB;SSTORE;SLT;SHR;SHL;SGT;SETFMP;SELFDESTRUCT;SAR;REVERT;RETURN;RETFMP;RET;PHI] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family161[local]:
  MEM inst.inst_opcode [STOP;STATICCALL;SMOD;SINK;SIGNEXTEND;SHA3;SDIV;PREVRANDAO] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family162[local]:
  MEM inst.inst_opcode [TLOAD;SLOAD;SELFBALANCE;RETURNDATASIZE;RETURNDATACOPY;RETPC_PARAM;PARAM] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_base_family170[local]:
  MEM inst.inst_opcode [XOR] /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  current_base_dispatch
QED

Theorem current_step_inst_base_agree:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_outputs_compatible rs inst.inst_outputs rt inst'.inst_outputs demand /\
  current_name_agree rs (operand_vars inst.inst_operands) st st' /\
  current_name_agree rs (current_before_outputs inst.inst_outputs demand) st st' ==>
  current_result_agree rt demand (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[] >>
  (fn g as (asms,_) =>
    let
      val eq = valOf (List.find (fn t => is_eq t andalso
        is_const (rhs t) andalso type_of (rhs t) = ``:opcode``) asms)
      val opc = fst (dest_const (rhs eq))
      val families = [
        (["Exp","Div","DELEGATECALL","CREATE","CALLVALUE","CALLER","CALLDATASIZE",
          "CALLDATALOAD","CALLDATACOPY","BLOCKHASH","ASSIGN","ASSERT_UNREACHABLE",
          "ASSERT","AND","ALLOCA","ADDMOD","ADD"], current_base_family130),
        (["DRET","DLOADBYTES","DJMP","DALLOCA","CREATE2","CHAINID","CALL","BYTE",
          "BUMP","BASEFEE","BALANCE","ADDRESS"], current_base_family131),
        (["EXTCODESIZE","EXTCODEHASH","EXTCODECOPY","EQ","DLOAD","COINBASE",
          "CODESIZE","CODECOPY","BLOBHASH","BLOBBASEFEE"], current_base_family132),
        (["JNZ","JMP","ISZERO","ISTORE","INVOKE","GETFMP","GAS","FMP_PARAM"],current_base_family140),
        (["INVALID","INITIAL_FMP","ILOAD","GT","GASPRICE","GASLIMIT"],current_base_family141),
        (["ORIGIN","OFFSET","NUMBER","NOT","NOP","Mod","MULMOD","MUL","MSTORE","MEMTOP","LOG"],current_base_family150),
        (["MSTORE8","OR"],current_base_family151),
        (["MLOAD","MCOPY","LT"],current_base_family152),
        (["TSTORE","TIMESTAMP","SUB","SSTORE","SLT","SHR","SHL","SGT","SETFMP",
          "SELFDESTRUCT","SAR","REVERT","RETURN","RETFMP","RET","PHI"],current_base_family160),
        (["STOP","STATICCALL","SMOD","SINK","SIGNEXTEND","SHA3","SDIV","PREVRANDAO"],current_base_family161),
        (["TLOAD","SLOAD","SELFBALANCE","RETURNDATASIZE","RETURNDATACOPY","RETPC_PARAM","PARAM"],current_base_family162),
        (["XOR"],current_base_family170)]
      val th = snd (valOf (List.find (fn (ops,_) => mem opc ops) families))
    in (irule th >> simp[] >> qexists_tac `rs` >> simp[]) g end)
QED
