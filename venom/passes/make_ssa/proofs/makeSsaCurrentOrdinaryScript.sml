Theory makeSsaCurrentOrdinary
Ancestors
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomExecSemantics venomState
  stateFrame venomInst venomWf list rich_list

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
