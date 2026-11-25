(* Normalize the reached array's storage or transient reads at the selected word key. *)
Theory bodyMembershipSlotReadInputsMods
Ancestors
  builtinProps compileEnv list words arithmetic

Theorem membership_slot_read_inputs_mods:
  loc = (if tr then LocTransient else LocStorage) /\
  elem_size_in_location cenv loc ety = 1 /\
  (!i. i < LENGTH ws ==>
    let addr = w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i) in
    key_taint (if tr then Tu.t_trans else Tu.t_stor) addr = {} /\
    (if tr then tload addr u else sload addr u) = EL i ws) /\
  (!cap. bd = Dynamic cap ==>
    key_taint (if tr then Tu.t_trans else Tu.t_stor) w = {} /\
    (if tr then tload w u else sload w u) = n2w (LENGTH ws)) ==>
  (!i. i < LENGTH ws ==>
    let skip = case bd of Fixed _ => 0 | Dynamic _ => word_scale loc in
    let addr = w + n2w (skip + elem_size_in_location cenv loc ety * i) in
    ptr_load_val cenv.ce_is_ctor loc addr u = EL i ws /\
    (loc = LocStorage ==> key_taint Tu.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint Tu.t_trans addr = {})) /\
  (!cap. bd = Dynamic cap ==>
    case loc of
      LocStorage => key_taint Tu.t_stor w = {} /\ sload w u = n2w (LENGTH ws)
    | LocTransient => key_taint Tu.t_trans w = {} /\ tload w u = n2w (LENGTH ws)
    | _ => F)
Proof
  strip_tac >> Cases_on `tr` >> gvs[] >> Cases_on `bd` >>
  gvs[word_scale_def, ptr_load_val_def] >> metis_tac[]
QED
