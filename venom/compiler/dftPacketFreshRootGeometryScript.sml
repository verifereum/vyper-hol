Theory dftPacketFreshRootGeometry
Ancestors
  dftPacketFreshCutGeometry dftPacketChangedCallerSuccess dftPacketCallFreshEntry

Theorem dft_packet_fresh_root_geometry:
  !(F:num) C7 C8 rooted_eval
    (plan_eval : num -> venom_context -> string ->
      (basic_block # num # instruction list) list -> venom_state ->
      (string # num) list # exec_result)
    call_setup plan_ok levels_ok pre sf plan
    incoming root_fn entry bb0 d z0 c nm ops csf ctf args b0 child_entry readings
    cb z p cuts b cuts' levels' q.
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  MAP (\(ai,ds,ei,qi,zi). ai)
    (cuts : ((num # num) list # num list # num # num # instruction list) list) =
      REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts = LENGTH (pre ++ [(sf,plan,NONE)]) /\
  levels_ok F C7 (pre ++ [(sf,plan,NONE)])
    (MAP (\(ai,ds,ei,qi,zi). ai) cuts) incoming root_fn entry [] 0 /\
  LAST plan = (bb0,d,z0) /\
  c = EL (LENGTH z0) (DROP (phi_prefix_length bb0.bb_instructions)
    bb0.bb_instructions) /\
  c.inst_opcode = INVOKE /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME child_entry /\
  lookup_function nm C7.ctx_functions = SOME csf /\
  (!events u.
    rooted_eval F C7 (pre ++ [(sf,plan,NONE)]) entry = (events,OK u) ==>
    u.vs_gas_readings = readings /\
    (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
    (!callee argv.
      setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee argv b0)) /\
  plan_ok F C7 csf d [(cb,SUC d,z)]
    (child_entry with vs_gas_readings := readings) /\
  b = (d,c.inst_id)::p /\
  cuts' = cuts ++ [(b,[],SUC d,q,z)] /\
  levels' = pre ++ [(sf,plan,SOME c);(csf,[(cb,SUC d,z)],NONE)] ==>
  MAP (\(ai,ds,ei,qi,zi). ai) cuts' =
    REVERSE (GENLIST (\i. DROP i b) (SUC (LENGTH b))) /\
  LENGTH cuts' = LENGTH levels' /\
  levels_ok F C7 levels' (MAP (\(ai,ds,ei,qi,zi). ai) cuts')
    (incoming ++ [d]) root_fn entry [] 0
Proof
  qx_gen_tac `fuel` >> rpt gen_tac >> strip_tac >>
  `!events ent.
    rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)]) entry = (events,OK ent) ==>
    plan_ok fuel C7 csf d [(cb,SUC d,z)] ent` by
    (rpt gen_tac >> strip_tac >>
     `?u. rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)]) entry = (events,OK u) /\
          call_setup C7 c u = OK ent` by
       (irule dft_packet_changed_caller_success >>
        conj_tac >- (qexists_tac `plan_eval fuel C7` >> simp[]) >>
        asm_rewrite_tac[]) >>
     first_x_assum drule >> strip_tac >>
     drule_all dft_packet_call_source_setup >> strip_tac >>
     gvs[]) >>
  drule_all dft_packet_call_fresh_cut_geometry >> simp[]
QED
