(* Scratch probe: o1_source_unit_ok on hand-built programs that use forms
   outside supported_program. *)
Theory o1ShapeProbeExtra
Ancestors
  evalCompiler unitShapeDefs compileVyper concretizeMemLocDefs
  alist byte integer_word option
Libs finite_mapLib computeLib wordsLib

val rcf = ``<| rcf_max_outsize := 0; rcf_is_delegate := F;
              rcf_is_static := F; rcf_revert_on_failure := T |>``
val rcf_delegate = ``<| rcf_max_outsize := 0; rcf_is_delegate := T;
              rcf_is_static := F; rcf_revert_on_failure := T |>``

(* @external def foo(t: address): raw_call(t, msg.data) *)
Definition x_raw_call_msg_data_program_def:
  x_raw_call_msg_data_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("t", BaseT AddressT)] ([] : expr list) NoneT
       [Expr (Call NoneT (RawCallCalldataTarget ^rcf)
          [Name (BaseT AddressT) "t"; Literal (BaseT (UintT 256)) (IntL 0)]
          NONE)]]
End

(* @external def foo(t: address): raw_call(t, msg.data, is_delegate_call=True) *)
Definition x_delegate_msg_data_program_def:
  x_delegate_msg_data_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("t", BaseT AddressT)] ([] : expr list) NoneT
       [Expr (Call NoneT (RawCallCalldataTarget ^rcf_delegate)
          [Name (BaseT AddressT) "t"; Literal (BaseT (UintT 256)) (IntL 0)]
          NONE)]]
End

(* imm: immutable(uint256); __init__: imm = 5; foo() -> uint256: return imm *)
Definition x_immutable_read_program_def:
  x_immutable_read_program =
    [VariableDecl Private Immutable "imm" (BaseT (UintT 256)) NONE;
     FunctionDecl Deploy Nonpayable F F "__init__"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "imm")))
          (Literal (BaseT (UintT 256)) (IntL 5))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (TopLevelName (BaseT (UintT 256)) (NONE, "imm")))]]
End

(* @internal def bar(x: uint256) -> uint256: (loop first) for i in range(2): pass; return x *)
Definition x_internal_loop_first_program_def:
  x_internal_loop_first_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          2 [Pass];
        Return (SOME (Name (BaseT (UintT 256)) "x"))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
          [Name (BaseT (UintT 256)) "x"] NONE))]]
End

(* internal baz -> internal bar -> external foo *)
Definition x_internal_chain_program_def:
  x_internal_chain_program =
    [FunctionDecl Internal Nonpayable F F "baz"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))];
     FunctionDecl Internal Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Call (BaseT (UintT 256)) (IntCall (NONE, "baz"))
          ([] : expr list) NONE))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
          ([] : expr list) NONE))]]
End

(* @internal def bar(x) -> uint256: y: uint256 = x + 1; return y *)
Definition x_internal_local_program_def:
  x_internal_local_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "x";
              Literal (BaseT (UintT 256)) (IntL 1)]);
        Return (SOME (Name (BaseT (UintT 256)) "y"))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
          [Name (BaseT (UintT 256)) "x"] NONE))]]
End

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := ~1

val out = TextIO.openAppend "/tmp/opus-626-probe-extra.out"
fun say s = (TextIO.output (out, s ^ "\n"); TextIO.flushOut out;
             print (s ^ "\n"))

val rpolicy = optionSyntax.dest_some (rhs (concl
  (EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)))

val theories = ["o1ShapeProbeExtra"]

val only = case OS.Process.getEnv "PROBE_ONLY" of
             SOME s => String.tokens (fn c => c = #",") s | NONE => []

fun programs thy =
  List.mapPartial
    (fn (n, th) =>
       if String.isSuffix "_program_def" n then
         SOME (fst (dest_eq (concl (SPEC_ALL th))))
       else NONE) (DB.definitions thy)

val all_programs = List.concat (map programs theories)
val all_programs =
  if null only then all_programs
  else List.filter (fn p => mem (fst (dest_const p)) only) all_programs

fun dlist t = fst (listSyntax.dest_list t)
fun ev tm = rhs (concl (EVAL tm))
fun evb tm = let val r = ev tm in
               if aconv r T then "T" else if aconv r F then "F"
               else "STUCK" end

fun tstr tm = term_to_string tm

(* opaque_use_ok: least closure of copy_phi_var computed in ML. *)
fun opaque_check fname fn_tm =
  let
    val triples = dlist (ev
      ``MAP (\i. (i, i.inst_opcode, i.inst_operands, i.inst_outputs))
            (fn_insts ^fn_tm)``)
    val insts = map (fn t => let val (i, rest) = pairSyntax.dest_pair t
                                 val (opc, rest) = pairSyntax.dest_pair rest
                                 val (ops, outs) = pairSyntax.dest_pair rest
                             in (i, fst (dest_const opc), dlist ops,
                                 map stringSyntax.fromHOLstring
                                   (dlist outs)) end) triples
    fun var_of opd = if is_comb opd andalso
                       fst (dest_const (rator opd)) = "Var"
                    then SOME (stringSyntax.fromHOLstring (rand opd))
                    else NONE
    fun closure origin =
      let
        val seeds = List.concat (map (fn (_, opc, _, outs) =>
                      if opc = origin then outs else []) insts)
        fun step set =
          let val new = List.concat (map (fn (_, opc, ops, outs) =>
                if (opc = "ASSIGN" andalso length ops = 1) orelse opc = "PHI"
                then if List.exists (fn opd => case var_of opd of
                                         SOME y => mem y set | NONE => false) ops
                     then List.filter (fn x => not (mem x set)) outs else []
                else []) insts)
          in if null new then set else step (set @ new) end
      in step seeds end
    val gas = closure "GAS"
    val retpc = closure "RETPC_PARAM"
    val bad = ref []
    fun is_var x opd = var_of opd = SOME x
    (* gas_use_ok / retpc_use_ok decided on the concrete operand list *)
    fun gas_ok (opc, ops) x =
      opc = "ASSIGN" orelse opc = "PHI" orelse
      ((opc = "CALL" orelse opc = "STATICCALL") andalso
       (case ops of h :: rest => is_var x h andalso
                                 not (List.exists (is_var x) rest)
                  | [] => false))
    fun retpc_ok (opc, ops) x =
      opc = "ASSIGN" orelse opc = "PHI" orelse
      (opc = "RET" andalso not (null ops) andalso
       is_var x (List.last ops) andalso
       not (List.exists (is_var x) (List.take (ops, length ops - 1))))
    fun show_ops ops = "[" ^ String.concatWith "; " (map tstr ops) ^ "]"
    fun chk (i, opc, ops, _) =
      List.app (fn opd =>
        case var_of opd of
          NONE => ()
        | SOME x =>
            (if mem x gas andalso not (gas_ok (opc, ops) x)
             then bad := ("gas " ^ x ^ " used in " ^ opc ^ " " ^ show_ops ops)
                         :: !bad else ();
             if mem x retpc andalso not (retpc_ok (opc, ops) x)
             then bad := ("retpc " ^ x ^ " used in " ^ opc ^ " " ^ show_ops ops)
                         :: !bad else ()))
        ops
  in List.app chk insts; rev (!bad) end

fun report_filter label tm =
  let val r = ev tm in
    say ("      " ^ label ^ ": " ^ tstr r)
  end

fun probe_fn is_head fn_tm =
  let
    val fname = stringSyntax.fromHOLstring (ev ``(^fn_tm).fn_name``)
    val checks =
      [("entry_label", ``fn_entry_label ^fn_tm = SOME (^fn_tm).fn_name``,
        ``fn_entry_label ^fn_tm``),
       ("reserved_labels",
        ``EVERY (\bb. ~reserved_label bb.bb_label) (^fn_tm).fn_blocks``,
        ``FILTER reserved_label (MAP (\bb. bb.bb_label) (^fn_tm).fn_blocks)``),
       ("inst_shape_ok", ``EVERY inst_shape_ok (fn_insts ^fn_tm)``,
        ``MAP (\i. (i.inst_opcode, i.inst_operands))
           (FILTER (\i. ~inst_shape_ok i) (fn_insts ^fn_tm))``),
       ("raw_opcode_ok",
        ``EVERY (\i. raw_opcode_ok i.inst_opcode) (fn_insts ^fn_tm)``,
        ``MAP (\i. (i.inst_opcode, i.inst_operands))
           (FILTER (\i. ~raw_opcode_ok i.inst_opcode) (fn_insts ^fn_tm))``),
       ("first_block_no_preds", ``first_block_no_preds ^fn_tm``,
        ``(HD (^fn_tm).fn_blocks).bb_label,
          MAP (\bb. bb.bb_label)
            (FILTER (\bb. MEM (HD (^fn_tm).fn_blocks).bb_label (bb_succs bb))
               (^fn_tm).fn_blocks)``)] @
      (if is_head then []
       else [("internal_termination",
              ``EVERY (\i. ~MEM i.inst_opcode [STOP; RETURN]) (fn_insts ^fn_tm)``,
              ``MAP (\i. i.inst_opcode)
                  (FILTER (\i. MEM i.inst_opcode [STOP; RETURN])
                     (fn_insts ^fn_tm))``)])
    val results = map (fn (n, c, w) => (n, evb c, w)) checks
    val opaque = opaque_check fname fn_tm
    val fails = List.filter (fn (_, r, _) => r <> "T") results
    val dump = TextIO.openAppend "/tmp/opus-626-extra-units.txt"
    val () = TextIO.output (dump, "#### fn " ^ fname ^ "\n" ^ tstr (ev
      ``MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode, i.inst_operands,
                     i.inst_outputs)) bb.bb_instructions)) (^fn_tm).fn_blocks``)
      ^ "\n")
    val () = TextIO.closeOut dump
    val nblocks = length (dlist (ev ``(^fn_tm).fn_blocks``))
  in
    say ("    fn " ^ fname ^ " (" ^ Int.toString nblocks ^ " blocks): " ^
         (if null fails andalso null opaque then "ok"
          else String.concatWith ", "
                 (map (fn (n, r, _) => n ^ "=" ^ r) fails @
                  (if null opaque then [] else ["opaque_use_ok=F"]))));
    List.app (fn (n, _, w) => report_filter n w) fails;
    List.app (fn s => say ("      opaque: " ^ s)) opaque
  end

fun probe p =
  let
    val name = fst (dest_const p)
    val t0 = Time.now ()
    val r = ev ``lower_vyper_runtime_unit ^p ^rpolicy``
    val secs = Time.toReal (Time.- (Time.now (), t0))
    val () = let val d = TextIO.openAppend "/tmp/opus-626-extra-units.txt"
             in TextIO.output (d, "######## " ^ name ^ "\n"); TextIO.closeOut d end
    val _ = say ("== " ^ name ^ " lowered in " ^ Real.fmt (StringCvt.FIX (SOME 1)) secs ^ "s")
  in
    if optionSyntax.is_none r then say "  lowering = NONE"
    else if not (optionSyntax.is_some r) then
      say ("  lowering STUCK: " ^ String.substring (tstr r, 0,
             Int.min (400, size (tstr r))))
    else
      let
        val u = optionSyntax.dest_some r
        val unit_checks =
          [("entry_fn_first",
            ``(^u).cu_context.ctx_functions <> [] /\
              (^u).cu_context.ctx_entry =
                SOME (HD (^u).cu_context.ctx_functions).fn_name``),
           ("entry_fn_no_ret",
            ``entry_fn_no_ret (HD (^u).cu_context.ctx_functions)``),
           ("entry_no_params",
            ``get_params (HD (HD (^u).cu_context.ctx_functions).fn_blocks)
                .bb_instructions = []``)]
        val ures = map (fn (n, c) => (n, evb c)) unit_checks
        val fns = dlist (ev ``(^u).cu_context.ctx_functions``)
        val whole = "n/a"
      in
        say ("  o1_source_unit_ok = " ^ whole ^ "; entry = " ^
             tstr (ev ``(^u).cu_context.ctx_entry``) ^ "; " ^
             String.concatWith ", " (map (fn (n, r) => n ^ "=" ^ r) ures));
        case fns of
          [] => say "  no functions"
        | h :: rest => (probe_fn true h; List.app (probe_fn false) rest)
      end
  end
  handle e => say ("  EXCEPTION: " ^ General.exnMessage e)

val () = say ("#### probe start, " ^ Int.toString (length all_programs) ^ " programs")
val () = List.app probe all_programs
val () = say "#### probe done"
