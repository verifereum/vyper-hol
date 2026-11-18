Theory staticO1CodeEndProbe
Ancestors
  o1PipelineCorrect codegenReadyCompute staticAbortDefs codegenSymRel
  lowerDloadDefs venomExecSemantics venomCompilerTypes venomState venomInst
  alist integer_word finite_map
Libs
  wordsLib finite_mapLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos,
   finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.FEVERY_FEMPTY,
   finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY,
   pred_setTheory.IN_COMPL])

fun eval tm = rhs (concl (EVAL tm))
fun require msg ok = if ok then () else raise Fail msg

val offset = ``0x8000000000000000000000000000000000000000000000000000000000000000w:256 word``
val fnIn = ``mk_raw_function "main"
  [<|bb_label := "main"; bb_instructions :=
     [mk_inst 0 TSTORE [Lit 0w; Lit 1w] [];
      mk_inst 1 DLOADBYTES [Lit 0w; Lit ^offset; Lit 0w] [];
      mk_inst 2 TSTORE [Lit 0w; Lit 2w] [];
      mk_inst 3 STOP [] []]|>]``
val ctxIn = ``mk_venom_context [^fnIn] (SOME "main")``
val unitIn = ``<|cu_context := ^ctxIn; cu_data_segment := []|>``
val policy = ``THE (resolve_o1_policy (o1_policy all_capabilities))``
val initial = eval ``(init_venom_state "main") with
  <|vs_call_ctx := empty_call_context with cc_static := T;
    vs_labels := FEMPTY |+ ("code_end", 0w)|>``
val () = require "initial empty code/data and code_end = 0"
  (aconv (eval ``(^initial).vs_code = [] /\ (^initial).vs_data_section = [] /\
    FLOOKUP (^initial).vs_labels "code_end" = SOME 0w``) boolSyntax.T)
val srcShape = eval ``o1_source_unit_ok ^unitIn /\
  unit_entry_no_params ^unitIn /\ unit_defs_reach_uses ^unitIn /\
  unit_fmp_unsealed ^unitIn``
val () = print ("Source shape checks: " ^ term_to_string srcShape ^ "\n")
val sourceFirst = eval ``step_inst 0 ^ctxIn (HD (fn_insts ^fnIn)) ^initial``
val () = require "source first step should abort at TSTORE"
  (same_const (fst (strip_comb sourceFirst)) (fst (strip_comb ``Abort ExHalt_abort ^initial``))
   andalso aconv (hd (snd (strip_comb sourceFirst))) ``ExHalt_abort``)
val () = print "Source first instruction TSTORE aborts with ExHalt_abort.\n"

val compiled = eval ``o1PipelineCorrect$o1_pipeline ^policy ^unitIn``
val output = optionSyntax.dest_some compiled
  handle HOL_ERR _ => raise Fail ("O1 output: " ^ term_to_string compiled)
val ctxOut = eval ``(^output).po_unit.cu_context``
val fnOut = eval ``HD (^ctxOut).ctx_functions``
val () = require "target has one straight-line block"
  (aconv (eval ``LENGTH (^fnOut).fn_blocks``) ``1:num``)
val () = require "target EOM is zero"
  (aconv (eval ``max_live_eom ^ctxOut``) ``SOME 0:num option``)
val (insns, _) = listSyntax.dest_list (eval ``fn_insts ^fnOut``)
val () = print ("O1 output opcodes: " ^
  term_to_string (eval ``MAP (\i. i.inst_opcode) (fn_insts ^fnOut)``) ^ "\n")

fun advance s (inst :: rest) =
    if aconv (eval ``(^inst).inst_opcode``) ``CODECOPY`` then (s, inst)
    else let
      val step = eval ``step_inst 0 ^ctxOut ^inst ^s``
      val (opHead, args) = strip_comb step
      val () = require "target should reach CODECOPY before a fault"
        (same_const opHead (fst (strip_comb ``OK ^s``)))
      val next = hd args
      val nextAt = eval ``^next with vs_inst_idx := SUC (^s).vs_inst_idx``
    in advance nextAt rest end
  | advance _ [] = raise Fail "O1 output contains no reached CODECOPY"

val (reached, copy) = advance initial insns
val [_, src, _] = fst (listSyntax.dest_list (eval ``(^copy).inst_operands``))
val (srcTag, [srcVar]) = strip_comb src
val () = require "CODECOPY source is a variable"
  (same_const srcTag (fst (strip_comb ``Var ""``)))
val () = require "CODECOPY source is seeded by a code_end ADD"
  (List.exists (fn inst =>
    aconv (eval ``(^inst).inst_opcode = ADD /\
      LENGTH (^inst).inst_operands = 2 /\
      EL 1 (^inst).inst_operands = Label "code_end" /\
      MEM ^srcVar (^inst).inst_outputs``) boolSyntax.T) insns)
val () = require "CODECOPY source has the bad offset"
  (aconv (eval ``eval_operand ^src ^reached``) ``SOME ^offset``)
val () = require "CODECOPY observes code_end zero"
  (aconv (eval ``FLOOKUP (^reached).vs_labels "code_end"``) ``SOME (0w:256 word)``)
val () = require "target offset falsifies the strict bound"
  (aconv (eval ``w2n (^offset - 0w) < dimword (:256) DIV 2``) boolSyntax.F)
val () = print "Target reaches a code_end-derived CODECOPY at offset 2^255. The strict bound is false.\n"

