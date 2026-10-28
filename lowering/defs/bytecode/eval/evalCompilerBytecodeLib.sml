(*
 * Independent Python compiler bytecode oracle reader
 *
 * TOP-LEVEL:
 *   read_hex_bytes -- read pinned-Python deploy/runtime oracle bytes into a term
 *   weak_eval -- checked evaluation preserving unused function-valued fields
 *)

structure evalCompilerBytecodeLib = struct

open HolKernel boolLib bossLib
open evalCompilerBytecodeEventHashTheory
open stackPlanObservationsTheory

(* All corpus consumers share the checked selector conversion. *)
val () = supportedEvalLib.configure ()

(* The imported theory supplies a generic event_hash CV translation. Its
   concrete hash test is not installed as a fixture-specific rewrite. *)
local
  val event_head = prim_mk_const {Thy="vyperEvent",Name="event_hash"}
  fun ordinary tm = Conv.REWR_CONV vyperEventTheory.event_hash_def tm
  fun event_conv tm = let
    val th = if null(free_vars tm) andalso null(type_vars_in_term tm) then
        (cv_transLib.cv_eval tm handle HOL_ERR _ => ordinary tm | Fail _ => ordinary tm)
      else ordinary tm
    val (left,right) = boolSyntax.dest_eq (Thm.concl th)
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if aconv left tm andalso type_of left = type_of right andalso
      null(Thm.hyp th) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then th
    else raise Fail "unsupported event hash certificate" end
  val rules = List.concat (List.concat (map
    (fn (_,xs) => map (fn clauses.RRules ths => ths | clauses.Conversion _ => []) xs)
    (computeLib.listItems (computeLib.the_compset ()))))
  val callers = List.filter (fn th =>
    can (find_term (aconv event_head))
      (boolSyntax.rhs (#2(boolSyntax.strip_forall(Thm.concl th))))
    handle HOL_ERR _ => false) rules
in
  val () = computeLib.del_funs [vyperEventTheory.event_hash_def]
  val () = computeLib.add_convs [(event_head,3,event_conv)]
  val () = computeLib.add_funs callers
end

(* Package and environment results contain functions that compilation applies
   later. Avoid expanding their unused lambda bodies when saving a stage. *)
fun weak_eval tm =
  computeLib.WEAK_CBV_CONV (computeLib.the_compset ()) tm

fun read_all path =
  let
    val input = TextIO.openIn path
  in
    TextIO.inputAll input before TextIO.closeIn input
  end

fun trim s =
  let
    val len = size s
    fun left i =
      if i >= len then len
      else if Char.isSpace (String.sub (s, i)) then left (i + 1)
      else i
    fun right i =
      if i < 0 then ~1
      else if Char.isSpace (String.sub (s, i)) then right (i - 1)
      else i
    val lo = left 0
    val hi = right (len - 1)
  in
    if hi < lo then "" else String.substring (s, lo, hi - lo + 1)
  end

fun strip_comment line =
  trim (case String.fields (fn c => c = #"#") line of
          [] => line
        | before_comment :: _ => before_comment)

fun fixture_line line =
  case strip_comment line of
    "" => NONE
  | line =>
      (case String.fields (fn c => c = #"=") line of
         [key, value] => SOME (trim key, trim value)
       | _ => raise Fail ("bad bytecode fixture line: " ^ line))

fun resolve_bytecode_fixture filename =
  let
    val candidates =
      [OS.Path.concat ("../python-o1-no-asm-opt", filename),
       OS.Path.concat ("bytecode/python-o1-no-asm-opt", filename),
       OS.Path.concat ("lowering/defs/bytecode/python-o1-no-asm-opt", filename)]
  in
    case List.find
           (fn path => OS.FileSys.access (path, [OS.FileSys.A_READ]))
           candidates of
      SOME path => path
    | NONE => raise Fail ("missing bytecode fixture: " ^ filename)
  end

fun bytecode_fixture_value filename entries key =
  case List.find (fn (entry_key, _) => entry_key = key) entries of
    SOME (_, value) => value
  | NONE => raise Fail ("missing " ^ key ^ " in bytecode fixture: " ^ filename)

fun drop_hex_prefix s =
  if String.isPrefix "0x" s orelse String.isPrefix "0X" s then
    String.extract (s, 2, NONE)
  else
    s

fun compact_hex s =
  String.implode (List.filter (not o Char.isSpace)
    (String.explode (drop_hex_prefix s)))

fun hex_digit c =
  if #"0" <= c andalso c <= #"9" then
    Char.ord c - Char.ord #"0"
  else if #"a" <= c andalso c <= #"f" then
    10 + Char.ord c - Char.ord #"a"
  else if #"A" <= c andalso c <= #"F" then
    10 + Char.ord c - Char.ord #"A"
  else
    raise Fail ("bad hex digit: " ^ String.str c)

fun hex_bytes_tm hex =
  let
    val hex = compact_hex hex
    val len = size hex
    val byte_ty = type_of (wordsSyntax.mk_wordii (0, 8))
    val _ =
      if len mod 2 = 0 then ()
      else raise Fail "hex bytecode fixture has odd length"
    fun bytes i acc =
      if i >= len then
        List.rev acc
      else
        let
          val n =
            16 * hex_digit (String.sub (hex, i)) +
            hex_digit (String.sub (hex, i + 1))
        in
          bytes (i + 2) (wordsSyntax.mk_wordii (n, 8) :: acc)
        end
  in
    listSyntax.mk_list (bytes 0 [], byte_ty)
  end

fun read_hex_bytes filename =
  let
    val path = resolve_bytecode_fixture filename
    val entries =
      List.mapPartial fixture_line
        (String.tokens (fn c => c = #"\n" orelse c = #"\r")
           (read_all path))
    val deploy = bytecode_fixture_value filename entries "deploy"
    val runtime = bytecode_fixture_value filename entries "runtime"
  in
    pairSyntax.mk_pair (hex_bytes_tm deploy, hex_bytes_tm runtime)
  end

(* Kernel-checked staged evaluation certificates only. Neither rewrite list
   may contain an oracle equality: oracle bytes are read solely in the final
   parity statement, whose proof remains plain EVAL_TAC. The lowering-stage
   certificates re-evaluate lowering_context_ok, including the budget guard. *)
(* CBV normalizes arguments before matching a compiler equation. *)
fun normalize_call tm =
  if is_comb tm then Conv.COMB2_CONV (normalize_call,computeLib.EVAL_CONV) tm
  else REFL tm

fun normalize_compile_eval certificate =
  Conv.CONV_RULE (Conv.LAND_CONV normalize_call) certificate

val profile_evaluation = OS.Process.getEnv "VYPER_HOL_EVAL_PROFILE" = SOME "1"
fun timed_evaluation head phase run =
  if not profile_evaluation then run () else let
    val started = Time.now ()
    val name = #Name(dest_thy_const head)
    val () = print ("EVAL_PHASE_BEGIN " ^ name ^ " " ^ phase ^ "\n")
    val result = run ()
    val () = print ("EVAL_PHASE_END " ^ name ^ " " ^ phase ^ " " ^
      Time.toString(Time.-(Time.now(),started)) ^ "\n")
  in result end

fun evaluate_call call =
  let
    val head = fst(strip_comb call)
    val inputs = timed_evaluation head "inputs" (fn () => normalize_call call)
    val evaluated = timed_evaluation head "body"
      (fn () => computeLib.EVAL_CONV (rhs(concl inputs)))
  in (TRANS inputs evaluated,evaluated) end

(* Policy records contain functions. computeLib silently ignores rewrite
   patterns containing lambdas, so use exact checked equations as conversions. *)
val compiler_certificates = ref ([] : thm list)
val certificate_heads = ref ([] : term list)
exception PlannerBoundary of term
datatype planner_attempt = PlannerComplete of thm * thm | PlannerPending of term
val planner_capture_heads = ref ([] : term list)
val planner_block_head = prim_mk_const {Thy="stackPlanGen",Name="generate_block_plan"}
val planner_inst_head = prim_mk_const {Thy="stackPlanGen",Name="generate_inst_plan"}
val scheduled_fold_head = prim_mk_const
  {Thy="venomFnScheduleRunner",Name="run_configured_fn_pass_fold"}

(* The symbolic two-pass equation exposes singleton folds. Capturing those
   also certifies their guards, so later steps reuse the completed prefix. *)
fun capture_eligible head tm =
  not(same_const head scheduled_fold_head) orelse
    (length(fst(listSyntax.dest_list(List.nth(snd(strip_comb tm),2)))) = 1
      handle HOL_ERR _ => false)

(* Recompiling a caller adds another copy to its existing cell. Refresh each
   equation once, otherwise later refreshes double all previous copies. *)
fun unique_rules rules =
  let
    fun keep (theorem,(seen,result)) =
      if HOLset.member(seen,concl theorem) then (seen,result)
      else (HOLset.add(seen,concl theorem),theorem::result)
  in rev(#2(List.foldl keep (HOLset.empty Term.compare,[]) rules)) end

(* Index syntax once. Repeated scans of every fixture's literal AST cost more
   than the checked stage evaluation; this index performs no proof reduction. *)
val rule_dependencies :
    (term,(string * string) HOLset.set) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Term.compare)
fun constant_key term =
  let val {Thy,Name,...} = dest_thy_const term in (Thy,Name) end
fun dependencies theorem =
  let val proposition = concl theorem in
    case Redblackmap.peek (!rule_dependencies,proposition) of
      SOME result => result
    | NONE => let
        val body = rhs(#2(strip_forall proposition)) handle HOL_ERR _ => T
        val result = HOLset.addList
          (HOLset.empty (pair_compare(String.compare,String.compare)),
           map constant_key (find_terms is_const body))
        val () = rule_dependencies :=
          Redblackmap.insert (!rule_dependencies,proposition,result)
      in result end
  end
val () = app (fn (_,entries) => app
  (fn clauses.RRules theorems => app (ignore o dependencies) theorems
    | clauses.Conversion _ => ()) entries)
  (computeLib.listItems(computeLib.the_compset()))

fun ensure_certificate_head head arity =
  if List.exists (same_const head) (!certificate_heads) then () else let
    fun cached tm =
      case List.find (fn th => aconv tm (lhs(concl th))) (!compiler_certificates) of
        SOME th => th
      | NONE => if List.exists (same_const head) (!planner_capture_heads)
          andalso null(free_vars tm) andalso capture_eligible head tm then let
            val inputs = Lib.with_flag (planner_capture_heads,[]) normalize_call tm
            val normalized = rhs(concl inputs)
          in case List.find (fn th => aconv normalized (lhs(concl th)))
                (!compiler_certificates) of
              SOME th => TRANS inputs th
            | NONE => raise PlannerBoundary normalized
          end else raise Conv.UNCHANGED
    val rules = unique_rules (List.concat (List.concat (map
      (fn (_,xs) => map (fn clauses.RRules ths => ths | clauses.Conversion _ => []) xs)
      (computeLib.listItems(computeLib.the_compset())))))
    fun headed th = same_const head
      (fst(strip_comb(lhs(#2(strip_forall(concl th))))))
      handle HOL_ERR _ => false
    val originals = List.filter headed rules
    val callers = List.filter (fn th => not(headed th) andalso
      HOLset.member(dependencies th,constant_key head)
      handle HOL_ERR _ => false) rules
    val () = computeLib.del_consts [head]
    val () = computeLib.add_convs [(head,arity,cached)]
    val () = computeLib.add_funs (rev originals @ callers)
    val () = certificate_heads := head :: !certificate_heads
  in () end

fun register_compile_eval certificate =
  let
    val (left,right) = dest_eq(concl certificate)
    val (head,args) = strip_comb left
    val (oracles,axioms) = Tag.dest_tag(tag certificate)
    val () = if is_const head andalso null(free_vars left) andalso
        null(hyp certificate) andalso null axioms andalso
        List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail "unsupported compiler evaluation certificate"
    val () = compiler_certificates := certificate :: !compiler_certificates
  in ensure_certificate_head head (length args) end

fun add_compile_eval certificate = register_compile_eval (normalize_compile_eval certificate)

(* Evaluate one named optional compiler stage inside an instrumented tactic.
   Its public SOME boundary is proved afterwards using the same certificate. *)
val pending_stage_values = ref ([] : (thm option * thm) list)
val stage_serial = ref 0

fun publish_stage_values () =
  (app (fn (named,evaluated) =>
      (stage_serial := !stage_serial + 1;
       (case named of SOME th =>
         (ignore(Theory.save_thm ("parity_stage_value_" ^ Int.toString(!stage_serial),th));
          computeLib.add_funs [th]) | NONE => ());
       ignore(Theory.save_thm ("parity_stage_call_" ^ Int.toString(!stage_serial),evaluated));
       register_compile_eval evaluated))
    (rev (!pending_stage_values));
   pending_stage_values := [])

fun restore_stage_values theory =
  let val facts = DB.thms theory
  in
    app (fn (name,th) => if String.isPrefix "parity_stage_value_" name then
      computeLib.add_funs [th] else ()) facts;
    app (fn (name,th) => if String.isPrefix "parity_stage_call_" name then
      register_compile_eval th else ()) facts
  end

fun cache_value definition goal =
  let
    val (evaluated,normalized) = evaluate_call (rhs(concl definition))
    val named = TRANS definition evaluated
    val () = pending_stage_values := (SOME named,normalized) :: !pending_stage_values
    val () = timed_evaluation (fst(strip_comb(lhs(concl normalized)))) "register"
      (fn () => register_compile_eval normalized)
    val named_normalized = normalize_compile_eval named
    val () = register_compile_eval named_normalized
    val () = pending_stage_values := (NONE,named_normalized) :: !pending_stage_values
  in Tactic.ACCEPT_TAC (TRANS evaluated (SYM named)) goal end

fun cache_stage definition goal =
  let
    val (_,body) = boolSyntax.dest_eq (Thm.concl definition)
    val call = rand body
    val (evaluated,normalized) = evaluate_call call
    val result = boolSyntax.rhs (Thm.concl evaluated)
    val (oracles,axioms) = Tag.dest_tag (Thm.tag evaluated)
    val name = #Name(dest_thy_const(boolSyntax.lhs(Thm.concl definition)))
    val () = if optionSyntax.is_some result andalso null(Thm.hyp evaluated) andalso
        null axioms andalso List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("incomplete compiler stage: " ^ name)
    val projected = AP_TERM (rator body) evaluated
    val value = Conv.CONV_RULE
      (Conv.RAND_CONV (Rewrite.PURE_REWRITE_CONV [optionTheory.THE_DEF])) projected
    val named = TRANS definition value
    val () = pending_stage_values := (SOME named,normalized) :: !pending_stage_values
    val boundary = TRANS evaluated (AP_TERM (rator result) (SYM named))
  in Tactic.ACCEPT_TAC boundary goal end

(* Name a checked optional result without recomputing its input projections.
   Matching uses the conservative definitions, before CBV expands arguments. *)
fun cache_named_results evaluated =
  app (fn name => (let
    val definition = SPEC_ALL (DB.fetch "evalCompilerBytecodeStages" (name ^ "_def"))
    val the_operator = rator(rhs(concl definition))
    val instance = Conv.REWR_CONV (SYM definition)
      (mk_comb(the_operator,lhs(concl evaluated)))
    val projected = AP_TERM the_operator evaluated
    val value = Conv.CONV_RULE (Conv.RAND_CONV
      (Rewrite.PURE_REWRITE_CONV [optionTheory.THE_DEF])) projected
    val named = TRANS (SYM instance) value
    val normalized = normalize_compile_eval named
    val () = register_compile_eval normalized
    val () = pending_stage_values := (SOME named,normalized) :: !pending_stage_values
  in () end handle HOL_ERR _ => ()))
  ["parity_policy", "parity_runtime_unit", "parity_pre0", "parity_pre1",
   "parity_runtime_pipeline", "parity_runtime_bytes", "parity_deploy_unit",
   "parity_deploy_pipeline", "parity_entry_plan", "parity_entry_successor_prefix",
   "parity_walk_result"]

(* Each conjunct is an actual optional stage, evaluated under its own tactic
   budget. The later bytecode theorem still proves the independent equality. *)
fun cache_some (goal as (_,proposition)) =
  let
    val call = rand proposition
    val head = fst(strip_comb call)
    val expanded =
      if is_const head andalso #Thy(dest_thy_const head) = "evalCompilerBytecodeStages" then
        Conv.REWR_CONV (DB.fetch "evalCompilerBytecodeStages"
          (#Name(dest_thy_const head) ^ "_def")) call
      else REFL call
    val (body_evaluated,body_normalized) = evaluate_call (rhs(concl expanded))
    val evaluated = TRANS expanded body_evaluated
    val result = rhs(concl evaluated)
    val () = if optionSyntax.is_some result then ()
      else raise Fail "compiler stage did not return SOME"
    val normalized = if aconv call (rhs(concl expanded)) then body_normalized
      else normalize_compile_eval evaluated
    val () = pending_stage_values := (NONE,normalized) :: !pending_stage_values
    val () = if aconv (lhs(concl normalized)) (lhs(concl body_normalized)) then ()
      else (pending_stage_values := (NONE,body_normalized) :: !pending_stage_values;
            register_compile_eval body_normalized)
    val () = timed_evaluation head "register" (fn () => register_compile_eval normalized)
    val () = cache_named_results body_evaluated
    val () = if is_const head andalso
        #Thy(dest_thy_const head) = "evalCompilerBytecodeStages" andalso
        #Name(dest_thy_const head) = "parity_pass_call" then let
      val relation = SPECL (#2(strip_comb call))
        (DB.fetch "evalCompilerBytecodeStages" "parity_pass_call_value")
      val projected = AP_TERM (rator(rhs(concl relation))) evaluated
      val named = TRANS relation
        (Conv.CONV_RULE (Conv.RAND_CONV
          (Rewrite.PURE_REWRITE_CONV [optionTheory.THE_DEF])) projected)
      val named_normalized = normalize_compile_eval named
      val () = register_compile_eval named_normalized
      val () = pending_stage_values :=
        (SOME named,named_normalized) :: !pending_stage_values
    in () end else ()
    val boundary = timed_evaluation head "boundary" (fn () => EQT_ELIM (TRANS (AP_TERM (rator proposition) evaluated)
      (Rewrite.PURE_REWRITE_CONV [optionTheory.IS_SOME_DEF]
        (mk_comb(rator proposition,result)))))
  in Tactic.ACCEPT_TAC boundary goal end

fun cache_checkpoint (goal as (_,proposition)) =
  if is_eq proposition then let
    val alias = rhs proposition
    val head = fst(strip_comb alias)
    val {Thy,Name,...} = dest_thy_const head
    val () = if Thy = "evalCompilerBytecodeStages" then ()
      else raise Fail "unexpected compiler projection"
    val definition = Conv.REWR_CONV (DB.fetch Thy (Name ^ "_def")) alias
  in cache_value definition goal end
  else cache_some goal

fun prepare_closed_call call goal =
  let
    val (_,normalized) = evaluate_call call
    val () = register_compile_eval normalized
    val () = pending_stage_values := (NONE,normalized) :: !pending_stage_values
  in Tactical.ALL_TAC goal end

fun prepare_function_analysis analysis (goal as (_,proposition)) =
  prepare_closed_call (mk_comb(analysis,List.last (#2(strip_comb(rand proposition))))) goal

(* Each preparation step certifies one instruction or completed block.
   Suspended calls remain data; only completed kernel equations enter the cache. *)
val planner_root = ref (NONE : term option)
val planner_pending = ref ([] : term list)

fun warm_some_step certificate_arities captures_for (goal as (_,proposition)) =
  let
    val root = rand proposition
    val () = if Option.isSome (!planner_root) andalso
        aconv (valOf(!planner_root)) root then ()
      else (planner_root := SOME root; planner_pending := [])
    val () = app (fn (head,arity) => ensure_certificate_head head arity)
      certificate_arities
    fun remember (evaluated,normalized) = let
      val () = if optionSyntax.is_some(rhs(concl evaluated)) then ()
        else raise Fail "planner stage did not return SOME"
      val () = register_compile_eval normalized
      val () = pending_stage_values := (NONE,normalized) :: !pending_stage_values
    in () end
    fun step () = let
      val is_root = null (!planner_pending)
      val current = if is_root then root else hd(!planner_pending)
      val head = fst(strip_comb current)
      val captures = captures_for head
      fun evaluate_current () = if is_root then evaluate_call current else let
        (* Boundary capture already normalized every argument. *)
        val evaluated = timed_evaluation head "pending"
          (fn () => computeLib.EVAL_CONV current)
      in (evaluated,evaluated) end
      val attempt =
        (PlannerComplete (Lib.with_flag (planner_capture_heads,captures) evaluate_current ())
         handle PlannerBoundary child => PlannerPending child)
    in case attempt of
      PlannerPending child => (planner_pending := child :: !planner_pending; step ())
    | PlannerComplete (result as (evaluated,_)) => let
        val () = remember result
      in if not is_root then
          (planner_pending := tl(!planner_pending); Tactical.ALL_TAC goal)
        else let
          val () = planner_pending := []
          val result_term = rhs(concl evaluated)
          val boundary = EQT_ELIM (TRANS (AP_TERM (rator proposition) evaluated)
            (Rewrite.PURE_REWRITE_CONV [optionTheory.IS_SOME_DEF]
              (mk_comb(rator proposition,result_term))))
        in Tactic.ACCEPT_TAC boundary goal end
      end
    end
  in step () end

fun warm_planner_step goal =
  warm_some_step [(planner_inst_head,10)]
    (fn head => if same_const head planner_block_head then [planner_inst_head]
      else if same_const head planner_inst_head then [] else [planner_block_head]) goal

(* A callee-first schedule threads the changed unit and supply into each
   function. Cache its actual pass calls before checking the full schedule. *)
val scheduled_function_head = prim_mk_const
  {Thy="venomFnScheduleRunner",Name="run_configured_fn_passes"}
val scheduled_pass_head = prim_mk_const
  {Thy="venomPassDispatcher",Name="execute_configured_fn_pass"}

fun warm_schedule_step goal =
  warm_some_step [(scheduled_function_head,6),(scheduled_fold_head,7),(scheduled_pass_head,5)]
    (fn head => if same_const head scheduled_function_head then [scheduled_fold_head]
      else if same_const head scheduled_fold_head then [scheduled_pass_head]
      else if same_const head scheduled_pass_head then [] else [scheduled_function_head]) goal

(* A singleton result is a reusable step of the original guarded fold. The
   three cases are exhaustive and avoid rewriting a singleton into itself. *)
fun configure_pass_stages () =
  let
    val definition = venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def
    val equations = map SPEC_ALL (CONJUNCTS (SPEC_ALL definition))
    val empty = hd equations
    val cons = List.nth(equations,1)
    val pass_list = List.nth(#2(strip_comb(lhs(concl cons))),2)
    val (_,tail) = listSyntax.dest_cons pass_list
    val empty_passes = listSyntax.mk_list([],listSyntax.dest_list_type(type_of tail))
    val single = SIMP_RULE pure_ss [empty] (INST [tail |-> empty_passes] cons)
    val fold = fst(strip_comb(lhs(concl empty)))
    val rules = unique_rules (List.concat (List.concat (map
      (fn (_,xs) => map (fn clauses.RRules ths => ths | clauses.Conversion _ => []) xs)
      (computeLib.listItems(computeLib.the_compset())))))
    val callers = List.filter (fn th => let
      val (left,right) = dest_eq (#2(strip_forall(concl th)))
    in not(same_const (fst(strip_comb left)) fold) andalso
       can (find_term (same_const fold)) right end
      handle HOL_ERR _ => false) rules
    val () = computeLib.del_consts [fold]
    val () = computeLib.add_funs
      [empty,single,venomFnScheduleEvalTheory.run_configured_fn_pass_fold_two]
    val () = computeLib.add_funs callers
  in () end

fun add_staged_compile_eval runtime_rewrites codegen_rewrites compile_rewrites
                            runtime_tm compile_tm =
  let
    fun evaluate rewrites tm =
      let val step = simpLib.SIMP_CONV pureSimps.pure_ss rewrites tm
      in TRANS step (computeLib.EVAL_CONV (boolSyntax.rhs (concl step))) end
    val runtime_step = simpLib.SIMP_CONV pureSimps.pure_ss
      runtime_rewrites runtime_tm
    val codegen_step = Rewrite.PURE_REWRITE_CONV codegen_rewrites
      (boolSyntax.rhs (concl runtime_step))
    val runtime_eval = TRANS runtime_step
      (TRANS codegen_step (computeLib.EVAL_CONV
        (boolSyntax.rhs (concl codegen_step))))
    val compile_eval = evaluate (runtime_eval :: compile_rewrites) compile_tm
  in
    add_compile_eval compile_eval
  end

end
