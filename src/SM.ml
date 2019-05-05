open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(*                                 *) | JMPDROP of string * int
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval :  -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((functionStack, stack, (state, configInput, configOutput) as stmtConfig) as cfg) program =
  match program with
  | [] -> (functionStack, stack, (state, configInput, configOutput))
  | prg::rest ->
(*        let _ = Printf.printf "%s\n" (GT.transform(insn) new @insn[show] () prg) in*)
        match prg with
        | LABEL _ -> eval env cfg rest
        | BINOP op -> eval env (match stack with
                       | y::x::tail -> (functionStack, Language.Value.of_int (Language.Expr.getFunction op (Language.Value.to_int x) (Language.Value.to_int y)) :: tail, (state, configInput, configOutput))
                       | _ -> failwith "Not enouth values on stack for BINOP"
                       ) rest
        | CONST n -> eval env (functionStack, [Language.Value.of_int n] @ stack, (state, configInput, configOutput)) rest
        | STRING s -> eval env (functionStack, (Language.Value.of_string (Bytes.of_string s))::stack, (state, configInput, configOutput)) rest
        | LD x -> eval env (functionStack, Language.State.eval state x :: stack, (state, configInput, configOutput)) rest
        | ST x -> eval env (match stack with
                  | head::tail -> (functionStack, tail, (Language.State.update x head state, configInput, configOutput))
                  | _ -> failwith "Not enouth values on stack for ST"
                  ) rest
        | STA (x, size) -> let (value::ids), tail = split (size + 1) stack in
                           eval env (functionStack, tail, (Language.Stmt.update state x value ids, configInput, configOutput)) rest
        | JMP l -> eval env cfg (env#labeled l)
        | CJMP (c, l) -> (match stack with
                          | head :: tails-> if (c = "z" && (Language.Value.to_int head) = 0) || (c = "nz" && (Language.Value.to_int head) != 0) then
                                               eval env (functionStack, tails, (state, configInput, configOutput)) (env#labeled l)
                                            else
                                               eval env (functionStack, tails, (state, configInput, configOutput)) rest
                          | _ -> failwith "Not enough values on stack for CJMP"
                         )
        | BEGIN (n, a, loc) -> let scope = State.enter state (a @ loc) in
                               let state', stack' = List.fold_left (fun (s, value::tail) name -> (State.update name value s, tail)) (scope, stack) (List.rev a) in
                               eval env (functionStack, stack', (state', configInput, configOutput)) rest
        | CALL (f, args_count, is_function) -> if env#is_label f then
                                eval env ((rest, state) :: functionStack, stack, (state, configInput, configOutput)) (env#labeled f)
                            else
                                eval env (env#builtin (functionStack, stack, (state, configInput, configOutput)) f args_count (not is_function)) rest
        | RET _
        | END -> (match functionStack with
                            | (rest, state') :: tail -> eval env (tail, stack, (State.leave state state', configInput, configOutput)) rest
                            | _ -> (functionStack, stack, (state, configInput, configOutput)))
        | JMPDROP (l, depth) -> let z::stack = stack in
                                if Value.to_int z = 0 then
                                   let (_, jmp_stack) = split depth stack in
                                   eval env (functionStack, jmp_stack, (state, configInput, configOutput)) (env#labeled l)
                                else
                                   eval env (functionStack, stack, (state, configInput, configOutput)) rest
        | ENTER args -> let values, stack = split (List.length args) stack in
                        let scope = List.fold_left (fun st (name, value) -> State.bind name value st) State.undefined (List.combine args values) in
                        let state = (State.push state scope args) in
                        eval env (functionStack, stack, (state, configInput, configOutput)) rest
        | LEAVE      -> eval env (functionStack, stack, (state, configInput, configOutput)) rest
        | DROP       -> eval env (functionStack, (List.tl stack), (state, configInput, configOutput)) rest
        | DUP  -> eval env (functionStack, (List.hd stack)::stack, (state, configInput, configOutput)) rest
        | TAG t -> let x::rest' = stack in
                   let res = match x with
                     | Value.Sexp (t', _) -> if (t = t') then 1 else 0
                     | _ -> 0 in
                   eval env (functionStack, (Value.of_int res)::rest', (state, configInput, configOutput)) rest
        | SWAP -> let x::y::rest' = stack in
                eval env (functionStack, y::x::rest', (state, configInput, configOutput)) rest
        | SEXP (tag, count) -> let values, rest' = split count stack in
                               let new_stack = (Value.sexp tag @@ (List.rev values))::rest' in
                               eval env (functionStack, new_stack, (state, configInput, configOutput)) rest
        | it -> failwith "this comand"

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
(*           let _ = Printf.printf "n: %d\nstack:" n in*)
(*           let _ = List.iter (fun it -> Printf.printf "%s " (Value.show it)) stack in*)
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label =
  object(self)
    val mutable labelCount = 0

    method getLabel = labelCount <- labelCount + 1; ".L" ^ string_of_int labelCount
  end

  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Array exprs      -> let compiledExprs = List.flatten (List.map (expr)  exprs) in
                             compiledExprs @ [CALL (".array", (List.length compiledExprs), true)]
  | Expr.String s         -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Elem (arr, idx)  -> expr arr @ expr idx @ [CALL (".elem", 2, true)]
  | Expr.Length arr       -> expr arr @ [CALL (".length", 1, true)]
  | Expr.Call (f, args) -> let cArgs = List.flatten (List.map expr args) in
                           cArgs @ [CALL (f, List.length args, true)]
  | Expr.Sexp (name, exprs) -> let compiledExprs = List.flatten (List.map expr exprs) in
                               compiledExprs @ [SEXP (name, List.length exprs)]

let make_bindings pattern =
  let rec inner p = match p with
                    | Stmt.Pattern.Wildcard -> []
                    | Stmt.Pattern.Ident var -> [[]]
                    | Stmt.Pattern.Sexp (_, exprs) ->
                        let next i x = List.map (fun arr -> i::arr) (inner x) in
                        List.flatten (List.mapi next exprs) in
                    let elem i = [CONST i; CALL (".elem", 2, true)] in
                    let extract_bind_value path = [DUP] @ (List.flatten (List.map elem path)) @ [SWAP] in
                    let result = List.flatten (List.map extract_bind_value (List.rev (inner pattern))) in
                    result

let rec compile_pattern pattern end_label depth = match pattern with
  | Stmt.Pattern.Wildcard
  | Stmt.Pattern.Ident _ -> [DROP], false
  | Stmt.Pattern.Sexp (name, exprs) -> let compile_subpattern i pattern =
                                        let inner = match pattern with
                                                    | Stmt.Pattern.Sexp (_, ps) -> if (List.length ps) > 0 then
                                                                                        [DUP] @ fst (compile_pattern pattern end_label (depth + 1)) @ [DROP]
                                                                                   else
                                                                                        fst (compile_pattern pattern end_label depth)
                                                    | _ -> fst (compile_pattern pattern end_label depth)
                                        in [DUP; CONST i; CALL (".elem", 2, true)] @ inner in
                                       let prg = List.flatten (List.mapi compile_subpattern exprs) in
                                       [TAG name; JMPDROP (end_label, depth)] @ prg, true

     let rec compileBlock stmt outLabel = match stmt with
          | Stmt.Seq (s1, s2) -> let l_end1 = label#getLabel in
                                 let code, used1 = compileBlock s1 l_end1 in
                                 let code', used2 = compileBlock s2 outLabel in
                                 code @ (if used1 then [LABEL l_end1] else []) @ code', used2
          | Stmt.Assign (x, idx, e) -> (match idx with
                                        | [] -> expr e @ [ST x], false
                                        | idx -> let compiledIdx = List.fold_left (fun comp e -> comp @ (expr e)) [] (List.rev idx) in
                                                 compiledIdx @ expr e @ [STA (x, List.length idx)], false
                                        )
          | Stmt.If (c, t, e)  -> let else_label = label#getLabel in
                                  let then_block, used_then = compileBlock t outLabel in
                                  let else_block, used_else = compileBlock e outLabel in
                                  expr c @ [CJMP ("z", else_label)] @ then_block @ [JMP outLabel; LABEL else_label] @ else_block @ [JMP outLabel], true
          | Stmt.Skip          -> [], false
          | Stmt.While (c, b)  -> let bodyLabel  = label#getLabel in
                                  let condLabel  = label#getLabel in
                                  let body, _ = compileBlock b condLabel in
                                  [JMP condLabel; LABEL bodyLabel] @ body @ [LABEL condLabel] @ expr c @ [CJMP ("nz", bodyLabel)], false
          | Stmt.Repeat (b, c) -> let bodyLabel  = label#getLabel in
                                  let end_label = label#getLabel in
                                  let body, used  = compileBlock b end_label in
                                  [LABEL bodyLabel] @ body @ [LABEL end_label] @ expr c @ [CJMP ("z", bodyLabel)], false
          | Stmt.Call (f, a) ->  List.flatten (List.map expr a) @ [CALL (f, List.length a, false)], false
          | Stmt.Return e    -> (match e with
                                  | Some v -> (expr v) @ [RET true], false
                                  | _ ->  [RET false], false
                                )
          | Stmt.Leave -> [LEAVE], false
          | Stmt.Case (e, brs) -> let compile_simple_branch pattern stmt next_label end_label =
                                      let patterg_prg, n_used = compile_pattern pattern next_label 0 in
                                      let stmt_prg, s_used = compileBlock (Stmt.Seq (stmt, Stmt.Leave)) end_label in
                                      patterg_prg @ make_bindings pattern @ [DROP; ENTER (List.rev (Stmt.Pattern.vars pattern))] @ stmt_prg, n_used, s_used in
                                  (match brs with
                                    | [pattern, stmt] ->
                                        let br_prg, p_used, s_used = compile_simple_branch pattern stmt outLabel outLabel in
                                        let result = expr e @ [DUP] @ br_prg in
(*                                        let _ = List.iter (fun i -> Printf.printf "%s " (GT.transform(insn) new @insn[show] () i)) result in*)
(*                                        let _ = Printf.printf "\n\n" in*)
                                        result, p_used || s_used
                                    | brs -> let n = List.length brs - 1 in
                                             let compile_branch_fold (prev_label, i, prg) (pattern, stmt) =
                                                let next_label = if i != n then label#getLabel else outLabel in
                                                let label_prg = match prev_label with Some x -> [LABEL x; DUP] | _ -> [] in
                                                let br_prg, _, _ = compile_simple_branch pattern stmt next_label outLabel in
                                                let cur_prg = label_prg @ br_prg @ (if i!=n then [JMP outLabel] else []) in
                                                Some next_label, i + 1, cur_prg :: prg in
                                             let _, _, prg = List.fold_left compile_branch_fold (None, 0, []) brs in
                                             let result = expr e @ [DUP] @ List.flatten @@ List.rev prg in
(*                                             let _ = List.iter (fun i -> Printf.printf "%s " (GT.transform(insn) new @insn[show] () i)) result in*)
(*                                             let _ = Printf.printf "\n\n" in*)
                                             result, true
          )

let compileStmt stmt =
    let end_label = label#getLabel in
    let prg, used = compileBlock stmt end_label in
    prg @ [LABEL end_label]

let rec compileDefs defs = List.fold_left (fun prev (name, (args, locals, body)) ->
                                           let compiledBody = compileStmt body in
                                           prev @ [LABEL name] @ [BEGIN (name, args, locals)] @ compiledBody @ [END]
                                           ) [] defs

 let rec compile (defs, main) =
    let compiledMain = compileStmt main in
    let compiledDefs = compileDefs defs in
(*    let _ = List.iter (fun i -> Printf.printf "%s " (GT.transform(insn) new @insn[show] () i)) (compiledMain @ [END] @ compiledDefs) in*)
    compiledMain @ [END] @ compiledDefs
