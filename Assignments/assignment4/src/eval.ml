open Ast

exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Print env to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Print env to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)

(* evaluate an arithmetic expression in an environment *)
let rec eval_expr (e : exp) (env : environment) : value =
  let rec find_var_in_env var_str env = 
    match env with
    [] -> raise (UndefinedVar)
    | ((var_name, value)::t) -> 
      if var_name = var_str then
        match value with
        Int_Val v -> Int_Val v
        | Bool_Val v -> Bool_Val v
        | Closure (env, inner_var_str, exp) -> Closure (env, inner_var_str, exp) 
      else
        (find_var_in_env var_str t) in
  match e with
  | Var x -> (find_var_in_env x env)
  | True -> Bool_Val true
  | False -> Bool_Val false
  | Number num -> Int_Val num
  | Plus (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> (Int_Val (v1 + v2))
    | (_,_) -> (raise TypeError))
  | Minus (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> (Int_Val (v1 - v2))
    | (_,_) -> (raise TypeError))
  | Times (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> Int_Val (v1 * v2)
    | (_,_) -> (raise TypeError))
  | Div (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> 
      if v2 = 0 then
        (raise (DivByZeroError))
      else
        Int_Val (v1 / v2)
    | (_,_) -> (raise TypeError))
  | Mod (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> 
      if v2 = 0 then
        (raise (DivByZeroError))
      else
        Int_Val ((mod) (v1) (v2))
    | (_,_) -> (raise TypeError))
  | Or (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Bool_Val v1, Bool_Val v2) ->
      if (v1 = true || v2 = true) then
        Bool_Val true
      else
        Bool_Val false
    | (_,_) -> (raise TypeError))
  | And (exp1, exp2) -> 
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Bool_Val v1, Bool_Val v2) ->
      if (v1 = true && v2 = true) then
        Bool_Val true
      else
        Bool_Val false
    | (_,_) -> (raise TypeError);)
  | Not (exp) ->
    let result = (eval_expr exp env) in
    (match result with
    | Bool_Val v -> 
      (match v with
      | true -> Bool_Val false
      | false -> Bool_Val true)
    | Int_Val v -> (raise TypeError)
    | Closure (_,_,_) -> (raise TypeError))
  | Lt (exp1, exp2) ->
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> 
      if v1 < v2 then
        Bool_Val true
      else
        Bool_Val false
    | (_,_) -> (raise TypeError))
  | Leq (exp1, exp2) ->
      let result1 = (eval_expr exp1 env) in
      let result2 = (eval_expr exp2 env) in
      (match (result1, result2) with
      | (Int_Val v1, Int_Val v2) -> 
        if v1 <= v2 then
          Bool_Val true
        else
          Bool_Val false
      | (_,_) -> (raise TypeError))
  | Eq (exp1, exp2) ->
    let result1 = (eval_expr exp1 env) in
    let result2 = (eval_expr exp2 env) in
    (match (result1, result2) with
    | (Int_Val v1, Int_Val v2) -> 
      if v1 = v2 then
        Bool_Val true
      else
        Bool_Val false
    | (Bool_Val v1, Bool_Val v2) -> 
      if v1 = v2 then
        Bool_Val true
      else
        Bool_Val false
    | (_,_) -> (raise TypeError))
  | App (exp1, exp2) -> 
    let arg_value = (eval_expr exp2 env) in
    let func = (eval_expr exp1 env) in
    (match func with
    | Closure (env, arg, exp) -> eval_expr exp ((arg, arg_value)::env)
    | (_) -> raise TypeError)
  | Fun (arg, exp) ->
    Closure (env, arg, exp)

(* let x = (eval_expr (Plus (Number 1, Var "p")) [("x", Int_Val(1)); ("p", Bool_Val(false))]) *)
(* let x = (eval_expr (And (Var "q", Lt (True, Var "y"))) [("x", Int_Val(1)); ("p", Bool_Val(false)); ("y", Int_Val(6)); ("q", Bool_Val(true))]) *)
(* let x = (eval_expr (Div (Var "x", Number 0)) [("x", Int_Val(1)); ("p", Bool_Val(false)); ("y", Int_Val(6)); ("q", Bool_Val(true))]) *)
(* let x = (eval_expr (Mod (Var "x", Var "y")) [("x", Int_Val(1)); ("p", Bool_Val(false))]) *)
(* let x = (eval_expr (App (Fun ("z", Minus (Var "z", Number 2)), App (Fun ("x", Plus (Var "x", Number 1)), Number 2))) []);;
(print_val x);; *)


(* evaluate a command in an environment *)
let rec eval_command (c : com) (env : environment) : environment =
  let rec update_env given_var_name given_value env acc (updated:bool)= 
    match env with
    | [] -> 
      if updated = true then
        acc
      else
        raise (UndefinedVar)
    | ((var_name, value)::t) -> 
      if var_name = given_var_name && updated = false then
        (match (value, given_value) with
        | (Int_Val v1, Int_Val v2) -> (update_env (given_var_name) (given_value) (t) (acc@[(var_name, Int_Val v2)]) (true))
        | (Bool_Val v1, Bool_Val v2) -> (update_env (given_var_name) (given_value) (t) (acc@[(var_name, Bool_Val v2)]) (true))
        | (Closure (env1, arg1, exp1), Closure (env2, arg2, exp2)) -> (update_env (given_var_name) (given_value) (t) (acc@[(var_name, Closure (env2, arg2, exp2))]) (true))
        | (_,_) -> raise TypeError)
      else
        (update_env (given_var_name) (given_value) (t) (acc@[(var_name, value)]) (updated)) in
  match c with
  | Skip -> env
  | Comp (com1, com2) -> 
    (eval_command com2 (eval_command com1 env)) 
  | Declare (data_type, var_name) -> 
    (match data_type with
    | Int_Type -> (var_name, Int_Val 0)::env
    | Bool_Type -> (var_name, Bool_Val false)::env
    | Lambda_Type -> (var_name, Closure (env, "x", Var "x"))::env)
  | Assg (var_name, exp) ->
    let value = (eval_expr exp env) in
    let new_env = (update_env (var_name) (value) (env) ([]) (false)) in new_env
  | Cond (exp, com_if, com_else) ->
    let condition = (eval_expr exp env) in
    (match condition with
    | Bool_Val v -> 
      (match v with
      | true -> (eval_command com_if env)
      | false -> (eval_command com_else env))
    | (_) -> raise TypeError)
  | While (exp, com) -> 
    let condition = (eval_expr exp env) in
    (match condition with
    | Bool_Val v -> 
      (match v with
      | true -> (eval_command c (eval_command com env))
      | false -> (env))
    | (_) -> raise TypeError)
  | For (exp, com) ->
    let count = (eval_expr exp env) in 
    (match count with
    | Int_Val v ->
      if v < 1 then
        env
      else
        (eval_command (For((Number (v-1)), com)) (eval_command com env))
    | (_) -> raise TypeError)

