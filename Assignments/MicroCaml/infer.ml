open MicroCamlTypes

(* Part 3: Type Inference *)

(*******************************************************************|
|**********************   Environment   ****************************|
|*******************************************************************|
| - The environment is a map that holds type information of         |
|   variables                                                       |
|*******************************************************************)
type environment = (var * typeScheme) list

exception OccursCheckException

exception UndefinedVar

type substitutions = (string * typeScheme) list

let type_variable = ref (Char.code 'a')

(* generates a new unknown type placeholder.
   returns T(string) of the generated alphabet *)
let gen_new_type () =
  let c1 = !type_variable in
  incr type_variable; T(Char.escaped (Char.chr c1))
;;

let string_of_constraints (constraints: (typeScheme * typeScheme) list) =
  List.fold_left (fun acc (l, r) -> Printf.sprintf "%s%s = %s\n" acc (string_of_type l) (string_of_type r)) "" constraints

let string_of_subs (subs: substitutions) =
  List.fold_left (fun acc (s, t) -> Printf.sprintf "%s%s: %s\n" acc s (string_of_type t)) "" subs





(*********************************************************************|
|******************   Annotate Expressions   *************************|
|*********************************************************************|
| Arguments:                                                          |
|   env -> A typing environment                                       |
|   e -> An expression that has to be annotated                       |
|*********************************************************************|
| Returns:                                                            |
|   returns an annotated expression of type aexpr that holds          |
|   type information for the given expression e.                      |
|   and the type of e                                                 |
|   and a list of typing constraints.                                 |
|*********************************************************************|
| - This method takes every expression/sub-expression in the          |
|   program and assigns some type information to it.                  |
| - This type information maybe something concrete like a TNum        |
|   or it could be a unique parameterized type(placeholder) such      |
|   as 'a.                                                            |
| - Concrete types are usually assigned when you encounter            |
|   simple literals like 10, true and "hello"                         |
| - Whereas, a random type placeholder is assigned when no            |
|   explicit information is available.                                |
| - The algorithm not only infers types of variables and              |
|   functions defined by user but also of every expression and        |
|   sub-expression since most of the inference happens from           |
|   analyzing these expressions only.                                 |
| - A constraint is a tuple of two typeSchemes. A strict equality     |
|   is being imposed on the two types.                                |
| - Constraints are generated from the expresssion being analyzed,    |
|   for e.g. for the expression ABinop(x, Add, y, t) we can constrain |
|   the types of x, y, and t to be TNum.                              |
| - In short, most of the type checking rules will be added here in   |
|   the form of constraints.                                          |
| - Further, if an expression contains sub-expressions, then          |
|   constraints need to be obtained recursively from the              |
|   subexpressions as well.                                           |
| - Lastly, constraints obtained from sub-expressions should be to    |
|   the left of the constraints obtained from the current expression  |
|   since constraints obtained from current expression holds more     |
|   information than constraints from subexpressions and also later   |
|   on we will be working with these constraints from right to left.  |
|*********************************************************************)
let rec gen (env: environment) (e: expr): aexpr * typeScheme * (typeScheme * typeScheme) list =
  let rec check_env var env = 
    match env with
    | [] -> raise UndefinedVar
    | ((var_name:string), (var_type:typeScheme))::t -> if var_name = var then var_type else (check_env var t) in
  match e with
  | Int int_val -> (AInt(int_val, TNum), TNum, [])
  | Bool bool_val -> (ABool(bool_val, TBool), TBool, [])
  | String str_val -> (AString(str_val, TStr), TStr, [])
  | ID var -> let var_type = (check_env var env) in (AID(var, var_type), var_type, [])
  | Fun (var, expr) -> 
    let input_type = gen_new_type () in 
    let output_type = gen_new_type () in 
    let _env = ((var, input_type)::env) in
    let (anno_expr, anno_expr_type, type_constraint_list) = (gen _env expr) in
    let type_constraint_list = type_constraint_list@[(anno_expr_type, output_type)] in
    (AFun (var, anno_expr, TFun(input_type, anno_expr_type)), TFun(input_type, anno_expr_type), type_constraint_list)
  | Not (expr)-> 
    let (anno_expr, anno_expr_type, type_constraint_list) = (gen env expr) in
    let anno_expr_type = (if anno_expr_type = TBool then TBool else failwith "Type Mismatch") in
    let type_constraint_list = type_constraint_list@[(anno_expr_type, TBool)] in
    (ANot (anno_expr, anno_expr_type), anno_expr_type, type_constraint_list)
  | Binop (op, expr1, expr2)-> 
    let (anno_expr1, anno_expr_type1, type_constraint_list1) = (gen env expr1) in
    let (anno_expr2, anno_expr_type2, type_constraint_list2) = (gen env expr2) in
    let output_type = 
        match op with
        | Concat -> TStr
        | Or -> TBool
        | And -> TBool
        | Add -> TNum
        | Sub -> TNum
        | Mult -> TNum
        | Div -> TNum
        | _ -> TBool in
    let constraint_type = 
      (match op with
      | Concat -> [(anno_expr_type1, TStr);(anno_expr_type2, TStr)]
      | Or -> [(anno_expr_type1, TBool);(anno_expr_type2, TBool)]
      | And -> [(anno_expr_type1, TBool);(anno_expr_type2, TBool)]
      | Add -> [(anno_expr_type1, TNum);(anno_expr_type2, TNum)]
      | Sub -> [(anno_expr_type1, TNum);(anno_expr_type2, TNum)]
      | Mult -> [(anno_expr_type1, TNum);(anno_expr_type2, TNum)]
      | Div -> [(anno_expr_type1, TNum);(anno_expr_type2, TNum)]
      | _ -> [(anno_expr_type1, anno_expr_type2)]) (*("<", ">", "=", "<=", ">=")*) in
    let type_constraint_list = type_constraint_list1@type_constraint_list2@constraint_type in
    (ABinop (op, anno_expr1, anno_expr2, output_type), output_type, type_constraint_list)
  | If (expr1, expr2, expr3) -> 
    let (anno_expr1, anno_expr_type1, type_constraint_list1) = (gen env expr1) in
    let (anno_expr2, anno_expr_type2, type_constraint_list2) = (gen env expr2) in
    let (anno_expr3, anno_expr_type3, type_constraint_list3) = (gen env expr3) in
    let type_constraint_list = 
      if anno_expr_type1 = TBool && anno_expr_type2 = anno_expr_type3 then
        type_constraint_list1@type_constraint_list2@type_constraint_list3@[(anno_expr_type1, TBool);(anno_expr_type2, anno_expr_type3)]
      else
        failwith "Type Mismatch" in
    (AIf (anno_expr1, anno_expr2, anno_expr3, anno_expr_type2), anno_expr_type2, type_constraint_list)
  | FunctionCall (expr1, expr2) -> 
    let (anno_expr1, anno_expr_type1, type_constraint_list1) = (gen env expr1) in
    let (anno_expr2, anno_expr_type2, type_constraint_list2) = (gen env expr2) in
    let output_type = gen_new_type () in
    let type_constraint_list = type_constraint_list1@type_constraint_list2@[(anno_expr_type1, (TFun(anno_expr_type2, output_type)))] in
    (AFunctionCall (anno_expr1, anno_expr2, output_type), output_type, type_constraint_list)
  | Let (var, rec_bool, expr1, expr2) -> 
    let fun_type = gen_new_type () in
    let _env = ((var, fun_type)::env) in
    let (anno_expr1, anno_expr_type1, type_constraint_list1) = (gen _env expr1) in
    let (anno_expr2, anno_expr_type2, type_constraint_list2) = (gen _env expr2) in
    let type_constraint_list = type_constraint_list1@[(fun_type, anno_expr_type1)]@type_constraint_list2 in
    (ALet (var, rec_bool, anno_expr1, anno_expr2, anno_expr_type2), anno_expr_type2, type_constraint_list)
    
  (* raise UndefinedVar *)


(******************************************************************|
|**********************   Unification   ***************************|
|**********************    Algorithm    ***************************|
|******************************************************************)


(******************************************************************|
|**********************   Substitute   ****************************|
|******************************************************************|
|Arguments:                                                        |
|   t -> type in which substitutions have to be made.              |
|   (x, u) -> (type placeholder, resolved substitution)            |
|******************************************************************|
|Returns:                                                          |
|   returns a valid substitution for t if present, else t as it is.|
|******************************************************************|
|- In this method we are given a substitution rule that asks us to |
|  replace all occurrences of type placeholder x with u, in t.     |
|- We are required to apply this substitution to t recursively, so |
|  if t is a composite type that contains multiple occurrences of  |
|  x then at every position of x, a u is to be substituted.        |
*******************************************************************)
let rec substitute (u: typeScheme) (x: string) (t: typeScheme) : typeScheme =
  match t with
  | TNum | TBool | TStr -> t
  | T(c) -> if c = x then u else t
  | TFun(t1, t2) -> TFun(substitute u x t1, substitute u x t2)
;;

(******************************************************************|
|*************************    Apply    ****************************|
|******************************************************************|
| Arguments:                                                       |
|   subs -> list of substitution rules.                            |
|   t -> type in which substitutions have to be made.              |
|******************************************************************|
| Returns:                                                         |
|   returns t after all the substitutions have been made in it     |
|   given by all the substitution rules in subs.                   |
|******************************************************************|
| - Works from right to left                                       |
| - Effectively what this function does is that it uses            |
|   substitution rules generated from the unification algorithm and|
|   applies it to t. Internally it calls the substitute function   |
|   which does the actual substitution and returns the resultant   |
|   type after substitutions.                                      |
| - Substitution rules: (type placeholder, typeScheme), where we   |
|   have to replace each occurrence of the type placeholder with   |
|   the given type t.                                              |
|******************************************************************)
let apply (subs: substitutions) (t: typeScheme) : typeScheme =
  List.fold_right (fun (x, u) t -> substitute u x t) subs t
;;


(******************************************************************|
|***************************   Unify   ****************************|
|******************************************************************|
| Arguments:                                                       |
|   constraints -> list of constraints (tuple of 2 types)          |
|******************************************************************|
| Returns:                                                         |
|   returns a list of substitutions                                |
|******************************************************************|
| - The unify function takes a bunch of constraints it obtained    |
|   from the collect method and turns them into substitutions.     |
| - It is crucial to remember that these constraints are dependent |
|   on each other, therefore we have separate function unify_one   |
|   and unify.                                                     |
| - Since constraints on the right have more precedence we start   |
|   from the rightmost constraint and unify it by calling the      |
|   unify_one function. unify_one transforms the constraint to a   |
|   substitution. More details given below.                        |
| - Now these substitutions will be applied to both types of the   |
|   second rightmost constraint following which they will be       |
|   unified by again calling the unify_one function.               |
| - This process of unification(unify_one) and substitution(apply) |
|   goes on till all the constraints have been accounted for.      |
| - In the end we get a complete list of substitutions that helps  |
|   resolve types of all expressions in our program.               |
|******************************************************************)
let rec unify (constraints: (typeScheme * typeScheme) list) : substitutions =
  match constraints with
  | [] -> []
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let t2 = unify xs in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let t1 = unify_one (apply t2 x) (apply t2 y) in
    (* t1 @ t2 *)
    let sub = t1 @ t2 in
    (* unify all *)
    let rec match_all sub sub_sub =
      match sub with 
      | [] -> sub_sub
      | one_sub::t -> match_all t (List.map (fun (x,y) -> (x, (apply [one_sub] y))) sub_sub) in
    (* (match_all sub sub) *)
    let all_substitutions = match_all sub sub in
    (* check for occur *)
    let check_occur = 
      (List.map (fun (var, typeS) ->
       let rec check_conflict var typeS sub = 
        match sub with
        | TFun(typeS1, typeS2) -> 
          let (_,first_typeS) =  
            if typeS1 = T(var) then 
              raise OccursCheckException 
            else 
              (check_conflict var typeS1 typeS1) in
          let (_,second_typeS) = 
            if typeS2 = T(var) then 
              raise OccursCheckException 
            else
              (check_conflict var typeS2 typeS2) in
          (var, TFun(first_typeS, second_typeS))
        | _ -> (var, typeS)
       in check_conflict var typeS typeS ) all_substitutions)
    in check_occur
    (* List.map (fun (x,y) -> (x,(apply sub y)) ) sub  *)

(******************************************************************|
|*************************   Unify One  ***************************|
|******************************************************************|
| Arguments:                                                       |
|   t1, t2 -> two types (one pair) that need to be unified.        |
|******************************************************************|
| Returns:                                                         |
|   returns a substitution rule for the two types if one of them   |
|   is a parameterized type else nothing.                          |
|******************************************************************|
| - A constraint is converted to a substitution here.              |
| - As mentioned several times before a substitution is nothing    |
|   but a resolution rule for a type placeholder.                  |
| - If a constraint yields multiple type resolutions then the      |
|   resolutions should be broken up into a list of constraints and |
|   be passed to the unify function.                               |
| - If both types are concrete then we need not create a new       |
|   substitution rule.                                             |
| - If the types are concrete but don't match then that indicates  |
|   a type mismatch.                                               |
|******************************************************************)
and unify_one (t1: typeScheme) (t2: typeScheme) : substitutions =
  match t1, t2 with
  | TNum, TNum | TBool, TBool | TStr, TStr -> []
  | T(x), z | z, T(x) -> [(x, z)]
    (* let rec check_conflict var typeS inferred_typeS =
    match inferred_typeS with
    | TFun(a, b) -> 
      let first = if a = T(var) then raise OccursCheckException else (check_conflict var typeS a) in 
      let second = if b = T(var) then raise OccursCheckException else (check_conflict var typeS b) in 
      typeS
    | T(y) -> if (x = y) then raise OccursCheckException else typeS
    | _ -> typeS
    in [(x, (check_conflict x z z))] *)
  | TFun(a, b), TFun(x, y) -> unify [(a, x); (b, y)]
    (* let rec check_conflict z sub comp =
        match sub with
        | TFun(a, b) -> if a = comp then raise OccursCheckException else (check_conflict z b comp)
        | T(y) -> if (comp = T(y)) then raise UndefinedVar else z
        | _ -> z in 
      unify [((check_conflict a a x), (check_conflict x x a)); ((check_conflict b b y), (check_conflict y y b))] *)
  | _ -> raise (failwith "mismatched types")
;;

(* applies a final set of substitutions on the annotated expr *)
let rec apply_expr (subs: substitutions) (ae: aexpr): aexpr =
  match ae with
  | ABool(b, t) -> ABool(b, apply subs t)
  | AInt(n, t) -> AInt(n, apply subs t)
  | AString(s, t) -> AString(s, apply subs t)
  | AID(s, t) -> AID(s, apply subs t)
  | AFun(id, e, t) -> AFun(id, apply_expr subs e, apply subs t)
  | ANot(e, t) -> ANot(apply_expr subs e, apply subs t)
  | ABinop(op, e1, e2, t) -> ABinop(op, apply_expr subs e1, apply_expr subs e2, apply subs t)
  | AIf(e1, e2, e3, t) -> AIf(apply_expr subs e1, apply_expr subs e2, apply_expr subs e3, apply subs t)
  | AFunctionCall(fn, arg, t) -> AFunctionCall(apply_expr subs fn, apply_expr subs arg, apply subs t)
  | ALet(id, b, e1, e2, t) -> ALet(id, b, apply_expr subs e1, apply_expr subs e2, apply subs t)
;;

(******************************************************************|
|**********************   Main Interface  *************************|
|******************************************************************)

(* 1. annotate expression with placeholder types and generate constraints
   2. unify types based on constraints *)
let infer (e: expr) : typeScheme =
  let env = [] in
  let ae, t, constraints = gen env e in
  (*let _ = print_string "\n"; print_string (string_of_constraints constraints) in
  let _ = print_string "\n"; print_string (string_of_aexpr ae) in *)
  let subs = unify constraints in
  (* let _ = print_string "\n"; print_string (string_of_subs subs) in *)
  (* reset the type counter after completing inference *)
  type_variable := (Char.code 'a');
  (* apply_expr subs annotated_expr *)
  apply subs t
;;
