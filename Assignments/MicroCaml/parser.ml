open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) =
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) =
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* Part 2: Parsing expressions *)

let rec parse_expr toks = 
  let rec parse_lang toks curr_expr = 
    match lookahead toks with
    | Some Tok_Add -> let toks = match_token toks (Tok_Add) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Add, curr_expr, expr))
    | Some Tok_Sub -> let toks = match_token toks (Tok_Sub) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Sub, curr_expr, expr))
    | Some Tok_Mult -> let toks = match_token toks (Tok_Mult) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Mult, curr_expr, expr))
    | Some Tok_Div -> let toks = match_token toks (Tok_Div) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Div, curr_expr, expr))
    | Some (Tok_Int int_val) -> let toks = match_token toks (Tok_Int int_val) in let (toks, expr) = (parse_lang toks (Int int_val)) in (toks, FunctionCall (curr_expr, expr))
    | Some (Tok_ID var) -> let toks = match_token toks (Tok_ID var) in let (toks, expr) = (parse_lang toks (ID var)) in (toks, FunctionCall (curr_expr, expr))
    | Some (Tok_Bool bool_val) -> let toks = match_token toks (Tok_Bool bool_val) in let (toks, expr) = (parse_lang toks (Bool bool_val)) in (toks, FunctionCall (curr_expr, expr))
    | Some (Tok_String str_val) -> let toks = match_token toks (Tok_String str_val) in let (toks, expr) = (parse_lang toks (String str_val)) in (toks, FunctionCall (curr_expr, expr))
    | Some Tok_Equal -> let toks = match_token toks (Tok_Equal) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Equal, curr_expr, expr))
    | Some Tok_NotEqual -> let toks = match_token toks (Tok_NotEqual) in let (toks, expr) = parse_expr (toks) in (toks, Binop (NotEqual, curr_expr, expr))
    | Some Tok_Greater -> let toks = match_token toks (Tok_Greater) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Greater, curr_expr, expr))
    | Some Tok_GreaterEqual -> let toks = match_token toks (Tok_GreaterEqual) in let (toks, expr) = parse_expr (toks) in (toks, Binop (GreaterEqual, curr_expr, expr))
    | Some Tok_Less -> let toks = match_token toks (Tok_Less) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Less, curr_expr, expr))
    | Some Tok_LessEqual -> let toks = match_token toks (Tok_LessEqual) in let (toks, expr) = parse_expr (toks) in (toks, Binop (LessEqual, curr_expr, expr))
    | Some Tok_Concat -> let toks = match_token toks (Tok_Concat) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Concat, curr_expr, expr))
    | Some Tok_And -> let toks = match_token toks (Tok_And) in let (toks, expr) = parse_expr (toks) in (toks, Binop (And, curr_expr, expr))
    | Some Tok_Or -> let toks = match_token toks (Tok_Or) in let (toks, expr) = parse_expr (toks) in (toks, Binop (Or, curr_expr, expr))
    | Some Tok_In -> (toks, curr_expr) 
    | Some Tok_Then -> (toks, curr_expr) 
    | Some Tok_Else -> (toks, curr_expr) 
    | Some Tok_LParen -> let (toks, expr) = parse_expr (toks) in (toks, FunctionCall (curr_expr, expr))
    | None -> (toks, curr_expr) 
    | _ -> (*(print_string (string_of_token (List.hd toks)));*) raise (InvalidInputException "lang")
  in
  match lookahead toks with 
  | Some Tok_Int int_val -> 
    (* print_int (List.length toks); (print_string (" "^(string_of_token (List.nth toks ((List.length toks)-2) )))); print_string "\n"; *)
    let toks = match_token toks (Tok_Int int_val) in
    (parse_lang toks (Int int_val))
  | Some Tok_Bool bool_val -> 
    (* (match_token toks (Tok_Bool bool_val), (Bool bool_val)) *)
    let toks = match_token toks (Tok_Bool bool_val) in
    (parse_lang toks (Bool bool_val))
  | Some Tok_String str_val -> 
    (* (match_token toks (Tok_String str_val), (String str_val)) *)
    let toks = match_token toks (Tok_String str_val) in
    (parse_lang toks (String str_val))
  | Some Tok_ID var -> 
    (* (match_token toks (Tok_ID var), (ID var)) *)
    let toks = match_token toks (Tok_ID var) in
    (parse_lang toks (ID var))
  | Some Tok_LParen -> 
    let toks = match_token toks Tok_LParen in
    let rec find_rparen toks acc rparen_pos = 
      (match toks with
      | [] -> if (rparen_pos <> (-1)) then rparen_pos else raise (InvalidInputException "") (* missing right parenthes *)
      | h::t -> if h = Tok_RParen then (find_rparen t (acc+1) acc) else if ((h = Tok_LParen) && (rparen_pos <> (-1))) then rparen_pos else (find_rparen t (acc+1) rparen_pos)) in
    let furthest_rparen_pos = find_rparen toks 0 (-1) in
    (* print_int furthest_rparen_pos; print_string "\n"; *)
    let inner_toks_list = 
      let rec get_inner pos acc toks = 
        (match toks with
        | [] -> acc
        | h::t -> if pos = 0 then acc else (get_inner (pos-1) (acc@[h]) t)) in (get_inner furthest_rparen_pos [] toks)
    in
    let (_, inner_expr) = parse_expr inner_toks_list in
    (* print_int (List.length inner_toks_list); print_string "\n"; *)
    let toks = match_many toks inner_toks_list in
    let toks = match_token toks Tok_RParen in
    (* let (toks, expr) = parse_expr toks in *)
    let (toks, expr) = (parse_lang toks inner_expr) in
    (toks, expr)
  | Some Tok_RParen -> raise (InvalidInputException "expr")
  | Some Tok_Let ->
    (* match let keyword *)
    let toks = match_token toks Tok_Let in
    (* check if it is recursive *)
    let next = lookahead toks in 
    let toks = if (next = (Some Tok_Rec)) then (match_token toks Tok_Rec) else toks in
    (* match variable name *)
    let next_id_var = 
      match lookahead toks with
      | Some (Tok_ID var) -> var
      | _ -> raise (InvalidInputException "expr")
    in
    let toks = match_token toks (Tok_ID next_id_var) in
    (* match equal sign *)
    let toks = match_token toks Tok_Equal in
    (* shrinking expression after equal sign and before keyword in *)
    let (toks, expr1) = parse_expr toks in
    (* match keyword in *)
    let toks = match_token toks Tok_In in
    (* shrinking expression after keyword in before  *)
    let (toks, expr2) = parse_expr toks in
    (* return (token_list, expr) *)
    (toks, Let (next_id_var, (if (next = (Some Tok_Rec)) then true else false), expr1, expr2))
  | Some Tok_In -> raise (InvalidInputException "expr")
  | Some Tok_Fun ->
    (* match fun keyword *)
    let toks = match_token toks Tok_Fun in
    (* match function parameter *)
    let next_id_para = 
      match lookahead toks with
      | Some (Tok_ID var) -> var
      | _ -> raise (InvalidInputException "expr")
    in
    let toks = match_token toks (Tok_ID next_id_para) in
    (* match lambda *)
    let toks = match_token toks (Tok_Arrow) in
    (* shrink expression after lambda *)
    let (toks, expr) = parse_expr toks in
    (* return (token_list, expr) *)
    (toks, Fun (next_id_para, expr))
  | Some Tok_If -> 
    (* match if keyword *)
    let toks = match_token toks Tok_If in
    (* shrink and get condition expr *)
    let (toks, expr1) = parse_expr toks in
    (* match then keyword *)
    let toks = match_token toks Tok_Then in
    (* shrink and get then expr *)
    let (toks, expr2) = parse_expr toks in
    (* match else keyword *)
    let toks = match_token toks Tok_Else in
    (* shrink and get else expr *)
    let (toks, expr3) = parse_expr toks in
    (toks, If (expr1, expr2, expr3))
  | Some Tok_Then -> raise (InvalidInputException "expr")
  | Some Tok_Else -> raise (InvalidInputException "expr")
  | Some Tok_Not -> 
    (* match Not keyword *)
    let toks = match_token toks Tok_Not in
    let (toks, expr) = parse_expr toks in
    (toks, Not (expr))
  | _ -> (*print_int (List.length toks);*) raise (InvalidInputException "expr")

  (* raise (InvalidInputException "") *)
