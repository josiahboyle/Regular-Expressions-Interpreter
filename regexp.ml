(* CMSC 330 / Fall 2013 / Project 4 *)
(* Name: ?? *)
open Nfa

let get_next_gen () =
  let x = ref 0 in
  (fun () -> let r = !x in x := !x + 1; r)

let next = get_next_gen ()

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

let rec regexp_to_nfa_helper re s1 s2 = match re with
  Empty_String -> [(s1, None, s2)]
  | Char c -> [(s1, Some c, s2)]
  | Union (r1,r2) -> let t2 = next () in let t3 = next () in let t4 = next () in let t5 = next () in
                      (regexp_to_nfa_helper Empty_String s1 t2)@(regexp_to_nfa_helper Empty_String s1 t3)@(regexp_to_nfa_helper r1 t2 t4)@(regexp_to_nfa_helper r2 t3 t5)@(regexp_to_nfa_helper Empty_String t4 s2)@(regexp_to_nfa_helper Empty_String t5 s2)
  | Concat (r1,r2) -> let t2 = next () in
                      (regexp_to_nfa_helper r1 s1 t2)@(regexp_to_nfa_helper r2 t2 s2)
  | Star r1 ->        let t2 = next () in let t3 = next () in let t4 = next () in
                      (regexp_to_nfa_helper Empty_String s1 t2)@(regexp_to_nfa_helper Empty_String t2 t3)@(regexp_to_nfa_helper r1 t3 t4)@(regexp_to_nfa_helper Empty_String t4 s2)@(regexp_to_nfa_helper Empty_String s2 t2)@(regexp_to_nfa_helper Empty_String t2 s2)
;; 

let regexp_to_nfa re = match re with 
  Empty_String -> make_nfa 0 [0] [(0, None, 0)]
  | Char c -> make_nfa 0 [1] [(0, Some c, 1)] 
  | Union (r1,r2) ->  let t1 = next () in let t2 = next () in let t3 = next () in let t4 = next () in let t5 = next () in let t6 = next () in
                      make_nfa 0 [t6] ((regexp_to_nfa_helper Empty_String t1 t2)@(regexp_to_nfa_helper Empty_String t1 t3)@(regexp_to_nfa_helper r1 t2 t4)@(regexp_to_nfa_helper r2 t3 t5)@(regexp_to_nfa_helper Empty_String t4 t6)@(regexp_to_nfa_helper Empty_String t5 t6))
  | Concat (r1,r2) -> let t1 = next () in let t2 = next () in let t3 = next () in
                      make_nfa 0 [t3] ((regexp_to_nfa_helper r1 t1 t2)@(regexp_to_nfa_helper r2 t2 t3))
  | Star r1 ->        let t1 = next () in let t2 = next () in let t3 = next () in let t4 = next () in
                      make_nfa 0 [t4] ((regexp_to_nfa_helper Empty_String t1 t2)@(regexp_to_nfa_helper r1 t2 t3)@(regexp_to_nfa_helper Empty_String t3 t4)@(regexp_to_nfa_helper Empty_String t4 t1)@(regexp_to_nfa_helper Empty_String t1 t4))
;;

let rec regexp_to_string re = match re with 
    | Empty_String -> "E"
    | Char c -> let s1 = String.make 1 c in s1
    | Union (x,y) -> let s1 = regexp_to_string x in let s2 = regexp_to_string y in 
                     let s3 = String.concat "" ["(";s1;"|";s2;")"] in s3
    | Concat (x,y) -> let s1 = regexp_to_string x in let s2 = regexp_to_string y in 
                      let s3 = String.concat "" ["(";s1;s2;")"] in s3
    | Star (x) -> let s1 = regexp_to_string x in let s2 = String.concat "" ["(";s1;")*"] in s2

(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let tokenize str =
  let re_var = Str.regexp "[a-z]" in
  let re_epsilon = Str.regexp "E" in
  let re_union = Str.regexp "|" in
  let re_star = Str.regexp "*" in
  let re_lparen = Str.regexp "(" in
  let re_rparen = Str.regexp ")" in
  let rec tok pos s =
    if pos >= String.length s then
      [Tok_END]
    else begin
      if (Str.string_match re_var s pos) then
        let token = Str.matched_string s in
        (Tok_Char token.[0])::(tok (pos+1) s)
      else if (Str.string_match re_epsilon s pos) then
        Tok_Epsilon::(tok (pos+1) s)
      else if (Str.string_match re_union s pos) then
        Tok_Union::(tok (pos+1) s)
      else if (Str.string_match re_star s pos) then
        Tok_Star::(tok (pos+1) s)
      else if (Str.string_match re_lparen s pos) then
        Tok_LParen::(tok (pos+1) s)
      else if (Str.string_match re_rparen s pos) then
        Tok_RParen::(tok (pos+1) s)
      else
        raise (IllegalExpression("tokenize: " ^ s))
    end
  in
  tok 0 str

let tok_to_str t = ( match t with
      Tok_Char v -> (Char.escaped v)
    | Tok_Epsilon -> "E"
    | Tok_Union -> "|"
    | Tok_Star ->  "*"
    | Tok_LParen -> "("
    | Tok_RParen -> ")"
    | Tok_END -> "END"
  )

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) = 
  let lookahead tok_list = match tok_list with
      [] -> raise (IllegalExpression "lookahead")
    | (h::t) -> (h,t)
  in

  let rec parse_S l =
    let (a1,l1) = parse_A l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Union -> (
        let (a2,l2) = (parse_S n) in
        (Union (a1,a2),l2)
      )
    | _ -> (a1,l1)

  and parse_A l =
    let (a1,l1) = parse_B l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Char c ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_Epsilon ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_LParen ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | _ -> (a1,l1)

  and parse_B l =
    let (a1,l1) = parse_C l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Star -> (Star a1,n)
    | _ -> (a1,l1)

  and parse_C l =
    let (t,n) = lookahead l in
    match t with
      Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
      let (a1,l1) = parse_S n in
      let (t2,n2) = lookahead l1 in
      if (t2 = Tok_RParen) then
        (a1,n2)
      else
        raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let (rxp, toks) = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")

let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
